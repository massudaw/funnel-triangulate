{-# LANGUAGE TupleSections #-}
module Triangulation where

import Data.Ord
import System.IO.Unsafe
import qualified Triangle.FFI as Tri
import Search
import System.Random
import GareysTriangulation
import Control.Applicative
import DXF
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Monoid
import Language.Mecha
import Language.Mecha.Solid
import Data.Tuple
import Data.Maybe

import qualified Data.List as L
import Linear.V2
import Linear.V3
import Linear.Vector
import Polygon
import Point2
import Triangle
import qualified Data.Map as M

import qualified Data.Array as A
import Data.Graph
import Debug.Trace
import qualified Data.Foldable as F
import Numeric

data PolygonSet ix a
  = PolygonSet
  { nodes :: [(ix,Point2 a)]
  , links :: [(ix,(ix,ix))]
  , triangles :: [(ix,[(ix,Bool)])]
  }deriving Show

testDXF = do
  Right f <- readDXF "/home/massudaw/src/triangulate/PATH.DXF"
  let ([Entity a1 ob (LWPOLYLINE _ _ _ b _ _ )],hs) = splitAt 1 $ reverse $ L.sortBy (comparing (abs . Polygon.area . PolygonCW .fmap (unconvV2 .fst) . projLine)) $  filter ((== "room").layer. eref) $ entities f
      door = filter ((== "origin").layer. eref) $ entities f
      projLine (Entity _ _ (LWPOLYLINE _ _ _ h _ _ )) = h
      pessoas = filter ((== "pessoa").layer. eref ) $ entities f
      saidas = filter ((== "saida").layer . eref ) $ entities f
      projC (Entity _ _  (CIRCLE(V3 tx ty _ ) _ )) = Point2 (tx,ty)
      entity = (fmap (unconvV2 .fst) b, fmap (fmap (unconvV2 .fst).projLine)  hs)
      po = triangulate entity
  o <- searchPaths (projC <$> pessoas) (projC <$> saidas) po
  let genPath o = (\s -> Entity a1 (ob {layer = "rotas", handle = s})  (LWPOLYLINE False 0 Nothing (fmap (\(Point2 (a,b)) -> (V2 a b  ,Nothing)) o ) Nothing Nothing ))

  writeDXF "/home/massudaw/src/triangulate/PATHW.DXF" (foldr addEntity f (genPath <$> o))


--  make a edge path oriented in CCW direction
reorderpath
  :: (Num a, Ord a) =>
     Point2 a
     -> [(t, (Point2 a, Point2 a))] -> [(t, (Point2 a, Point2 a))]
reorderpath p1 ((i,(a,b)):xs)
  | ta == 0 =  if b == p1
        then (i,(b,a)): reorderpath b xs
        else (i,(a,b)): reorderpath a xs
  | ta > 0 = (i,(a,b)): reorderpath a xs
  | ta < 0 = (i,(b,a)): reorderpath b xs
    where ta = area2 p1 a b
reorderpath p1 [] = []

-- build nearest path  using funnel and checking for target in sight
funnel _ t apx (pl,pr) xl i
  | i  + 1 >= length xl =  tip
    where
      (_,(l,r)) = xl !!  i
      deg f = id -- trace (f <> show (apx,pl,pr))
      tip
        | area2 apx pr t <= 0 &&  area2 apx pl t >= 0
          = deg "visible both" $ Just [t]
        | area2 apx pr t <= 0 && area2 apx pl t < 0
           =  deg "visible last left " $Just [l,t]
        | area2 apx pl t >= 0&& area2 apx pr t > 0
           = deg "visible last right" $ Just [r,t]
        | otherwise
           = deg "no case last" $ Just [t]
funnel  (ir,il) t apx (pl,pr) xl ip =
    let
      cr = area2 apx pr r <= 0.0
      ccr = vequal apx  pr || area2 apx pl r > 0.0
      cl = area2 apx pl l >= 0.0
      ccl = vequal apx pl || area2 apx pr l < 0.0
      i = ip +1
      (_,(l,r)) = xl !!  i

      deg f = id -- trace (f <> show (apx,pl,pr,l,r))
      ret
        | cr &&  ccr  &&  cl &&   ccl
          = deg "forwb"  $ funnel (i,i) t apx (l , r) xl i
        -- |  area2 apx pr t <= 0 &&  area2 apx pl t >= 0  && (area2 apx pl t > 0) &&  (area2 apx pr t < 0)
        --  = deg "visible"  $  Just [t]
        | (cr &&  not ccr ) &&  (cl &&   ccl)
          =
                let il = i
                    pl = l
                    apx = pl
                    iapx = il
                in (pl:) <$> deg "cutrfl"   (funnel (iapx,iapx) t apx (apx,apx) xl iapx )
        | (cr &&  ccr)  &&  (cl &&   not ccl)
          =
                let ir = i
                    pr = r
                    apx = pr
                    iapx = ir
                in (pr:) <$> deg "cutlfr" (funnel  (iapx,iapx) t apx (apx,apx) xl iapx  )
        | cr
          = if ccr
              then deg "forwr"  $ funnel (i,il) t apx (pl,r) xl i
              else
                let apx = pl
                    iapx = il
                in (pl:) <$> deg "cutr"   (funnel (iapx,iapx) t apx (apx,apx) xl iapx )
        | cl
          = if ccl
              then deg "forwl" $ funnel  (ir,i) t apx (l,pr) xl i
              else
                let apx = pr
                    iapx = ir
                in (pr:) <$> deg "cutl" (funnel  (iapx,iapx) t apx (apx,apx) xl iapx  )
        | otherwise  = deg "increment"  $ funnel  (ir,il) t apx (pl,pr) xl i
     in ret

vequal :: Point2 Double -> Point2 Double -> Bool
vequal a b  = distance a b < eq
  where eq = 1e-12


loadEdge g i = case lookE i of
               (h,t) -> (i,(lookV h,lookV t))
  where
    lookE e = fromJust $ M.lookup e (M.fromList (links g))
    lookV e = fromJust $ M.lookup e (M.fromList (nodes g))

lookT i = fromJust . L.find (flip containsBNV i.snd)


portals (pa,po) = catMaybes .fmap (flip M.lookup po) <$> pa


-- Search edges between triangles and path connection points
paths i t (g , l) =
    let
      (pini,_) = lookT i l
      (ptar,_) = lookT t l
    in (connected pini ptar gr , M.fromList $ concat $ (\(e,[(i,ib),(j,jb)]) -> [(i,(if ib then fmap swap else id )$ loadEdge g e),(j,(if jb then fmap swap else id )$  loadEdge g e)]  ) <$>  c2)
  where
    swapP (Point2 t) = Point2 (swap t)
    gr  = buildG (0,L.length l-1) $ (concat  c1)
    c1 = cote g
    c2 = cote2 g
    cote2 t = fmap (\(e,[(a,fa),(b,fb)]) ->  (e,[((a,b),fa),((b,a),fb)])) . filter ((>1) . L.length . snd) $ M.toList  li
      where li = M.fromListWith (++) $ concat $ fmap (\(ti,l)-> (\(e,i)-> (e ,pure  (ti,i))) <$> l) $ triangles t
    cote t = fmap mp . filter ((>1) . L.length . snd )$   M.toList  li
      where li = M.fromListWith (++) $ concat $ fmap (\(ti,l)-> (\(e,i)-> (e ,pure  ti)) <$> l) $ triangles t
            mp (e,[a,b]) = ([(a,b),(b,a)])
            mp (e,i ) = error (show i)

unconvV2 (V2 a b) = Point2 (a,b)
-- Triangulate and create a datastructure with nodes and edges
triangulate :: ([Point2 Double],[[Point2 Double]]) -> (PolygonSet Int Double, [(Int,Triangle Point2 Double)])
triangulate (prenodes ,holes) =  (PolygonSet (zip [0..] nodes ) (zip [0..] links) (zip [0..] trigs) ,  zip [0..] triangles)
  where
    -- nodes = prenodes
    nodes = fmap unconvV2 $ Tri.pointlist pretriangles
    centerHole = fmap (\hole -> (sum (convV2 <$> hole))^/ (fromIntegral $ length hole)) holes
    totallength = (length prenodes  + sum (fmap length holes))
    (pretriangles ,_)= traceShowId $ unsafePerformIO $ Tri.testTriangulate "pz" (traceShowId $ Tri.TriangulateIO (convV2 <$> prenodes <> concat holes) [] [] totallength 0 [] []  [] [] 0  0 0 holeSegs []    totallength centerHole  (length holes) [] 0 [] [] [] 0)
    consEdge prenodes hole = prenodes <> fmap (fmap fromIntegral) (zipWith V2 [length prenodes ..(length prenodes + length hole )-1] ([(length prenodes +1)..(length prenodes + length hole ) -1] <> [length prenodes ]))
    holeSegs =  foldl consEdge  [] (prenodes:holes)
    triangles = traceShowId $ fmap (\(V3 a b c) -> Triangle (var a,var b ,var c))$ Tri.trianglelist pretriangles
      where
        var i = fromJust $ M.lookup i (M.fromList (zip [0..] nodes ))

    triidx = (\(V3 a b c) -> [(a,b),(b,c),(c,a)]) . fmap fromIntegral <$> (Tri.trianglelist pretriangles)
    links = L.nubBy (\i j -> i == j || i == (swap j)) $ concat $ triidx
    trigs =  fmap (fmap (\i -> justError (show i) $ ((,True) <$> L.elemIndex i links)  <|> ((,False ) <$> L.elemIndex (swap i ) links )) ) triidx

justError i (Just v)  = v
justError i _ = error i

limitrange l o [] = [(o,l)]
limitrange l o (x:xs)
  | distance o x > l  = [(o ,l)] <> zip xs (repeat 0)
  | distance o x <= l  = (o, distance o x) : limitrange (l - distance o x) x xs



-- Rendering
drawEdge :: Show a => (a, (Point2 Double, Point2 Double)) -> Solid
drawEdge (i,t@(a,b@(Point2 (bx,by)))) = color (0,1,0,1) $ union (moveP b $ sphere 0.6 ) $ union (moveZ 1 $ moveP cen (scale (0.05,0.05,0.05) $ text (show i)) ) $  (extrude (Polygon (reverse [conv a, (\[i,j] -> [i -0.01,j+0.01]) (conv a) , conv b , (\[i,j] -> [i - 0.01,j+0.01]) (conv b)]) []) 0.3)
  where conv (Point2 (a,b)) = [a,b]
        cen = center t
        center (Point2 (ax,ay) , Point2 (bx,by)) = Point2 ((ax +bx)/2,(ay+by)/2)

drawTriangle (r,(i,t@(Triangle (a,b,c)))) =  color (1,r,0,1) $ union (moveZ 1 $ moveP cen (scale (0.05,0.05,0.05) $ text (show i))) $  extrude (Polygon [conv a,conv b,conv c] [] ) 0.2
  where
    cen = center t
    center (Triangle (Point2 (ax,ay),Point2 (bx,by),Point2 (cx,cy))) = Point2 ((ax + bx + cx) /3, (ay+by+cy)/3)

moveP (Point2 (x,y)) = move (x,y,0)
conv (Point2 (a,b)) = [a,b]
convV2 (Point2 (a,b)) = V2 a b
convV3 z (Point2 (a,b)) = (a, b, z)

line l = [color (0,0,1,1) $ extrude (Polygon (f <> reverse (fmap (\[i,j]-> [i-0.01 ,j+0.02]) f)) []) 0.3]
  where f = fmap conv l

genpath po  p1 p2 = f
  where a  = paths p1 p2 po
        f = fmap (\p -> (p1 :) <$> funnel (0,0) p2 p1  (p1,p1)  (reorderpath p1 p) (-1)) (portals a)


plotLimitedLine (o,l) =    union (move (convV3 (-3) o ) $ extrude ( Circle  l) 1) (move (convV3 (0) o ) $sphere 0.6)

pathDistance p =  sum $ zipWith distance p (tail p)

searchPaths p1s tar po = do
  s <- getStdGen
  let r = randoms s
  let f = concat $  fmap (\p1 -> catMaybes $ fmap (F.minimumBy (comparing (fmap pathDistance)) .genpath po p1) tar) p1s
  let lline = concat $ fmap (\f-> plotLimitedLine <$> limitrange 30 (head f) (tail f) )f
  T.writeFile "test.scad" (openSCAD (Statements $ (flip moveP (sphere 1) <$> p1s) <> fmap (flip moveP (cube 1)) tar   <> {- ( concat $ concat $ fmap (fmap drawEdge ).   (\p2 -> fmap (reorderpath p1). portals $  paths p1 p2  po ) <$> tar ) <>-} (drawTriangle <$>  (zip r $ snd po)) <> (concat $ line <$> f)))
  return (f)


