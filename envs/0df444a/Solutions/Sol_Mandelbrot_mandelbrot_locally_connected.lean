-- Prove2me | solution 1 for Mandelbrot.mandelbrot_locally_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T09:51:00.512459+00:00
-- url     : https://prove2.me/submissions/1cc64034-abb7-48d7-8355-afc69f96aafb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mandelbrot_sets
import Theorems.Thm_Mandelbrot_multibrot_locally_connected

open Topology Set Function Filter Bornology Metric MeasureTheory

theorem _root_.solution : LocallyConnectedSpace Mandelbrot.mandelbrotSet :=
  Mandelbrot.multibrot_locally_connected 2

#print axioms solution
