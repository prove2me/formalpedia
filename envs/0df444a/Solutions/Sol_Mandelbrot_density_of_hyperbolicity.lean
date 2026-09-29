-- Prove2me | solution 1 for Mandelbrot.density_of_hyperbolicity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T09:47:16.193842+00:00
-- url     : https://prove2.me/submissions/d7fbef80-7298-4b12-8cf3-7c85e88aff97
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mandelbrot_sets
import Theorems.Thm_Mandelbrot_density_of_hyperbolicity_general_exponent

open Topology Set Function Filter Bornology Metric MeasureTheory
open Mandelbrot

theorem _root_.solution :
    mandelbrotSet ⊆ closure {c : ℂ | ∃ m z, IsAttractingCycle (fun z ↦ z ^ 2 + c) m z} :=
  Mandelbrot.density_of_hyperbolicity_general_exponent (le_refl 2)

#print axioms solution
