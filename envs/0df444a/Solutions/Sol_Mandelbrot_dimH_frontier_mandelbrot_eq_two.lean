-- Prove2me | solution 1 for Mandelbrot.dimH_frontier_mandelbrot_eq_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-24T21:44:05.262621+00:00
-- url     : https://prove2.me/submissions/c1721509-a587-4d18-925b-45ddd132985e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mandelbrot_sets
import Theorems.Thm_Mandelbrot_exists_hyperbolicSet_dimH_gt
import Theorems.Thm_Mandelbrot_dimH_hyperbolicSet_le_dimH_frontier_inter
open Topology Set Function Filter Bornology Metric MeasureTheory

theorem solution : dimH (frontier Mandelbrot.mandelbrotSet) = 2 := by
  apply le_antisymm
  · calc dimH (frontier Mandelbrot.mandelbrotSet) ≤ dimH (univ : Set ℂ) :=
          dimH_mono (subset_univ _)
      _ = 2 := by rw [Real.dimH_univ_eq_finrank, Complex.finrank_real_complex]; rfl
  · refine le_of_forall_lt fun d hd => ?_
    obtain ⟨c, hc, K, hK, hdK⟩ := Mandelbrot.exists_hyperbolicSet_dimH_gt d hd
    calc d < dimH K := hdK
      _ ≤ dimH (frontier Mandelbrot.mandelbrotSet ∩ univ) :=
          Mandelbrot.dimH_hyperbolicSet_le_dimH_frontier_inter c hc K hK univ univ_mem
      _ ≤ dimH (frontier Mandelbrot.mandelbrotSet) := dimH_mono inter_subset_left
