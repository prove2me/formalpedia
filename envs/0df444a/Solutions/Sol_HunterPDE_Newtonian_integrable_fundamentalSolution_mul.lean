-- Prove2me | solution 1 for HunterPDE.Newtonian.integrable_fundamentalSolution_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T21:27:31.402996+00:00
-- url     : https://prove2.me/submissions/bbf8c7c6-d8f0-4b88-b380-27ea1da2c778

import Theorems.Thm_HunterPDE_Newtonian_locallyIntegrable_fundamentalSolution
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory HunterPDE.Newtonian

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 2 ≤ n)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => fundamentalSolution n (x - y) * g y) := by
  have hc : Continuous (fun z => g (x - z)) :=
    hg.comp (continuous_const.sub continuous_id)
  have hcc : HasCompactSupport (fun z => g (x - z)) :=
    hgc.comp_homeomorph (Homeomorph.subLeft x)
  have hi := (locallyIntegrable_fundamentalSolution n hn).integrable_smul_right_of_hasCompactSupport hc hcc
  simpa only [smul_eq_mul, sub_sub_cancel] using hi.comp_sub_left x
