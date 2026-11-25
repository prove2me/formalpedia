-- Prove2me | solution 1 for Kyprianou.Ch04.predictableLeftGridConvergesOfBounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:00:33.584455+00:00
-- url     : https://prove2.me/submissions/117210d2-4734-4f9d-b9ca-0af247e17b97

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    (q : Nat → NNReal) (t : NNReal)
    (h : ∀ n, (q n : Real) < (t : Real) ∧
      (t : Real) ≤ (q n : Real) + 1 / ((n : Real) + 1)) :
    Tendsto (fun n => (q n : Real)) atTop
      (nhdsWithin (t : Real) (Set.Iio (t : Real))) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Filter.Eventually.of_forall (fun n => (h n).1)⟩
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / eps)
  refine ⟨N, fun n hn => ?_⟩
  have hcast : (N : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hdiv : 1 / eps < (n : Real) + 1 := by linarith
  have hsmall : 1 / ((n : Real) + 1) < eps := by
    apply (div_lt_iff₀ (by positivity)).mpr
    simpa [mul_comm] using (div_lt_iff₀ heps).mp hdiv
  rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (h n).1)]
  linarith [(h n).2]
