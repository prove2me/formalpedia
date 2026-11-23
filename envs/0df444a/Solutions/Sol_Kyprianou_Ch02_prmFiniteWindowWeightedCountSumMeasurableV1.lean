-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteWindowWeightedCountSumMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:24:30.728857+00:00
-- url     : https://prove2.me/submissions/ac7eb9db-b4ec-4f57-b36a-1b377dad4d8e

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ) (C : Fin n → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i)) (w : Fin n → ℝ) :
    Measurable (fun (ω : Ω) =>
      ∑ i : Fin n, (w i) *
        (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i))).toReal) := by
  classical
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have hR :
      MeasurableSet (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ (B ∩ C i)) :=
    measurableSet_Ioc.prod (hB.inter (hC i))
  exact measurable_const.mul
    (ENNReal.measurable_toReal.comp (N.measurable_eval hR))
