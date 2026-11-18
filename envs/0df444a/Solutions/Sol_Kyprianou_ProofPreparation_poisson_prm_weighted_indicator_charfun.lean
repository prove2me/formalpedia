-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_weighted_indicator_charfun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:28:51.664827+00:00
-- url     : https://prove2.me/submissions/3fea2dfc-facb-4218-8009-1d506ad6421e

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_charFun_natCast_poissonRandomMeasure_apply

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The characteristic function of a weighted Poisson indicator integral. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (A : Set E) (hA : MeasurableSet A) (hfin : m A < ⊤)
    (a ξ : ℝ) :
    charFun (P.map (fun ω => ∫ x, a * A.indicator (fun _ => (1 : ℝ)) x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω))) ξ =
      Complex.exp (((m A).toReal : ℂ) *
        (Complex.exp ((((a * ξ : ℝ) : ℂ)) * Complex.I) - 1)) := by
  let Z : Ω → ℝ := fun ω => (poissonRandomMeasure K Y ω A).toReal
  have hZ : Measurable Z :=
    ENNReal.measurable_toReal.comp
      (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA)
  have hEval :
      (fun ω => ∫ x, a * A.indicator (fun _ => (1 : ℝ)) x ∂
        (poissonRandomMeasure K Y ω)) =
      (fun ω => a * Z ω) := by
    funext ω
    rw [integral_const_mul]
    exact congrArg (fun z : ℝ => a * z) (integral_indicator_one hA)
  rw [hEval]
  exact (charFun_map_mul_comp hZ.aemeasurable a ξ).trans
    (charFun_natCast_poissonRandomMeasure_apply hd hA hfin (a * ξ))
