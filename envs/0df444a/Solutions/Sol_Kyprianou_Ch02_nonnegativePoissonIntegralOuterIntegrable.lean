-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegativePoissonIntegralOuterIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:31:28.075075+00:00
-- url     : https://prove2.me/submissions/238d09b5-a86e-4f7d-a39c-d4474eb5fcd4

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_lintegral_lintegral_poissonRandomMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Outer integrability follows from finite nonnegative Campbell mean. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (hfi : Integrable f m) :
    Integrable (fun ω => ∫ x, f x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) P := by
  let Q : Ω → Measure E := fun ω => poissonRandomMeasure K Y ω
  let g : E → ENNReal := fun x => ENNReal.ofReal (f x)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp hf
  have hQ : Measurable Q :=
    Measure.measurable_of_measurable_coe Q (by
      intro A hA
      exact measurable_poissonRandomMeasure_apply
        hd.measurable_count hd.measurable_point hA)
  have hG : Measurable (fun ω => ∫⁻ x, g x ∂Q ω) :=
    (Measure.measurable_lintegral hg).comp hQ
  have hfin : (∫⁻ ω, (∫⁻ x, g x ∂Q ω) ∂P) ≠ ⊤ := by
    rw [lintegral_lintegral_poissonRandomMeasure hd hg]
    exact ((hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hfn)).mp hfi.hasFiniteIntegral).ne
  have hInt := integrable_toReal_of_lintegral_ne_top hG.aemeasurable hfin
  have heq : (fun ω => (∫⁻ x, g x ∂Q ω).toReal) =
      (fun ω => ∫ x, f x ∂Q ω) := by
    funext ω
    exact (integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall hfn) hf.aestronglyMeasurable).symm
  simpa only [heq] using hInt
