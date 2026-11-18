-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegativePoissonIntegralFirstMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:31:03.422212+00:00
-- url     : https://prove2.me/submissions/35e835f6-f8de-46ea-9fd4-179c45b2fedf

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_lintegral_lintegral_poissonRandomMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A direct nonnegative Campbell argument, including almost-sure integrability. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (hfi : Integrable f m) :
    (∀ᵐ ω ∂P, Integrable f
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∧
    (∫ ω, (∫ x, f x ∂
      (ProbabilityTheory.poissonRandomMeasure K Y ω)) ∂P) =
      ∫ x, f x ∂m := by
  let g : E → ENNReal := fun x => ENNReal.ofReal (f x)
  let N : Ω → Measure E := fun ω => poissonRandomMeasure K Y ω
  have hg : Measurable g := ENNReal.measurable_ofReal.comp hf
  have hN : Measurable N :=
    Measure.measurable_of_measurable_coe N (by
      intro A hA
      exact measurable_poissonRandomMeasure_apply
        hd.measurable_count hd.measurable_point hA)
  have hG : Measurable (fun ω => ∫⁻ x, g x ∂N ω) :=
    (Measure.measurable_lintegral hg).comp hN
  have hcamp :
      (∫⁻ ω, (∫⁻ x, g x ∂N ω) ∂P) = ∫⁻ x, g x ∂m :=
    lintegral_lintegral_poissonRandomMeasure hd hg
  have hfin : (∫⁻ ω, (∫⁻ x, g x ∂N ω) ∂P) < ⊤ := by
    rw [hcamp]
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hfn)).mp hfi.hasFiniteIntegral
  have hae : ∀ᵐ ω ∂P, (∫⁻ x, g x ∂N ω) < ⊤ :=
    ae_lt_top hG hfin.ne
  have hs : ∀ᵐ ω ∂P, Integrable f (N ω) := by
    filter_upwards [hae] with ω hw
    have hh := integrable_toReal_of_lintegral_ne_top
      hg.aemeasurable hw.ne
    have heq : (fun x => (g x).toReal) = f := by
      funext x
      exact ENNReal.toReal_ofReal (hfn x)
    simpa only [heq] using hh
  refine ⟨hs, ?_⟩
  calc
    (∫ ω, (∫ x, f x ∂N ω) ∂P) =
      ∫ ω, (∫⁻ x, g x ∂N ω).toReal ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω =>
          integral_eq_lintegral_of_nonneg_ae
            (Filter.Eventually.of_forall hfn) hf.aestronglyMeasurable
    _ = (∫⁻ x, g x ∂m).toReal := by
      rw [integral_toReal hG.aemeasurable hae, hcamp]
    _ = ∫ x, f x ∂m :=
      (integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall hfn) hf.aestronglyMeasurable).symm
