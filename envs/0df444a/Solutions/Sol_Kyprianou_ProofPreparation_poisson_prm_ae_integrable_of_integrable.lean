-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_prm_ae_integrable_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T13:24:32.543169+00:00
-- url     : https://prove2.me/submissions/e2c3e1ce-49a0-48d2-a89a-dbf15fbe4f91

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_lintegral_lintegral_poissonRandomMeasure
import Theorems.Thm_Kyprianou_ProofPreparation_measurable_lintegral_poissonRandomMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Intensity L1 integrability gives samplewise Poisson L1 integrability almost surely. -/
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    (f : E → ℝ) (hf : Measurable f) (hfi : Integrable f m) :
    ∀ᵐ ω ∂P, Integrable f
      (ProbabilityTheory.poissonRandomMeasure K Y ω) := by
  have hm : Measurable (fun ω =>
      ∫⁻ x, ‖f x‖ₑ ∂(poissonRandomMeasure K Y ω)) :=
    Kyprianou.ProofPreparation.measurable_lintegral_poissonRandomMeasure
      P m K Y hd hf.enorm
  have hc : (∫⁻ ω, (∫⁻ x, ‖f x‖ₑ ∂
      (poissonRandomMeasure K Y ω)) ∂P) =
      ∫⁻ x, ‖f x‖ₑ ∂m :=
    lintegral_lintegral_poissonRandomMeasure hd hf.enorm
  have hfinite : (∫⁻ ω, (∫⁻ x, ‖f x‖ₑ ∂
      (poissonRandomMeasure K Y ω)) ∂P) ≠ ⊤ := by
    rw [hc]
    exact hfi.hasFiniteIntegral.ne
  have he : ∀ᵐ ω ∂P,
      (∫⁻ x, ‖f x‖ₑ ∂(poissonRandomMeasure K Y ω)) < ⊤ :=
    ae_lt_top hm hfinite
  filter_upwards [he] with ω hω
  exact ⟨hf.aestronglyMeasurable, hω⟩
