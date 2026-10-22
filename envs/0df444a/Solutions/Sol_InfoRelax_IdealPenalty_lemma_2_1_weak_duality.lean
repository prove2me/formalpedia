-- Prove2me | solution 1 for InfoRelax.IdealPenalty.lemma_2_1_weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:33:34.198407+00:00
-- url     : https://prove2.me/submissions/4d50bcea-f714-448d-b5a7-2024973e3986

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework

set_option autoImplicit false
open MeasureTheory InfoRelax.IdealPenalty

theorem solution {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set (Fin (T + 1) → X))
    (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ) (r : (Fin (T + 1) → X) → Ω → ℝ)
    (hr : RewardIntegrable μ A r) (h𝔾 : IsRelaxation 𝔽 𝔾)
    (α : Ω → Fin (T + 1) → X) (hα : α ∈ adaptedPolicies A 𝔽)
    (z : (Fin (T + 1) → X) → Ω → ℝ) (hz : z ∈ dualFeasible μ A 𝔽) :
    ((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal) ≤ dualBound μ A 𝔾 r z := by
  have hαG : α ∈ adaptedPolicies A 𝔾 := ⟨hα.1, fun t => (hα.2 t).mono (h𝔾 t) le_rfl⟩
  have hpol : α ∈ policies (Ω := Ω) A :=
    ⟨hα.1, fun t => (hα.2 t).mono (𝔽.le t) le_rfl⟩
  have h1 := hr α hpol
  have h2 := hz.1 α hpol
  have h3 := hz.2 α hα
  have h4 : (∫ ω, r (α ω) ω ∂μ) ≤ ∫ ω, (r (α ω) ω - z (α ω) ω) ∂μ := by
    rw [integral_sub h1 h2]; linarith
  calc ((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal)
      ≤ ((∫ ω, (r (α ω) ω - z (α ω) ω) ∂μ : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr h4
    _ ≤ dualBound μ A 𝔾 r z := by
      unfold dualBound supValue
      exact le_iSup₂ (f := fun (β : Ω → Fin (T + 1) → X) (_ : β ∈ adaptedPolicies A 𝔾) =>
        ((∫ ω, (r (β ω) ω - z (β ω) ω) ∂μ : ℝ) : EReal)) α hαG
