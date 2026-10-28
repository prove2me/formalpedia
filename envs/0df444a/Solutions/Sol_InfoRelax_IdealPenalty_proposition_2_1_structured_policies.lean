-- Prove2me | solution 1 for InfoRelax.IdealPenalty.proposition_2_1_structured_policies
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:05:20.290195+00:00
-- url     : https://prove2.me/submissions/fa033e23-95e5-46d6-a5c3-d265b7f41b34

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework

open MeasureTheory

namespace Aux_IRP21
open InfoRelax.IdealPenalty

lemma core {Ω X : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace X] {T : ℕ} (μ : Measure Ω)
    (A : Set (Fin (T + 1) → X)) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (r : (Fin (T + 1) → X) → Ω → ℝ) (hr : RewardIntegrable μ A r) (h𝔾 : IsRelaxation 𝔽 𝔾)
    (S : Set (Ω → Fin (T + 1) → X)) (hS : S ⊆ policies A)
    (hSopt : primalValue μ A 𝔽 r = supValue μ (S ∩ adaptedPolicies A 𝔽) r)
    (z : (Fin (T + 1) → X) → Ω → ℝ) (hz : z ∈ penalties μ A)
    (hz0 : ∀ α ∈ S ∩ adaptedPolicies A 𝔽, ∫ ω, z (α ω) ω ∂μ ≤ 0) :
    primalValue μ A 𝔽 r ≤
        supValue μ (S ∩ adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω) ∧
      supValue μ (S ∩ adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω) ≤
        dualBound μ A 𝔾 r z := by
  refine ⟨?_, ?_⟩
  · rw [hSopt]
    unfold supValue
    refine iSup₂_le fun α hα => ?_
    have hαG : α ∈ S ∩ adaptedPolicies A 𝔾 :=
      ⟨hα.1, hα.2.1, fun t => (hα.2.2 t).mono (h𝔾 t) le_rfl⟩
    refine le_iSup₂_of_le α hαG ?_
    have hP := hS hα.1
    have hsub : ∫ ω, (r (α ω) ω - z (α ω) ω) ∂μ
        = ∫ ω, r (α ω) ω ∂μ - ∫ ω, z (α ω) ω ∂μ := integral_sub (hr α hP) (hz α hP)
    have hle := hz0 α hα
    exact EReal.coe_le_coe_iff.mpr (by rw [hsub]; linarith)
  · unfold dualBound supValue
    exact biSup_mono fun α h => h.2

end Aux_IRP21

open InfoRelax.IdealPenalty in
theorem solution {Ω X : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace X] {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set (Fin (T + 1) → X)) (hA : A.Nonempty) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (r : (Fin (T + 1) → X) → Ω → ℝ) (hr : RewardIntegrable μ A r) (h𝔾 : IsRelaxation 𝔽 𝔾)
    (S : Set (Ω → Fin (T + 1) → X)) (hS : S ⊆ policies A)
    (hSopt : primalValue μ A 𝔽 r = supValue μ (S ∩ adaptedPolicies A 𝔽) r) :
    (∀ z ∈ dualFeasible μ A 𝔽,
        primalValue μ A 𝔽 r ≤
            supValue μ (S ∩ adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω) ∧
          supValue μ (S ∩ adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω) ≤
            dualBound μ A 𝔾 r z) ∧
      (∀ z ∈ penalties μ A,
        (∀ α ∈ S ∩ adaptedPolicies A 𝔽, ∫ ω, z (α ω) ω ∂μ ≤ 0) →
          primalValue μ A 𝔽 r ≤
              supValue μ (S ∩ adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω) ∧
            supValue μ (S ∩ adaptedPolicies A 𝔾) (fun a ω => r a ω - z a ω) ≤
              dualBound μ A 𝔾 r z) := by
  refine ⟨fun z hz => ?_, fun z hz hz0 => ?_⟩
  · exact Aux_IRP21.core μ A 𝔽 𝔾 r hr h𝔾 S hS hSopt z hz.1 (fun α hα => hz.2 α hα.2)
  · exact Aux_IRP21.core μ A 𝔽 𝔾 r hr h𝔾 S hS hSopt z hz hz0
