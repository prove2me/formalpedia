-- Prove2me | solution 1 for InfoRelax.IdealPenalty.theorem_2_2_complementary_slackness
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:07:55.765492+00:00
-- url     : https://prove2.me/submissions/d4328aaa-e95c-4354-aad6-84380c523831

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework

open MeasureTheory

open InfoRelax.IdealPenalty in
theorem solution {Ω X : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace X] {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set (Fin (T + 1) → X)) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ)
    (r : (Fin (T + 1) → X) → Ω → ℝ) (hr : RewardIntegrable μ A r) (h𝔾 : IsRelaxation 𝔽 𝔾)
    (α : Ω → Fin (T + 1) → X) (hα : α ∈ adaptedPolicies A 𝔽)
    (z : (Fin (T + 1) → X) → Ω → ℝ) (hz : z ∈ dualFeasible μ A 𝔽) :
    (((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal) = primalValue μ A 𝔽 r ∧
        dualBound μ A 𝔾 r z = dualValue μ A 𝔽 𝔾 r) ↔
      (∫ ω, z (α ω) ω ∂μ = 0 ∧
        ((∫ ω, (r (α ω) ω - z (α ω) ω) ∂μ : ℝ) : EReal) = dualBound μ A 𝔾 r z) := by
  have hAFG : ∀ β, β ∈ adaptedPolicies A 𝔽 → β ∈ adaptedPolicies A 𝔾 :=
    fun β h => ⟨h.1, fun t => (h.2 t).mono (h𝔾 t) le_rfl⟩
  have hAFP : ∀ β, β ∈ adaptedPolicies A 𝔽 → β ∈ policies A :=
    fun β h => ⟨h.1, fun t => (h.2 t).mono (𝔽.le t) le_rfl⟩
  have weak : ∀ z' ∈ dualFeasible μ A 𝔽, primalValue μ A 𝔽 r ≤ dualBound μ A 𝔾 r z' := by
    intro z' hz'
    unfold primalValue dualBound supValue
    refine iSup₂_le fun β hβ => le_iSup₂_of_le β (hAFG β hβ) ?_
    have hs : ∫ ω, (r (β ω) ω - z' (β ω) ω) ∂μ = ∫ ω, r (β ω) ω ∂μ - ∫ ω, z' (β ω) ω ∂μ :=
      integral_sub (hr β (hAFP β hβ)) (hz'.1 β (hAFP β hβ))
    have := hz'.2 β hβ
    exact EReal.coe_le_coe_iff.mpr (by rw [hs]; linarith)
  have hPD : primalValue μ A 𝔽 r ≤ dualValue μ A 𝔽 𝔾 r := le_iInf₂ fun z' hz' => weak z' hz'
  have hDB : dualValue μ A 𝔽 𝔾 r ≤ dualBound μ A 𝔾 r z := iInf₂_le z hz
  have haP : ((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal) ≤ primalValue μ A 𝔽 r :=
    le_iSup₂_of_le (f := fun β (_ : β ∈ adaptedPolicies A 𝔽) =>
      ((∫ ω, r (β ω) ω ∂μ : ℝ) : EReal)) α hα le_rfl
  have hacB : ((∫ ω, (r (α ω) ω - z (α ω) ω) ∂μ : ℝ) : EReal) ≤ dualBound μ A 𝔾 r z :=
    le_iSup₂_of_le (f := fun β (_ : β ∈ adaptedPolicies A 𝔾) =>
      ((∫ ω, (r (β ω) ω - z (β ω) ω) ∂μ : ℝ) : EReal)) α (hAFG α hα) le_rfl
  have hsα : ∫ ω, (r (α ω) ω - z (α ω) ω) ∂μ = ∫ ω, r (α ω) ω ∂μ - ∫ ω, z (α ω) ω ∂μ :=
    integral_sub (hr α (hAFP α hα)) (hz.1 α (hAFP α hα))
  have hc : ∫ ω, z (α ω) ω ∂μ ≤ 0 := hz.2 α hα
  have strong : ((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal) = primalValue μ A 𝔽 r →
      dualValue μ A 𝔽 𝔾 r ≤ ((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal) := by
    intro hP
    set a := ∫ ω, r (α ω) ω ∂μ with ha
    have hzs : (fun b ω => r b ω - a) ∈ dualFeasible μ A 𝔽 := by
      refine ⟨fun β hβ => (hr β hβ).sub (integrable_const a), fun β hβ => ?_⟩
      have hs : ∫ ω, (r (β ω) ω - a) ∂μ = ∫ ω, r (β ω) ω ∂μ - a := by
        rw [integral_sub (hr β (hAFP β hβ)) (integrable_const a)]
        simp
      have hle : ((∫ ω, r (β ω) ω ∂μ : ℝ) : EReal) ≤ (a : EReal) := by
        rw [hP]
        exact le_iSup₂_of_le (f := fun β (_ : β ∈ adaptedPolicies A 𝔽) =>
          ((∫ ω, r (β ω) ω ∂μ : ℝ) : EReal)) β hβ le_rfl
      have := EReal.coe_le_coe_iff.mp hle
      rw [hs]; linarith
    refine (iInf₂_le _ hzs).trans ?_
    unfold dualBound supValue
    refine iSup₂_le fun β _ => ?_
    simp
  constructor
  · rintro ⟨hP, hBD⟩
    have hDa := strong hP
    have h1 : ((∫ ω, (r (α ω) ω - z (α ω) ω) ∂μ : ℝ) : EReal)
        ≤ ((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal) := hacB.trans (hBD ▸ hDa)
    have h2 := EReal.coe_le_coe_iff.mp h1
    rw [hsα] at h2
    have hc0 : ∫ ω, z (α ω) ω ∂μ = 0 := by linarith
    refine ⟨hc0, le_antisymm hacB ?_⟩
    rw [hsα, hc0, sub_zero, hBD]
    exact hDa
  · rintro ⟨hc0, hEq⟩
    rw [hsα, hc0, sub_zero] at hEq
    refine ⟨le_antisymm haP ?_, le_antisymm ?_ hDB⟩
    · rw [hEq]; exact hPD.trans hDB
    · rw [← hEq]; exact haP.trans hPD
