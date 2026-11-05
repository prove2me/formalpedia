-- Prove2me | solution 1 for InfoRelax.IdealPenalty.theorem_2_1_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T23:11:53.279653+00:00
-- url     : https://prove2.me/submissions/602c9827-4c07-435e-a310-5c1d698fc1ff

import Mathlib
import Definitions.Def_InfoRelax_IdealPenalty_Framework

set_option autoImplicit false
open MeasureTheory InfoRelax.IdealPenalty

theorem solution {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    {T : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set (Fin (T + 1) → X))
    (hA : A.Nonempty) (𝔽 𝔾 : Filtration (Fin (T + 1)) mΩ) (r : (Fin (T + 1) → X) → Ω → ℝ)
    (hr : RewardIntegrable μ A r) (h𝔾 : IsRelaxation 𝔽 𝔾) :
    primalValue μ A 𝔽 r = dualValue μ A 𝔽 𝔾 r ∧
      (primalValue μ A 𝔽 r ≠ ⊤ →
        ∃ z ∈ dualFeasible μ A 𝔽, dualBound μ A 𝔾 r z = primalValue μ A 𝔽 r) := by
  have hFG : 𝔽 ≤ 𝔾 := h𝔾
  obtain ⟨a0, ha0⟩ := hA
  -- F-adapted policies are G-adapted and measurable
  have hFpol : ∀ α ∈ adaptedPolicies A 𝔽, α ∈ adaptedPolicies A 𝔾 :=
    fun α hα => ⟨hα.1, fun t => (hα.2 t).mono (hFG t) le_rfl⟩
  have hFmeas : ∀ α ∈ adaptedPolicies A 𝔽, α ∈ policies (Ω := Ω) A :=
    fun α hα => ⟨hα.1, fun t => (hα.2 t).mono (𝔽.le t) le_rfl⟩
  have hconst : ∀ 𝔾' : Filtration (Fin (T + 1)) mΩ,
      (fun _ : Ω => a0) ∈ adaptedPolicies A 𝔾' :=
    fun _ => ⟨fun _ => ha0, fun _ => measurable_const⟩
  -- weak duality
  have hweak : ∀ z ∈ dualFeasible μ A 𝔽, primalValue μ A 𝔽 r ≤ dualBound μ A 𝔾 r z := by
    intro z hz
    unfold primalValue supValue
    refine iSup₂_le fun α hα => ?_
    have h1 : ∫ ω, r (α ω) ω ∂μ ≤ ∫ ω, (r (α ω) ω - z (α ω) ω) ∂μ := by
      rw [integral_sub (hr α (hFmeas α hα)) (hz.1 α (hFmeas α hα))]
      linarith [hz.2 α hα]
    refine (EReal.coe_le_coe_iff.2 h1).trans ?_
    unfold dualBound supValue
    exact le_iSup₂ (f := fun α (_ : α ∈ adaptedPolicies A 𝔾) =>
      ((∫ ω, (r (α ω) ω - z (α ω) ω) ∂μ : ℝ) : EReal)) α (hFpol α hα)
  have hle : primalValue μ A 𝔽 r ≤ dualValue μ A 𝔽 𝔾 r := by
    unfold dualValue
    exact le_iInf₂ fun z hz => hweak z hz
  -- the primal value is not ⊥
  have hbot : ((∫ ω, r a0 ω ∂μ : ℝ) : EReal) ≤ primalValue μ A 𝔽 r := by
    unfold primalValue supValue
    exact le_iSup₂ (f := fun α (_ : α ∈ adaptedPolicies A 𝔽) =>
      ((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal)) (fun _ => a0) (hconst 𝔽)
  -- the optimal penalty for a finite primal value
  have hopt : ∀ v : ℝ, primalValue μ A 𝔽 r = v →
      ∃ z ∈ dualFeasible μ A 𝔽, dualBound μ A 𝔾 r z = primalValue μ A 𝔽 r := by
    intro v hv
    refine ⟨fun a ω => r a ω - v, ⟨fun α hα => (hr α hα).sub (integrable_const v),
      fun α hα => ?_⟩, ?_⟩
    · rw [integral_sub (hr α (hFmeas α hα)) (integrable_const v)]
      have : ((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal) ≤ primalValue μ A 𝔽 r := by
        unfold primalValue supValue
        exact le_iSup₂ (f := fun α (_ : α ∈ adaptedPolicies A 𝔽) =>
          ((∫ ω, r (α ω) ω ∂μ : ℝ) : EReal)) α hα
      rw [hv] at this
      have := EReal.coe_le_coe_iff.1 this
      simp only [integral_const, probReal_univ, one_smul]
      linarith
    · rw [hv]
      unfold dualBound supValue
      have e : ∀ α : Ω → Fin (T + 1) → X,
          ∫ ω, (r (α ω) ω - (r (α ω) ω - v)) ∂μ = v := by
        intro α; simp
      simp_rw [e]
      apply le_antisymm
      · exact iSup₂_le fun _ _ => le_rfl
      · exact le_iSup₂ (f := fun α (_ : α ∈ adaptedPolicies A 𝔾) => (v : EReal))
          (fun _ => a0) (hconst 𝔾)
  refine ⟨?_, ?_⟩
  · apply le_antisymm hle
    by_cases htop : primalValue μ A 𝔽 r = ⊤
    · rw [htop]; exact le_top
    · have hne : primalValue μ A 𝔽 r ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hbot
      obtain ⟨v, hv⟩ : ∃ v : ℝ, primalValue μ A 𝔽 r = v :=
        ⟨(primalValue μ A 𝔽 r).toReal, (EReal.coe_toReal htop hne).symm⟩
      obtain ⟨z, hz, hzv⟩ := hopt v hv
      unfold dualValue
      exact (iInf₂_le z hz).trans hzv.le
  · intro htop
    have hne : primalValue μ A 𝔽 r ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hbot
    exact hopt _ (EReal.coe_toReal htop hne).symm
