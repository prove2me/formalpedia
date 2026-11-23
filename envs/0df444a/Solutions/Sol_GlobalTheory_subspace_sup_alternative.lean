-- Prove2me | solution 1 for GlobalTheory.subspace_sup_alternative
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:52.063145+00:00
-- url     : https://prove2.me/submissions/ba28a08a-24cf-468f-b033-7696f103b272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SubspaceSupAlternative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (K V Y σ : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype σ] (r : ℕ) (t : σ → Y → Y) (D : Y → Submodule K V → ℝ) (α : ℕ → Y → ℝ) (c Ω : ℝ), Module.finrank K V = r → 1 ≤ Ω → (∀ y W, 0 < D y W) → (∀ i ≤ r, ∀ y, IsLUB (D y '' {W | Module.finrank K W = i}) (α i y)) → (∀ y W₁ W₂, D y W₁ * D y W₂ ≤ D y (W₁ ⊓ W₂) * D y (W₁ ⊔ W₂)) → (∀ s y W, D (t s y) W ≤ Ω * D y W ∧ D y W ≤ Ω * D (t s y) W) → (∀ y W, W ≠ ⊥ → W ≠ ⊤ → ∑ s, D (t s y) W ≤ Fintype.card σ * (c * D y W)) → ∃ C : ℝ, 0 ≤ C ∧ (∀ (y : Y) (i : ℕ), 0 < i → i < r → (∑ s, α i (t s y) ≤ Fintype.card σ * (c * α i y)) ∨ ∃ j : ℕ, 0 < j ∧ j ≤ i ∧ i + j ≤ r ∧ ∀ s, α i (t s y) ≤ C * Real.sqrt (α (i - j) y * α (i + j) y))) := by
  intro K V Y σ _ _ _ _ _ r t D α c Ω hr hΩ hpos hlub hsub hmove hcon
  have hΩ0 : 0 < Ω := by linarith
  refine ⟨2 * Ω ^ 3, by positivity, fun y i hi0 hir => ?_⟩
  have hle : ∀ k ≤ r, ∀ z (W : Submodule K V), Module.finrank K W = k → D z W ≤ α k z :=
    fun k hk z W hW => (hlub k hk z).1 ⟨W, hW, rfl⟩
  have hub : ∀ k ≤ r, ∀ z (b : ℝ), (∀ W : Submodule K V, Module.finrank K W = k → D z W ≤ b) →
      α k z ≤ b := fun k hk z b hb => (hlub k hk z).2 (by
        rintro _ ⟨W, hW, rfl⟩
        exact hb W hW)
  have hex : ∀ b < α i y, ∃ W : Submodule K V, Module.finrank K W = i ∧ b < D y W := by
    intro b hb
    by_contra h
    push Not at h
    exact absurd (hub i hir.le y b h) (not_le.2 hb)
  have hA : 0 < α i y := by
    obtain ⟨W, hW, -⟩ := hex (α i y - 1) (by linarith)
    exact (hpos y W).trans_le (hle i hir.le y W hW)
  set A := α i y with hAdef
  set B := A / (2 * Ω ^ 2) with hBdef
  have hB0 : 0 < B := by positivity
  have hAB : A = 2 * Ω ^ 2 * B := by rw [hBdef]; field_simp
  have hBA : B < A := by
    have : 1 ≤ Ω ^ 2 := one_le_pow₀ hΩ
    nlinarith
  obtain ⟨W₀, hW₀, hBW₀⟩ := hex B hBA
  by_cases hcase : ∀ W : Submodule K V, Module.finrank K W = i → B < D y W → W = W₀
  · left
    have h0 : A = D y W₀ := by
      refine le_antisymm (hub i hir.le y _ fun W hW => ?_) (hle i hir.le y W₀ hW₀)
      by_cases h : B < D y W
      · rw [hcase W hW h]
      · exact (not_lt.1 h).trans hBW₀.le
    have h1 : ∀ s, α i (t s y) ≤ D (t s y) W₀ := by
      intro s
      refine hub i hir.le _ _ fun W hW => ?_
      by_cases h : B < D y W
      · rw [hcase W hW h]
      · have a1 := (hmove s y W).1
        have a2 := (hmove s y W₀).2
        have a3 : Ω * D y W ≤ Ω * B := mul_le_mul_of_nonneg_left (not_lt.1 h) hΩ0.le
        have a4 : Ω * (Ω * B) ≤ Ω * D (t s y) W₀ := by
          have : 0 < Ω ^ 2 * B := by positivity
          nlinarith
        have a5 := le_of_mul_le_mul_left a4 hΩ0
        linarith
    have hb : W₀ ≠ ⊥ := by
      rintro rfl
      rw [finrank_bot] at hW₀
      omega
    have ht : W₀ ≠ ⊤ := by
      rintro rfl
      rw [finrank_top] at hW₀
      omega
    rw [h0]
    exact (Finset.sum_le_sum fun s _ => h1 s).trans (hcon y W₀ hb ht)
  · right
    push Not at hcase
    obtain ⟨W₁, hW₁, hBW₁, hne⟩ := hcase
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₀
    have hlt : Module.finrank K ↥(W₁ ⊓ W₀) < i := by
      rw [← hW₁]
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hne ?_)
      exact Submodule.eq_of_le_of_finrank_eq (inf_eq_left.1 h) (hW₁.trans hW₀.symm)
    have hsr : Module.finrank K ↥(W₁ ⊔ W₀) ≤ r := hr ▸ Submodule.finrank_le _
    refine ⟨i - Module.finrank K ↥(W₁ ⊓ W₀), by omega, by omega, by omega, fun s => ?_⟩
    set j := i - Module.finrank K ↥(W₁ ⊓ W₀) with hj
    have e1 : D y (W₁ ⊓ W₀) ≤ α (i - j) y := hle _ (by omega) y _ (by omega)
    have e2 : D y (W₁ ⊔ W₀) ≤ α (i + j) y := hle _ (by omega) y _ (by omega)
    have e3 : B ^ 2 ≤ α (i - j) y * α (i + j) y := by
      calc B ^ 2 = B * B := sq B
        _ ≤ D y W₁ * D y W₀ := mul_le_mul hBW₁.le hBW₀.le hB0.le (hpos _ _).le
        _ ≤ _ := hsub y W₁ W₀
        _ ≤ _ := mul_le_mul e1 e2 (hpos _ _).le ((hpos _ _).le.trans e1)
    have e4 : B ≤ Real.sqrt (α (i - j) y * α (i + j) y) := Real.le_sqrt_of_sq_le e3
    have e5 : α i (t s y) ≤ Ω * A := hub i hir.le _ _ fun W hW =>
      (hmove s y W).1.trans (mul_le_mul_of_nonneg_left (hle i hir.le y W hW) hΩ0.le)
    calc α i (t s y) ≤ Ω * A := e5
      _ = 2 * Ω ^ 3 * B := by rw [hAB]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)
end GlobalTheory
