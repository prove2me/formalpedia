-- Prove2me | solution 1 for GlobalTheory.FinWeil.invariantForm_normOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:10.354808+00:00
-- url     : https://prove2.me/submissions/c420f407-66d8-4878-ac99-f59f5614b87a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InvariantFormNormalizedHeisenbergIntertwinerEq
import Theorems.Thm_GlobalTheory_FinWeil_invariantForm_translate_eq_zero
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_comm
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_iso
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_ne_zero
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_swap
import Theorems.Thm_GlobalTheory_FinWeil_IsHeis_zero_right
import Theorems.Thm_GlobalTheory_FinWeil_exists_transversal_of_idx_ne_zero
import Theorems.Thm_GlobalTheory_FinWeil_sumOp_eq_sum_transversal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinWeil
theorem _root_.solution : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ P Q : X →ₗ[R] X, (∀ x, P (P x) = P x) → (∀ x, Q (Q x) = Q x) → (∀ x, P (Q x) = 0) → (∀ x, Q (P x) = 0) → (∀ x y, γ (P x) y = γ x (Q y)) → (∀ a ∈ A, P a ∈ A) → (∀ a ∈ A, Q a ∈ A) → (∀ x, φ (P x) = P (φ x)) → (∀ x, φ (Q x) = Q (φ x)) → (∀ x, φ x - P (φ x) - Q (φ x) = x - P x - Q x) → ∃ n : ℕ, 0 < n ∧ ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ m, ℓ (T m) = (lam (idx A (A.map φ)))⁻¹ * (n : ℂ) * ℓ m := by
  intro R X M _ _ _ _ _ σ w γ W h lam A hA hspan φ hφ hφA hidx T hT hTe P Q hPP hQQ hPQ hQP hadj hPA hQA hφP hφQ hφr
  have hQadj : ∀ u v, γ (Q u) v = γ u (P v) := fun u v => by
    rw [h.swap, ← hadj, ← h.swap]
  have hPr : ∀ u y, γ (P u) (y - P y - Q y) = 1 := fun u y => by
    rw [hadj, map_sub, map_sub, hQP, hQQ, sub_zero, sub_self, h.zero_right]
  have hQr : ∀ u y, γ (Q u) (y - P y - Q y) = 1 := fun u y => by
    rw [hQadj, map_sub, map_sub, hPP, hPQ, sub_self, sub_zero, h.zero_right]
  have hrP : ∀ u y, γ (y - P y - Q y) (P u) = 1 := fun u y => by
    rw [h.swap, hPr, inv_one]
  have hsm : ∀ y : X, w • (y - P y - Q y) = w • y - P (w • y) - Q (w • y) := fun y => by
    simp only [smul_sub, map_smul]

  have hsplit : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ (y : X) (v : M),
      γ (w • Q y) (y - Q y) * ℓ (W y v) = ℓ (W (y - P y - Q y) (W (P y) v)) := by
    intro ℓ hl y v
    have e1 := hl y (W (y - Q y) v)
    rw [h.comp, show Q y + (y - Q y) = y by abel, map_smul, smul_eq_mul] at e1
    rw [e1, h.comp, hsm, hrP, one_smul, show y - P y - Q y + P y = y - Q y by abel]
  have hinvρ : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ y : X,
      ∀ u m, (ℓ.comp (W (y - P y - Q y))) (W (Q u) m) = (ℓ.comp (W (y - P y - Q y))) m := by
    intro ℓ hl y u m
    simp only [LinearMap.comp_apply]
    rw [h.comm, map_smul, smul_eq_mul, h.swap, hQr, inv_one, one_mul, hl]
  have hinvT : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) →
      ∀ u m, (ℓ.comp T) (W (Q u) m) = (ℓ.comp T) m := by
    intro ℓ hl u m
    simp only [LinearMap.comp_apply]
    rw [hT, hφQ, hl]

  have hterm : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ e, Fixes W A e →
      ∀ b ∈ A.map φ, ℓ (W b e) = ℓ (W (P b) e) := by
    intro ℓ hl e he b hb
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hb
    have hQb : Q (φ a) ∈ A.map φ := by
      rw [← hφQ]; exact Submodule.mem_map_of_mem (hQA a ha)
    have hd : φ a - Q (φ a) ∈ A.map φ := Submodule.sub_mem _ hb hQb
    have hr : φ a - P (φ a) - Q (φ a) ∈ A := by
      rw [hφr]; exact Submodule.sub_mem _ (Submodule.sub_mem _ ha (hPA a ha)) (hQA a ha)
    have h1 : W (Q (φ a)) (W (φ a - Q (φ a)) e) = W (φ a) e := by
      rw [h.comp, h.iso hφA (Submodule.smul_mem _ w hQb) hd, one_smul,
        show Q (φ a) + (φ a - Q (φ a)) = φ a by abel]
    have h2 : W (P (φ a)) (W (φ a - P (φ a) - Q (φ a)) e) = W (φ a - Q (φ a)) e := by
      rw [h.comp, ← map_smul P w (φ a), hPr, one_smul,
        show P (φ a) + (φ a - P (φ a) - Q (φ a)) = φ a - Q (φ a) by abel]
    rw [← h1, hl, ← h2, he _ hr]
  obtain ⟨k, f, hf, ht⟩ := exists_transversal_of_idx_ne_zero A (A.map φ) hidx

  have hE : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ e, Fixes W A e →
      ℓ (T e) = (lam (idx A (A.map φ)))⁻¹ * (((Finset.univ.filter (fun i => P (f i) ∈ A)).card : ℕ) : ℂ) * ℓ e := by
    intro ℓ hl e he
    rw [hTe e he]
    unfold normOp
    rw [(sumOp_eq_sum_transversal h A (A.map φ) hφA e he (Fin k) f hf ht).1, map_smul, map_sum,
      smul_eq_mul, mul_assoc]
    congr 1
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hterm ℓ hl e he (f i) (hf i)]
    by_cases hm : P (f i) ∈ A
    · simp [hm, he _ hm]
    · rw [invariantForm_translate_eq_zero h hPP hadj hA hQA ℓ hl he hm]
      simp [hm]

  have hmain : ∀ ℓ : M →ₗ[ℂ] ℂ, (∀ u m, ℓ (W (Q u) m) = ℓ m) → ∀ x e, Fixes W A e →
      ℓ (T (W x e)) = (lam (idx A (A.map φ)))⁻¹ * (((Finset.univ.filter (fun i => P (f i) ∈ A)).card : ℕ) : ℂ) * ℓ (W x e) := by
    intro ℓ hl x e he
    have hs0 := h.ne_zero (w • Q x) (x - Q x)
    have hA1 := hsplit ℓ hl x e
    have hB1 := hsplit ℓ hl (φ x) (T e)
    rw [hφr, ← hφQ, ← hφP, ← map_smul φ w (Q x), ← map_sub φ x (Q x), hφ, ← hT, ← hT] at hB1
    by_cases hp : P x ∈ A
    · rw [he _ hp] at hA1 hB1
      have h3 := hE (ℓ.comp (W (x - P x - Q x))) (hinvρ ℓ hl x) e he
      simp only [LinearMap.comp_apply] at h3
      rw [h3, ← hA1] at hB1
      apply mul_left_cancel₀ hs0
      rw [hB1]
      ring
    · have z1 := invariantForm_translate_eq_zero h hPP hadj hA hQA _ (hinvρ ℓ hl x) he hp
      have z2 := invariantForm_translate_eq_zero h hPP hadj hA hQA _ (hinvT _ (hinvρ ℓ hl x)) he hp
      simp only [LinearMap.comp_apply] at z1 z2
      rw [z1] at hA1
      rw [z2] at hB1
      rw [(mul_eq_zero.1 hA1).resolve_left hs0, (mul_eq_zero.1 hB1).resolve_left hs0, mul_zero]
  refine ⟨(Finset.univ.filter (fun i => P (f i) ∈ A)).card, ?_, ?_⟩
  · obtain ⟨i, hi, -⟩ := ht 0 (Submodule.zero_mem _)
    refine Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hPA _ ?_⟩⟩
    simpa using A.neg_mem hi
  · intro ℓ hl m
    have hle : (⊤ : Submodule ℂ M) ≤ LinearMap.ker (ℓ.comp T - ((lam (idx A (A.map φ)))⁻¹ * (((Finset.univ.filter (fun i => P (f i) ∈ A)).card : ℕ) : ℂ)) • ℓ) := by
      rw [← hspan, Submodule.span_le]
      rintro _ ⟨x, e, he, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [hmain ℓ hl x e he, sub_self]
    have hm := hle (Submodule.mem_top (x := m))
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      smul_eq_mul] at hm
    exact sub_eq_zero.1 hm
end GlobalTheory.FinWeil
