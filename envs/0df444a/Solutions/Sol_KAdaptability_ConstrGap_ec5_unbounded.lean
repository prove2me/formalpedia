-- Prove2me | solution 1 for KAdaptability.ConstrGap.ec5_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:03.973301+00:00
-- url     : https://prove2.me/submissions/23268e76-1b8e-49d8-8d61-e70fbe066856

import Mathlib
import Definitions.Def_KAdaptability_ConstrGap_Problem
import Definitions.Def_KAdaptability_ConstrGap_Values
import Definitions.Def_KAdaptability_ConstrGap_Instance

-- carved verbatim out of submission 1853fc7f-4dea-4504-960d-d58806e73b4a, lines 76-114

section
open Matrix
open KAdaptability.ConstrGap

theorem W_left (nQ : ℕ) (y : Fin nQ → ℝ) (q : Fin nQ) :
    (ec4W nQ *ᵥ y) (Fin.castAdd nQ q) = y q := by
  simp only [ec4W, mulVec, dotProduct, of_apply, Fin.addCases_left]
  simp

theorem W_right (nQ : ℕ) (y : Fin nQ → ℝ) (q : Fin nQ) :
    (ec4W nQ *ᵥ y) (Fin.natAdd nQ q) = -y q := by
  simp only [ec4W, mulVec, dotProduct, of_apply, Fin.addCases_right]
  simp

theorem H_left (nQ : ℕ) (ξ : Fin (nQ + 1) → ℝ) (q : Fin nQ) :
    (ec4H nQ *ᵥ ξ) (Fin.castAdd nQ q) = ξ (Fin.castSucc q) + 1 / 2 * ξ (Fin.last nQ) := by
  simp only [ec4H, mulVec, dotProduct, of_apply, Fin.addCases_left]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.castSucc_ne_last, (Fin.castSucc_lt_last q).ne', mul_comm]

theorem H_right (nQ : ℕ) (ξ : Fin (nQ + 1) → ℝ) (q : Fin nQ) :
    (ec4H nQ *ᵥ ξ) (Fin.natAdd nQ q) = -ξ (Fin.castSucc q) + 1 / 2 * ξ (Fin.last nQ) := by
  simp only [ec4H, mulVec, dotProduct, of_apply, Fin.addCases_right]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.castSucc_ne_last, (Fin.castSucc_lt_last q).ne', mul_comm]

theorem feas_iff (nQ : ℕ) (x : Fin 0 → ℝ) (y : Fin nQ → ℝ) (ξ : Fin (nQ + 1) → ℝ) :
    (inst nQ).T *ᵥ x + (inst nQ).W *ᵥ y ≤ (inst nQ).H *ᵥ ξ ↔
      ∀ q : Fin nQ, y q ≤ ξ (Fin.castSucc q) + 1 / 2 * ξ (Fin.last nQ) ∧
        -y q ≤ -ξ (Fin.castSucc q) + 1 / 2 * ξ (Fin.last nQ) := by
  show (0 : Matrix (Fin (nQ + nQ)) (Fin 0) ℝ) *ᵥ x + ec4W nQ *ᵥ y ≤ ec4H nQ *ᵥ ξ ↔ _
  rw [Matrix.zero_mulVec, zero_add, Pi.le_def]
  simp only [Fin.forall_fin_add, W_left, W_right, H_left, H_right]
  constructor
  · rintro ⟨h1, h2⟩ q; exact ⟨h1 q, h2 q⟩
  · intro h; exact ⟨fun q => (h q).1, fun q => (h q).2⟩

theorem solution (nQ K : ℕ) (hK : K < (inst nQ).Y.card) : (inst nQ).optPK K = ⊤ := by
  unfold Problem.optPK
  refine eq_top_iff.2 (le_iInf₂ fun x _ => le_iInf₂ fun ys hys => ?_)
  have hcard : (Finset.univ.image ys).card < (inst nQ).Y.card :=
    lt_of_le_of_lt (Finset.card_image_le.trans (by simp)) hK
  obtain ⟨y', hy'Y, hy'n⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hbin : ∀ j, y' j = 0 ∨ y' j = 1 := binaryCube_binary nQ y' hy'Y
  let ξ : Fin (nQ + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) y' 1
  have hξc : ∀ q, ξ (Fin.castSucc q) = y' q := fun q => by simp [ξ]
  have hξl : ξ (Fin.last nQ) = 1 := by simp [ξ]
  have hξ : ξ ∈ (inst nQ).Xi := by
    show ec4A nQ *ᵥ ξ ≤ ec4b nQ
    rw [ec4_Xi_iff, hξl, and_iff_left rfl]
    intro q; rw [hξc]; rcases hbin q with h | h <;> rw [h] <;> norm_num
  unfold Problem.objPK
  refine le_trans ?_ (le_iSup₂ (f := fun ξ (_ : ξ ∈ (inst nQ).Xi) =>
    (((ξ ⬝ᵥ ((inst nQ).C *ᵥ x) : ℝ) : EReal) +
    ⨅ k, ⨅ (_ : (inst nQ).T *ᵥ x + (inst nQ).W *ᵥ ys k ≤ (inst nQ).H *ᵥ ξ),
      ((ξ ⬝ᵥ ((inst nQ).Q *ᵥ ys k) : ℝ) : EReal))) ξ hξ)
  have hinner : (⨅ k, ⨅ (_ : (inst nQ).T *ᵥ x + (inst nQ).W *ᵥ ys k ≤ (inst nQ).H *ᵥ ξ),
      ((ξ ⬝ᵥ ((inst nQ).Q *ᵥ ys k) : ℝ) : EReal)) = ⊤ := by
    refine iInf_eq_top.2 fun k => iInf_eq_top.2 fun hf => ?_
    exfalso
    apply hy'n
    have hbk : ∀ j, ys k j = 0 ∨ ys k j = 1 := binaryCube_binary nQ (ys k) (hys k)
    have heq : ys k = y' := by
      funext q
      have h := (feas_iff nQ x (ys k) ξ).1 hf q
      rw [hξc, hξl] at h
      rcases hbk q with h1 | h1 <;> rcases hbin q with h2 | h2 <;> rw [h1, h2] at h ⊢ <;>
        norm_num at h
    rw [← heq]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  rw [hinner]
  simp

end
