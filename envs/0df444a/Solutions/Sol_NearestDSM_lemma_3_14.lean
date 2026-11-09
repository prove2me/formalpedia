-- Prove2me | solution 1 for NearestDSM.lemma_3_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T14:25:17.59705+00:00
-- url     : https://prove2.me/submissions/87b53522-039b-494a-9683-9377ac8669a4

import Mathlib
import Definitions.Def_NearestDSM_equivClass
import Definitions.Def_NearestDSM_shiftVec

open Matrix

open NearestDSM in
theorem solution {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (y : Dual n) (R C : Set (Fin (n + 1)))
    (hR : Fin.last n ∉ R)
    (hblk : ∀ a b, (a ∈ R ∧ b ∉ C) ∨ (a ∉ R ∧ b ∈ C) → Xmat Xh y a b = 0) (t : ℝ) :
    y + t • shiftVec R C ∈ equivClass Xh y ↔
      (∀ a ∉ R, ∀ b ∈ C, Ymat Xh y a b ≤ t) ∧ (∀ a ∈ R, ∀ b ∉ C, t ≤ -Ymat Xh y a b) := by
  classical
  have hY : ∀ a b, Ymat Xh (y + t • shiftVec R C) a b = Ymat Xh y a b +
      t * ((Amat n)ᵀ *ᵥ WithLp.ofLp (shiftVec R C)) (a, b) := by
    intro a b
    simp only [Ymat, WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hlast : ∀ x : Fin n, ¬ (Fin.last n = Fin.castSucc x) := fun x h =>
    (Fin.castSucc_lt_last x).ne' h
  have hD : ∀ a b, ((Amat n)ᵀ *ᵥ WithLp.ofLp (shiftVec R C)) (a, b) =
      (if a ∈ R then 1 else 0) - (if b ∈ C then 1 else 0) := by
    intro a b
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_sum_type, Amat,
      Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, shiftVec, WithLp.ofLp_toLp]
    have h1 : ∑ x : Fin (n + 1), (if b = x then (1:ℝ) else 0) * (if x ∈ C then -1 else 0) =
        -(if b ∈ C then 1 else 0) := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      split_ifs <;> simp
    have h2 : ∑ x : Fin n, (if a = Fin.castSucc x then (1:ℝ) else 0) *
        (if Fin.castSucc x ∈ R then 1 else 0) = (if a ∈ R then 1 else 0) := by
      rcases Fin.eq_castSucc_or_eq_last a with ⟨r0, rfl⟩ | rfl
      · simp only [Fin.castSucc_inj, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      · simp only [hlast, if_false, zero_mul, Finset.sum_const_zero, hR]
    rw [h1, h2]
    ring
  have hX : ∀ y' a b, Xmat Xh y' a b = max (Ymat Xh y' a b) 0 := fun _ _ _ => rfl
  simp only [equivClass, Set.mem_setOf_eq]
  constructor
  · intro heq
    have hpt : ∀ a b, Xmat Xh (y + t • shiftVec R C) a b = Xmat Xh y a b := fun a b => by
      rw [heq]
    refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_⟩
    · have h0 := hblk a b (Or.inr ⟨ha, hb⟩)
      have := hpt a b
      rw [h0, hX, hY, hD] at this
      simp only [ha, hb, if_false, if_true] at this
      have := le_of_eq this
      rw [max_le_iff] at this
      linarith [this.1]
    · have h0 := hblk a b (Or.inl ⟨ha, hb⟩)
      have := hpt a b
      rw [h0, hX, hY, hD] at this
      simp only [ha, hb, if_false, if_true] at this
      have := le_of_eq this
      rw [max_le_iff] at this
      linarith [this.1]
  · rintro ⟨h1, h2⟩
    funext a b
    rw [hX, hX, hY, hD]
    by_cases ha : a ∈ R <;> by_cases hb : b ∈ C
    · simp only [ha, hb, if_true, sub_self, mul_zero, add_zero]
    · have h0 := hblk a b (Or.inl ⟨ha, hb⟩)
      rw [hX] at h0
      have hy0 : Ymat Xh y a b ≤ 0 := by
        have := le_of_eq h0; rw [max_le_iff] at this; exact this.1
      have := h2 a ha b hb
      simp only [ha, hb, if_true, if_false, sub_zero, mul_one]
      rw [h0, max_eq_right (by linarith)]
    · have h0 := hblk a b (Or.inr ⟨ha, hb⟩)
      rw [hX] at h0
      have hy0 : Ymat Xh y a b ≤ 0 := by
        have := le_of_eq h0; rw [max_le_iff] at this; exact this.1
      have := h1 a ha b hb
      simp only [ha, hb, if_true, if_false, zero_sub, mul_neg, mul_one]
      rw [h0, max_eq_right (by linarith)]
    · simp only [ha, hb, if_false, sub_self, mul_zero, add_zero]
