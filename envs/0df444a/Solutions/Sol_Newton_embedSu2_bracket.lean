-- Prove2me | solution 1 for Newton.embedSu2_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:56:26.589962+00:00
-- url     : https://prove2.me/submissions/7a7a6679-9bf9-4715-a7e0-69429e83008e

import Definitions.Def_Newton_Gauge_LieAlgebra
import Definitions.Def_Newton_Gauge_GellMannMatrices
import Theorems.Thm_Newton_SuNAlgebra_lie_def
import Theorems.Thm_Newton_SuNAlgebra_lie_matrix
attribute [local simp] Newton.SuNAlgebra.lie_matrix



set_option autoImplicit false
open Matrix
open Newton
namespace Newton
theorem _root_.solution (A B : SuNAlgebra 2) (N : ℕ) :
    ⁅embedSu2 A N, embedSu2 B N⁆ = embedSu2 ⁅A, B⁆ N := by
  apply SuNAlgebra.ext
  simp only [SuNAlgebra.lie_def, embedSu2]
  ext i j
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [embedMatrix2]
  by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
  · -- i < 2, j < 2
    simp only [hi, hj, dite_true]
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    -- Compute the components of the matrix product
    have h0_lt : (0 : Fin (N + 2)).val < 2 := Nat.zero_lt_two
    have h1_lt : (1 : Fin (N + 2)).val < 2 := Nat.one_lt_two
    have h_sum_AB : ∑ k : Fin (N + 2),
        (if hk : k.val < 2 then A.matrix ⟨i.val, hi⟩ ⟨k.val, hk⟩ else 0) *
        (if hk : k.val < 2 then B.matrix ⟨k.val, hk⟩ ⟨j.val, hj⟩ else 0) =
        ∑ k : Fin 2, A.matrix ⟨i.val, hi⟩ k * B.matrix k ⟨j.val, hj⟩ := by
      -- Extract only the k = 0, 1 terms
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (N + 2))), ← Finset.sdiff_singleton_eq_erase]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp⟩ :
          (1 : Fin (N + 2)) ∈ Finset.univ \ {0}), ← Finset.sdiff_singleton_eq_erase]
      simp only [h0_lt, h1_lt, dite_true]
      -- The remaining sum is 0
      have hrest : ∑ k ∈ (Finset.univ \ {0}) \ {(1 : Fin (N + 2))},
          (if hk : k.val < 2 then A.matrix ⟨i.val, hi⟩ ⟨k.val, hk⟩ else 0) *
          (if hk : k.val < 2 then B.matrix ⟨k.val, hk⟩ ⟨j.val, hj⟩ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hk
        have hne0 : k ≠ 0 := hk.1
        have hne1 : k ≠ 1 := hk.2
        have hnotlt : ¬k.val < 2 := by
          by_contra hlt
          have hval : k.val = 0 ∨ k.val = 1 := by omega
          rcases hval with hv0 | hv1
          · exact hne0 (Fin.ext hv0)
          · exact hne1 (Fin.ext hv1)
        simp [hnotlt]
      rw [hrest, add_zero]
      rw [Fin.sum_univ_two]
      -- ⟨0, h0_lt⟩ = 0 and ⟨1, h1_lt⟩ = 1
      have h0eq : (⟨(0 : Fin (N + 2)).val, h0_lt⟩ : Fin 2) = 0 := Fin.ext rfl
      have h1eq : (⟨(1 : Fin (N + 2)).val, h1_lt⟩ : Fin 2) = 1 := Fin.ext rfl
      simp only [h0eq, h1eq]
    have h_sum_BA : ∑ k : Fin (N + 2),
        (if hk : k.val < 2 then B.matrix ⟨i.val, hi⟩ ⟨k.val, hk⟩ else 0) *
        (if hk : k.val < 2 then A.matrix ⟨k.val, hk⟩ ⟨j.val, hj⟩ else 0) =
        ∑ k : Fin 2, B.matrix ⟨i.val, hi⟩ k * A.matrix k ⟨j.val, hj⟩ := by
      -- Extract only the k = 0, 1 terms
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (N + 2))), ← Finset.sdiff_singleton_eq_erase]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp⟩ :
          (1 : Fin (N + 2)) ∈ Finset.univ \ {0}), ← Finset.sdiff_singleton_eq_erase]
      simp only [h0_lt, h1_lt, dite_true]
      -- The remaining sum is 0
      have hrest : ∑ k ∈ (Finset.univ \ {0}) \ {(1 : Fin (N + 2))},
          (if hk : k.val < 2 then B.matrix ⟨i.val, hi⟩ ⟨k.val, hk⟩ else 0) *
          (if hk : k.val < 2 then A.matrix ⟨k.val, hk⟩ ⟨j.val, hj⟩ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hk
        have hne0 : k ≠ 0 := hk.1
        have hne1 : k ≠ 1 := hk.2
        have hnotlt : ¬k.val < 2 := by
          by_contra hlt
          have hval : k.val = 0 ∨ k.val = 1 := by omega
          rcases hval with hv0 | hv1
          · exact hne0 (Fin.ext hv0)
          · exact hne1 (Fin.ext hv1)
        simp [hnotlt]
      rw [hrest, add_zero]
      rw [Fin.sum_univ_two]
      -- ⟨0, h0_lt⟩ = 0 and ⟨1, h1_lt⟩ = 1
      have h0eq : (⟨(0 : Fin (N + 2)).val, h0_lt⟩ : Fin 2) = 0 := Fin.ext rfl
      have h1eq : (⟨(1 : Fin (N + 2)).val, h1_lt⟩ : Fin 2) = 1 := Fin.ext rfl
      simp only [h0eq, h1eq]
    rw [h_sum_AB, h_sum_BA]
  · -- i < 2, j ≥ 2
    simp [hi, hj]
  · -- i ≥ 2, j < 2
    simp [hi, hj]
  · -- i ≥ 2, j ≥ 2
    simp [hi, hj]
end Newton
