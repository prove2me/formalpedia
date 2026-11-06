-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.rectangular_block_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:43:42.765779+00:00
-- url     : https://prove2.me/submissions/5d121b56-fde9-4e1b-9c50-411fb07e6f5e

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Blocks
import Theorems.Thm_OAI_SevenEighths_CubicSieve_masked_energy_le
import Theorems.Thm_OAI_SevenEighths_CubicSieve_conjugateVector_apply
import Theorems.Thm_OAI_SevenEighths_CubicSieve_norm_conjugateVector
import Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_apply
import Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_conjugate_norm
attribute [local simp] OAI.SevenEighths.CubicSieve.conjugateVector_apply
attribute [local simp] OAI.SevenEighths.CubicSieve.norm_conjugateVector
attribute [local simp] OAI.SevenEighths.CubicSieve.operator_apply



set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq n]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef mask : n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ j, ‖mask j‖ ≤ 1) :
    (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
      min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  have hleft :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card b : ℝ) * squaredNorm A) * ∑ j, ‖coef j‖ ^ 2 := by
    calc
      _ ≤ ∑ k : b, squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have h := masked_energy_le A coef (fun j => star (B k j) * mask j) (by
          intro j
          rw [norm_mul, norm_star]
          exact (mul_le_mul_of_nonneg_right (hB k j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by simp [mul_assoc]
  have hright :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i : a, squaredNorm (fun k j => star (B k j)) * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := masked_energy_le (fun k j => star (B k j)) coef
          (fun j => A i j * mask j) (by
            intro j
            rw [norm_mul]
            exact (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by
        have hn : squaredNorm (fun k j => star (B k j)) = squaredNorm B := by
          unfold squaredNorm
          rw [operator_conjugate_norm]
        rw [hn]
        simp [mul_assoc]
  rcases le_total ((Fintype.card b : ℝ) * squaredNorm A)
      ((Fintype.card a : ℝ) * squaredNorm B) with h | h
  · rw [min_eq_left h]
    exact hleft
  · rw [min_eq_right h]
    exact hright
end OAI.SevenEighths.CubicSieve
