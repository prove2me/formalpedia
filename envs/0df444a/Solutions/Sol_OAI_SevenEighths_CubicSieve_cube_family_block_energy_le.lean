-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.cube_family_block_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:03.578573+00:00
-- url     : https://prove2.me/submissions/7f0e2dd2-eca1-45af-a5ff-01674eca8e98

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Blocks
import Theorems.Thm_OAI_SevenEighths_CubicSieve_rectangular_block_energy_le
import Theorems.Thm_OAI_SevenEighths_CubicSieve_conjugateVector_apply
import Theorems.Thm_OAI_SevenEighths_CubicSieve_norm_conjugateVector
import Theorems.Thm_OAI_SevenEighths_CubicSieve_operator_apply
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
theorem _root_.solution {c : Type*} [Fintype c]
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef : n → ℂ) (mask : c → n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ l j, ‖mask l j‖ ≤ 1) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask l j‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm A)
          ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  calc
    _ ≤ ∑ l : c, min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro l _
      exact rectangular_block_energy_le A B coef (mask l) hA hB (hmask l)
    _ = _ := by simp [mul_assoc]
end OAI.SevenEighths.CubicSieve
