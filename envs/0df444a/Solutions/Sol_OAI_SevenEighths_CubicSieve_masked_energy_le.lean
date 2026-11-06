-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.masked_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:48.352246+00:00
-- url     : https://prove2.me/submissions/d3fc7318-3467-4627-b85e-3a2e31ed1757

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Blocks
import Theorems.Thm_OAI_SevenEighths_CubicSieve_squaredNorm_nonneg
import Theorems.Thm_OAI_SevenEighths_CubicSieve_energy_le_squaredNorm


set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq n]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (A : Matrix a n ℂ) (coef phase : n → ℂ)
    (hphase : ∀ j, ‖phase j‖ ≤ 1) :
    (∑ i, ‖∑ j, A i j * (coef j * phase j)‖ ^ 2) ≤
      squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
  apply (energy_le_squaredNorm A (fun j => coef j * phase j)).trans
  apply mul_le_mul_of_nonneg_left _ (squaredNorm_nonneg A)
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_of_le_one_right (norm_nonneg _) (hphase j)
end OAI.SevenEighths.CubicSieve
