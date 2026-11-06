-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.extracted_coefficients_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:25.534203+00:00
-- url     : https://prove2.me/submissions/05012bbf-52f6-4ceb-8a2a-7536e83a2283

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Algebra
import Theorems.Thm_OAI_SevenEighths_CubicSieve_cubic_norm_le_one

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite Rˣ]
omit [Finite Rˣ]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution {ι : Type*}
    (S : Finset ι) (coef : ι → ℂ) (χ : ι → MulChar R ℂ)
    (hχ : ∀ n ∈ S, χ n ^ 3 = 1) (b c : ι → R) :
    (∑ n ∈ S, ‖coef n * star (χ n (b n)) *
      (if IsUnit (c n) then (1 : ℂ) else 0)‖ ^ 2) ≤
      ∑ n ∈ S, ‖coef n‖ ^ 2 := by
  classical
  apply Finset.sum_le_sum
  intro n hn
  by_cases hc : IsUnit (c n)
  · simp only [if_pos hc, mul_one, norm_mul, norm_star]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_right (norm_nonneg _) (cubic_norm_le_one (χ n) (hχ n hn) _)
  · simp only [if_neg hc, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
end OAI.SevenEighths.CubicSieve
