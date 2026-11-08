-- Prove2me | solution 1 for OAI.SharpPlanar.cheb_integral_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:05:45.116208+00:00
-- url     : https://prove2.me/submissions/99f6d424-4e9f-405f-8794-3f1ebf71ef9e

import Mathlib
import Theorems.Thm_OAI_SharpPlanar_cheb_primitive_deriv_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Quadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Real Polynomial Finset MeasureTheory
open Polynomial.Chebyshev

namespace SharpPlanar

lemma cheb_integral_g_oai (n : ℕ) :
    (∫ x in (-1:ℝ)..1, (T ℝ n).eval x) =
    (1+(-1:ℝ)^n)/(1-(n:ℝ)^2) := by
  by_cases hn : n=1
  · subst n
    norm_num [integral_id]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => cheb_primitive_deriv_g (n:ℤ) (by omega) (by omega) x)
    ((T ℝ (n:ℤ)).continuous.intervalIntegrable (-1) 1)
  rw [h, T_eval_one, T_eval_one, T_eval_neg_one, T_eval_neg_one]
  have hp : ((n:ℤ)+1).negOnePow = -(n:ℤ).negOnePow := by simp [Int.negOnePow_add]
  have hm : ((n:ℤ)-1).negOnePow = -(n:ℤ).negOnePow := by simp [Int.negOnePow_sub]
  rw [hp, hm]
  simp only [Units.val_neg, Int.cast_neg]
  have hnat : (((n:ℤ).negOnePow : ℤ) : ℝ) = (-1:ℝ)^n := by
    rw [Int.cast_negOnePow]
    simp
  rw [hnat]
  push_cast
  have hn₁ : (n:ℝ)+1 ≠ 0 := by positivity
  have hn₂ : (n:ℝ)-1 ≠ 0 := by exact_mod_cast (by omega : (n:ℤ)-1 ≠ 0)
  have hn₃ : 1-(n:ℝ)^2 ≠ 0 := by
    intro hzero
    have : (n:ℝ)=1 := by have := Nat.cast_nonneg (α:=ℝ) n; nlinarith
    exact hn (by exact_mod_cast this)
  field_simp
  ring

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.cheb_integral_g_oai := @OAI.SharpPlanar.cheb_integral_g_oai
