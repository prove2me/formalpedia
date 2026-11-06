-- Prove2me | solution 1 for OAI.SharpPlanar.fejer_cheb_integral_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:40:56.91477+00:00
-- url     : https://prove2.me/submissions/21d0af37-73ef-456b-8f0c-664f1722fc92

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_cheb_integral_e
import Theorems.Thm_OAI_SharpPlanar_fejer_integral_even_e
import Theorems.Thm_OAI_SharpPlanar_fejer_integral_odd_e
import Theorems.Thm_OAI_SharpPlanar_fejer_integral_zero_e

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

lemma fejer_cheb_integral_e_oai (n : ℕ) (hn : n < 256) :
    (∫ x, fejerPolynomial.eval x*(T ℝ n).eval x ∂measureT) =
      (Real.pi/2)*(∫ x in (-1:ℝ)..1, (T ℝ n).eval x) := by
  rw [cheb_integral_e]
  rcases Nat.even_or_odd n with ⟨k,hk⟩ | ⟨k,hk⟩
  · have he : n=2*k := by omega
    rw [he] at hn ⊢
    by_cases hk₀ : k=0
    · subst k
      simpa only [Nat.mul_zero, Nat.cast_zero, pow_zero, add_self_div_two,
        zero_pow (by norm_num : 2 ≠ 0), sub_zero, div_one, one_add_one_eq_two,
        div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using fejer_integral_zero_e
    · rw [show ((2*k:ℕ):ℤ)=2*(k:ℤ) by push_cast; rfl,
        fejer_integral_even_e k (by simp only [Finset.mem_Icc]; omega)]
      simp only [pow_mul, neg_one_sq, one_pow, Nat.cast_mul, Nat.cast_ofNat]
      ring
  · subst n
    rw [show ((2*k+1:ℕ):ℤ)=2*(k:ℤ)+1 by push_cast; rfl, fejer_integral_odd_e]
    simp [pow_add, pow_mul]

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fejer_cheb_integral_e_oai := @OAI.SharpPlanar.fejer_cheb_integral_e_oai
