-- Prove2me | solution 1 for OAI.SharpPlanar.cheb_primitive_deriv_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:05:49.298889+00:00
-- url     : https://prove2.me/submissions/82b0b9fd-7824-4326-8be2-e17f84335594

import Mathlib

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

lemma cheb_primitive_deriv_g_oai (n : ℤ) (hn₁ : n+1 ≠ 0) (hn₂ : n-1 ≠ 0) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (T ℝ (n+1)).eval x/(2*(n+1:ℤ))-
      (T ℝ (n-1)).eval x/(2*(n-1:ℤ))) ((T ℝ n).eval x) x := by
  have h := ((T ℝ (n+1)).hasDerivAt x).div_const (2*(n+1:ℤ) : ℝ)
  have h' := ((T ℝ (n-1)).hasDerivAt x).div_const (2*(n-1:ℤ) : ℝ)
  convert h.sub h' using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  rw [T_derivative_eq_U, T_derivative_eq_U]
  simp only [eval_mul, eval_intCast]
  have hu := congrArg (fun p : ℝ[X] => p.eval x) (two_mul_T_eq_U_sub_U ℝ (n-2))
  simp only [sub_add_cancel, eval_mul, eval_sub, eval_ofNat] at hu
  have hn₁' : (n+1:ℝ) ≠ 0 := by exact_mod_cast hn₁
  have hn₂' : (n-1:ℝ) ≠ 0 := by exact_mod_cast hn₂
  push_cast
  simp only [show n+1-1=n by omega, show n-1-1=n-2 by omega]
  field_simp
  nlinarith [hu]

end SharpPlanar



open MeasureTheory Set
open scoped BigOperators


end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.cheb_primitive_deriv_g_oai := @OAI.SharpPlanar.cheb_primitive_deriv_g_oai
