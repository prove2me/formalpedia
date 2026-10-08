-- Prove2me | solution 1 for MazurTransfer.order49_vertical_vertical_of_polynomial_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:22:35.640154+00:00
-- url     : https://prove2.me/submissions/5ddecca4-3901-44d3-9c07-887065d3f76e

import Mathlib
open Polynomial
namespace MazurTransfer.Order49GenericVerticalDerivativeHelpers
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/





open Polynomial

namespace MazurTorsion.Kubert.OrderSevenDoublingDerivative

















































private theorem vertical_of_common_denominator_derivative
    {A Ad B Bd H Hd Kh Khd Q Qd Ht Htd Nh R Rt K N : ℚ}
    (hA : A = B) (hAd : Ad = Bd)
    (hden : H * Kh ^ 2 = Q * Ht)
    (hdendot : Hd * Kh ^ 2 + 2 * H * Kh * Khd = Qd * Ht + Q * Htd)
    (hleft : Ad * H * Kh - A * (Hd * Kh + 2 * H * Khd) = 2 * Nh * R)
    (hright : Bd * Q * Ht - B * (Qd * Ht + Q * Htd) = 2 * Rt * K * N)
    (hKh : Kh = K * N) (hK : K ≠ 0) (hN : N ≠ 0) :
    Nh * R = Rt := by
  have hcommon :
      Kh * (Ad * H * Kh - A * (Hd * Kh + 2 * H * Khd)) =
        Bd * Q * Ht - B * (Qd * Ht + Q * Htd) := by
    linear_combination
      Ad * hden + (Q * Ht) * hAd - A * hdendot -
        (Qd * Ht + Q * Htd) * hA
  rw [hleft, hright, hKh] at hcommon
  have hcancel : (2 * K * N) * (Nh * R) = (2 * K * N) * Rt := by
    linear_combination hcommon
  exact mul_left_cancel₀
    (mul_ne_zero (mul_ne_zero (by norm_num) hK) hN) hcancel

private theorem vertical_of_polynomial_certificates
    (A B H Kh K N Q Ht : ℚ[X]) (x Nh R Rt : ℚ)
    (hA : A = B) (hKh : Kh = K * N) (hQ : Q = K ^ 2)
    (hHt : Ht = H * N ^ 2)
    (hK : K.eval x ≠ 0) (hN : N.eval x ≠ 0)
    (hleft :
      (derivative A).eval x * H.eval x * Kh.eval x - A.eval x *
          ((derivative H).eval x * Kh.eval x +
            2 * H.eval x * (derivative Kh).eval x) =
        2 * Nh * R)
    (hright :
      (derivative B).eval x * Q.eval x * Ht.eval x - B.eval x *
          ((derivative Q).eval x * Ht.eval x +
            Q.eval x * (derivative Ht).eval x) =
        2 * Rt * K.eval x * N.eval x) :
    Nh * R = Rt := by
  have hdenPoly : H * Kh ^ 2 = Q * Ht := by
    rw [hKh, hQ, hHt]
    ring
  have hAeval : A.eval x = B.eval x := by rw [hA]
  have hAderiv : (derivative A).eval x = (derivative B).eval x := by rw [hA]
  have hden : H.eval x * Kh.eval x ^ 2 = Q.eval x * Ht.eval x := by
    simpa using congrArg (Polynomial.eval x) hdenPoly
  have hdendot :
      (derivative H).eval x * Kh.eval x ^ 2 +
          2 * H.eval x * Kh.eval x * (derivative Kh).eval x =
        (derivative Q).eval x * Ht.eval x +
          Q.eval x * (derivative Ht).eval x := by
    have hd := congrArg Polynomial.derivative hdenPoly
    have hde := congrArg (Polynomial.eval x) hd
    simp [derivative_mul, derivative_pow] at hde
    linear_combination hde
  have hKheval : Kh.eval x = K.eval x * N.eval x := by
    simpa using congrArg (Polynomial.eval x) hKh
  exact MazurTransfer.Order49GenericVerticalDerivativeHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.vertical_of_common_denominator_derivative
    hAeval hAderiv hden hdendot hleft hright hKheval hK hN





























end MazurTorsion.Kubert.OrderSevenDoublingDerivative

end MazurTransfer.Order49GenericVerticalDerivativeHelpers

theorem solution (A B H Kh K N Q Ht : ℚ[X]) (x Nh R Rt : ℚ)
    (hA : A = B) (hKh : Kh = K * N) (hQ : Q = K ^ 2)
    (hHt : Ht = H * N ^ 2)
    (hK : K.eval x ≠ 0) (hN : N.eval x ≠ 0)
    (hleft :
      (derivative A).eval x * H.eval x * Kh.eval x - A.eval x *
          ((derivative H).eval x * Kh.eval x +
            2 * H.eval x * (derivative Kh).eval x) =
        2 * Nh * R)
    (hright :
      (derivative B).eval x * Q.eval x * Ht.eval x - B.eval x *
          ((derivative Q).eval x * Ht.eval x +
            Q.eval x * (derivative Ht).eval x) =
        2 * Rt * K.eval x * N.eval x) :
    Nh * R = Rt := by
  exact @MazurTransfer.Order49GenericVerticalDerivativeHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.vertical_of_polynomial_certificates A B H Kh K N Q Ht x Nh R Rt hA hKh hQ hHt hK hN hleft hright
#print axioms solution
