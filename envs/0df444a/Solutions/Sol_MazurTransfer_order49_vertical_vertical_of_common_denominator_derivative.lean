-- Prove2me | solution 1 for MazurTransfer.order49_vertical_vertical_of_common_denominator_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T04:22:27.745748+00:00
-- url     : https://prove2.me/submissions/993f9118-2cce-4412-8e8f-fadaafe97536

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































end MazurTorsion.Kubert.OrderSevenDoublingDerivative

end MazurTransfer.Order49GenericVerticalDerivativeHelpers

theorem solution {A Ad B Bd H Hd Kh Khd Q Qd Ht Htd Nh R Rt K N : ℚ}
    (hA : A = B) (hAd : Ad = Bd)
    (hden : H * Kh ^ 2 = Q * Ht)
    (hdendot : Hd * Kh ^ 2 + 2 * H * Kh * Khd = Qd * Ht + Q * Htd)
    (hleft : Ad * H * Kh - A * (Hd * Kh + 2 * H * Khd) = 2 * Nh * R)
    (hright : Bd * Q * Ht - B * (Qd * Ht + Q * Htd) = 2 * Rt * K * N)
    (hKh : Kh = K * N) (hK : K ≠ 0) (hN : N ≠ 0) :
    Nh * R = Rt := by
  exact @MazurTransfer.Order49GenericVerticalDerivativeHelpers.MazurTorsion.Kubert.OrderSevenDoublingDerivative.vertical_of_common_denominator_derivative A Ad B Bd H Hd Kh Khd Q Qd Ht Htd Nh R Rt K N hA hAd hden hdendot hleft hright hKh hK hN
#print axioms solution
