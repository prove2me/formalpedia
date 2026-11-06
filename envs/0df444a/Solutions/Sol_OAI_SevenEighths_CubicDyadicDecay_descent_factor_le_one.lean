-- Prove2me | solution 1 for OAI.SevenEighths.CubicDyadicDecay.descent_factor_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:00:37.685181+00:00
-- url     : https://prove2.me/submissions/ff53bcac-be34-41b3-897e-45a8944eed42

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicDyadicDecay

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.CubicDyadicDecay
theorem _root_.solution (e d u v : ℝ) (he : 1 ≤ e) (hed : e ≤ d)
    (hv : v ≤ 0) (huv : u+v ≤ 0) : e^u*d^v ≤ 1 := by
  have hd : 1 ≤ d := he.trans hed
  by_cases hu : 0 ≤ u
  · calc
      _ ≤ d^u*d^v := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by linarith) hed hu) (by positivity)
      _ = d^(u+v) := (Real.rpow_add (by linarith : 0 < d) u v).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hd huv
  · exact (mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos he (le_of_not_ge hu))
      (Real.rpow_le_one_of_one_le_of_nonpos hd hv) (by positivity) (by norm_num)).trans_eq
      (one_mul 1)
end OAI.SevenEighths.CubicDyadicDecay
