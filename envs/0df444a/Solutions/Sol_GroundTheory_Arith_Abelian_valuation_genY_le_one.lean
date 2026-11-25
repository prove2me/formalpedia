-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.valuation_genY_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:57:51.490709+00:00
-- url     : https://prove2.me/submissions/c9a773d7-bdc4-4c15-a234-780e102d6bb7

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_valuation_poly_le_one
import Theorems.Thm_GroundTheory_Arith_Abelian_genY_sq_add_weierstrassB
import Theorems.Thm_GroundTheory_Arith_Abelian_genY_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)
variable {W}
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) : w (genY W) ≤ 1 := by
  by_contra hy
  have hy0 : w (genY W) ≠ 0 := (Valuation.ne_zero_iff _).mpr (genY_ne_zero W)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, w (genY W) = exp m := ⟨_, (exp_log hy0).symm⟩
  rw [not_le, hm, ← exp_zero, exp_lt_exp] at hy
  have hwB := valuation_poly_le_one w hF hx (weierstrassB W)
  have hwQ := valuation_poly_le_one w hF hx (weierstrassRHS W)
  have hwy2 : w (genY W ^ 2) = exp (2 * m) := by
    rw [Valuation.map_pow, hm, ← exp_nsmul, nsmul_eq_mul]
    norm_num
  have hlt : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W) <
      w (genY W ^ 2) := by
    rw [Valuation.map_mul, hm, hwy2]
    calc _ ≤ 1 * exp m := mul_le_mul_left hwB _
      _ < exp (2 * m) := by rw [one_mul, exp_lt_exp]; linarith
  have heq := congrArg w (genY_sq_add_weierstrassB W)
  rw [Valuation.map_add_eq_of_lt_left _ hlt, hwy2] at heq
  rw [← heq, ← exp_zero, exp_le_exp] at hwQ
  linarith
end GroundTheory.Arith.Abelian
