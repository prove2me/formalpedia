-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.valuation_genY_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:57:52.103737+00:00
-- url     : https://prove2.me/submissions/f9b946ab-de2d-46b7-b329-4c43b31dc2c9

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_valuation_poly_of_one_lt
import Theorems.Thm_GroundTheory_Arith_Abelian_valuation_poly_le_of_one_lt
import Theorems.Thm_GroundTheory_Arith_Abelian_genY_sq_add_weierstrassB
import Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_weierstrassRHS
import Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_weierstrassB_le
import Theorems.Thm_GroundTheory_Arith_Abelian_weierstrassRHS_ne_zero
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
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {k : ℤ} (hk0 : 0 < k)
    (hk : w (genX W) = exp k) : ∃ m : ℤ, w (genY W) = exp m ∧ 2 * m = 3 * k := by
  have hy0 : w (genY W) ≠ 0 := (Valuation.ne_zero_iff _).mpr (genY_ne_zero W)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, w (genY W) = exp m := ⟨_, (exp_log hy0).symm⟩
  refine ⟨m, hm, ?_⟩
  have hwQ : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassRHS W)) = exp (3 * k) := by
    rw [valuation_poly_of_one_lt w hF hk0 hk (weierstrassRHS_ne_zero W), natDegree_weierstrassRHS]
    norm_num
  have hwB : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W)) ≤ exp (1 * k) :=
    valuation_poly_le_of_one_lt w hF hk0 hk _ (natDegree_weierstrassB_le W)
  have hwy2 : w (genY W ^ 2) = exp (2 * m) := by
    rw [Valuation.map_pow, hm, ← exp_nsmul, nsmul_eq_mul]
    norm_num
  have hwBy : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W) ≤
      exp (k + m) := by
    rw [Valuation.map_mul, hm]
    calc _ ≤ exp (1 * k) * exp m := mul_le_mul_left hwB _
      _ = exp (k + m) := by rw [← exp_add, one_mul]
  have heq := congrArg w (genY_sq_add_weierstrassB W)
  rcases lt_or_ge k m with hkm | hmk
  · have hlt : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W) <
        w (genY W ^ 2) := by
      rw [hwy2]
      exact lt_of_le_of_lt hwBy (exp_lt_exp.mpr (by linarith))
    rw [Valuation.map_add_eq_of_lt_left _ hlt, hwy2, hwQ] at heq
    exact exp_inj.mp heq
  · exfalso
    have hle : w (genY W ^ 2 + algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) *
        genY W) ≤ exp (2 * k) :=
      w.map_add_le (by rw [hwy2, exp_le_exp]; linarith) (hwBy.trans (by rw [exp_le_exp]; linarith))
    rw [heq, hwQ, exp_le_exp] at hle
    linarith
end GroundTheory.Arith.Abelian
