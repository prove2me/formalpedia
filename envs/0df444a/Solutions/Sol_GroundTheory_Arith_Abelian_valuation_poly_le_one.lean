-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.valuation_poly_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:55:32.440823+00:00
-- url     : https://prove2.me/submissions/733bf394-7adc-4bbd-87f5-611be640ca17

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_algebraMap_C_functionField
import Theorems.Thm_GroundTheory_Arith_Abelian_genX_eq
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



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
    (hx : w (genX W) ≤ 1) (p : F[X]) : w (algebraMap F[X] W.toAffine.FunctionField p) ≤ 1 := by
  induction p using Polynomial.induction_on with
  | C c =>
    rw [algebraMap_C_functionField]
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · exact (hF c hc).le
  | add p q hp hq => rw [map_add]; exact w.map_add_le hp hq
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, ← genX_eq]
    exact mul_le_one' ih hx
end GroundTheory.Arith.Abelian
