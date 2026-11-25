-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.genY_sq_add_weierstrassB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:50:51.504236+00:00
-- url     : https://prove2.me/submissions/3f2c7e94-8652-4d48-aee3-07351221d42d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
import Theorems.Thm_GroundTheory_Arith_Abelian_algebraMap_C_functionField
import Theorems.Thm_GroundTheory_Arith_Abelian_genY_sq_add
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
namespace GroundTheory.Arith.Abelian
theorem _root_.solution :
    genY W ^ 2 + algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W =
      algebraMap F[X] W.toAffine.FunctionField (weierstrassRHS W) := by
  simp only [weierstrassB, weierstrassRHS, map_add, map_mul, map_pow,
    algebraMap_C_functionField, ← genX_eq]
  linear_combination genY_sq_add W
end GroundTheory.Arith.Abelian
