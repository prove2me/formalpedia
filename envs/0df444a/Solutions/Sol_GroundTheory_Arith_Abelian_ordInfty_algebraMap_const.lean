-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ordInfty_algebraMap_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:21.462098+00:00
-- url     : https://prove2.me/submissions/e31a0ce0-22af-4475-8f61-46e5ef9a1bed

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_algebraMap
import Theorems.Thm_GroundTheory_Arith_Abelian_finrank_coordinateRing


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
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {c : F} (hc : c ≠ 0) :
    ordInfty W (algebraMap F W.toAffine.FunctionField c) = 0 := by
  have h : algebraMap F W.toAffine.FunctionField c =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap F[X] W.toAffine.CoordinateRing (C c)) := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F F[X] W.toAffine.FunctionField c,
      algebraMap_eq]
  have hc' : algebraMap F[X] W.toAffine.CoordinateRing (C c) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr (C_ne_zero.mpr hc)
  rw [h, ordInfty_algebraMap W hc', Algebra.norm_algebraMap, finrank_coordinateRing, ← C_pow,
    natDegree_C, Nat.cast_zero, neg_zero]
end GroundTheory.Arith.Abelian
