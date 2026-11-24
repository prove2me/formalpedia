-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ordInfty_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:38.961525+00:00
-- url     : https://prove2.me/submissions/faa0c613-b321-498e-8cac-05f685ce342d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_algebraMap
import Theorems.Thm_GroundTheory_Arith_Abelian_finrank_coordinateRing
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
    ordInfty W (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (AdjoinRoot.mk W.toAffine.polynomial (C X))) = -2 := by
  have hx : AdjoinRoot.mk W.toAffine.polynomial (C X) =
      algebraMap F[X] W.toAffine.CoordinateRing X := by
    simp only [AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  have h0 : algebraMap F[X] W.toAffine.CoordinateRing X ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr X_ne_zero
  rw [hx, ordInfty_algebraMap W h0, Algebra.norm_algebraMap, finrank_coordinateRing,
    natDegree_X_pow]
  norm_num
end GroundTheory.Arith.Abelian
