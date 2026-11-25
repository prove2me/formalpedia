-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ordInfty_X_div_Y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:30.558215+00:00
-- url     : https://prove2.me/submissions/94c667f8-75e3-4cb6-b409-9c39ebad57ce

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_div
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_X
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_Y
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
      (AdjoinRoot.mk W.toAffine.polynomial (C X)) /
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.mk W.toAffine.polynomial X)) = 1 := by
  have hne : ∀ f : W.toAffine.FunctionField, ordInfty W f ≠ 0 → f ≠ 0 := by
    rintro f hf rfl
    exact hf (by simp [ordInfty])
  rw [ordInfty_div W (hne _ (by rw [ordInfty_X]; norm_num)) (hne _ (by rw [ordInfty_Y]; norm_num)),
    ordInfty_X, ordInfty_Y]
  norm_num
end GroundTheory.Arith.Abelian
