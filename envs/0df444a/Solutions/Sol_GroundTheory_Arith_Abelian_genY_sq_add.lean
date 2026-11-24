-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.genY_sq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:20.046728+00:00
-- url     : https://prove2.me/submissions/b6a48600-f2f2-4536-aa37-34aae0a378d8

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation
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
theorem _root_.solution : genY W ^ 2 + algebraMap F W.toAffine.FunctionField W.a₁ * genX W * genY W +
    algebraMap F W.toAffine.FunctionField W.a₃ * genY W = genX W ^ 3 +
      algebraMap F W.toAffine.FunctionField W.a₂ * genX W ^ 2 +
      algebraMap F W.toAffine.FunctionField W.a₄ * genX W +
      algebraMap F W.toAffine.FunctionField W.a₆ := by
  have e := (equation_iff _ _).mp (equation_gen W)
  simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using e
end GroundTheory.Arith.Abelian
