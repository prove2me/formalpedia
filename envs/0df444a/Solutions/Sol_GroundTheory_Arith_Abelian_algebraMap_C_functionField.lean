-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.algebraMap_C_functionField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:02.714139+00:00
-- url     : https://prove2.me/submissions/73fc4897-e870-4cc7-90af-762edc4b1cd4

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsValuation

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
theorem _root_.solution (c : F) :
    algebraMap F[X] W.toAffine.FunctionField (C c) = algebraMap F W.toAffine.FunctionField c :=
  (IsScalarTower.algebraMap_apply F F[X] W.toAffine.FunctionField c).symm
end GroundTheory.Arith.Abelian
