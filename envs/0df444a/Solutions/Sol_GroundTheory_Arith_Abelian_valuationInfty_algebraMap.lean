-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.valuationInfty_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:01.023648+00:00
-- url     : https://prove2.me/submissions/aca9ceb2-733d-4653-a196-532d92e8d256

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd

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
theorem _root_.solution (a : W.toAffine.CoordinateRing) :
    valuationInfty W (algebraMap _ W.toAffine.FunctionField a) = valuationInftyCoord W a :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ a
end GroundTheory.Arith.Abelian
