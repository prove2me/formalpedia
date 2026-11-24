-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ordInfty_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:14.253947+00:00
-- url     : https://prove2.me/submissions/329c7a30-04a9-4b41-9d4d-37a210333338

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_valuationInfty_algebraMap

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
theorem _root_.solution {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) :
    ordInfty W (algebraMap _ W.toAffine.FunctionField a) =
      -((Algebra.norm F[X] a).natDegree : ℤ) := by
  rw [ordInfty, valuationInfty_algebraMap, valuationInftyCoord_apply W ha, log_exp]
end GroundTheory.Arith.Abelian
