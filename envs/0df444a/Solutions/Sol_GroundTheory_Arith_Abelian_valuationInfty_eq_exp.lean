-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.valuationInfty_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:44:08.35145+00:00
-- url     : https://prove2.me/submissions/19dcf4c3-7b06-4633-9ed3-9608de5d2bfb

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_valuationInfty_ne_zero

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
theorem _root_.solution {f : W.toAffine.FunctionField} (hf : f ≠ 0) :
    valuationInfty W f = exp (-ordInfty W f) := by
  rw [ordInfty, neg_neg, exp_log (valuationInfty_ne_zero W hf)]
end GroundTheory.Arith.Abelian
