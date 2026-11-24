-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ordInfty_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:44:10.061297+00:00
-- url     : https://prove2.me/submissions/317efcb0-9f18-47ac-aa09-b43a9b80d999

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
theorem _root_.solution {f g : W.toAffine.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    ordInfty W (f * g) = ordInfty W f + ordInfty W g := by
  rw [ordInfty, ordInfty, ordInfty, map_mul,
    log_mul (valuationInfty_ne_zero W hf) (valuationInfty_ne_zero W hg), neg_add]
end GroundTheory.Arith.Abelian
