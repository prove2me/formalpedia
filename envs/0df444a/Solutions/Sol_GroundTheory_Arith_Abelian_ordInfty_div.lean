-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ordInfty_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:34.633584+00:00
-- url     : https://prove2.me/submissions/b718888d-7b95-45d0-a1fc-53bd4b29beec

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_mul
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_inv

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
    ordInfty W (f / g) = ordInfty W f - ordInfty W g := by
  rw [div_eq_mul_inv, ordInfty_mul W hf (inv_ne_zero hg), ordInfty_inv, sub_eq_add_neg]
end GroundTheory.Arith.Abelian
