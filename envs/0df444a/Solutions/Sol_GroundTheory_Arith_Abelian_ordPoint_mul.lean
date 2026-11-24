-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.ordPoint_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:41.327403+00:00
-- url     : https://prove2.me/submissions/0dafd538-dac8-435f-9c75-5804b61aea4e

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_ordInfty_mul
import Theorems.Thm_GroundTheory_Arith_Abelian_ordAtIdeal_mul

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
variable [IsAlgClosed F] [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (P : W.toAffine.Point) {f g : W.toAffine.FunctionField} (hf : f ≠ 0)
    (hg : g ≠ 0) : ordPoint W P (f * g) = ordPoint W P f + ordPoint W P g := by
  cases P with
  | zero => exact ordInfty_mul W hf hg
  | some x y h => exact ordAtIdeal_mul W _ hf hg
end GroundTheory.Arith.Abelian
