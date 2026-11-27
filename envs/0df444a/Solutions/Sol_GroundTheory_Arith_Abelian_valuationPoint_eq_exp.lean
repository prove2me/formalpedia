-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.valuationPoint_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:24.519973+00:00
-- url     : https://prove2.me/submissions/57a7772d-53a5-4313-b132-f05d9a0466af

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsOrd
import Theorems.Thm_GroundTheory_Arith_Abelian_valuationInfty_eq_exp
import Theorems.Thm_GroundTheory_Arith_Abelian_valuation_eq_exp_neg_ordAtIdeal

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
theorem _root_.solution (P : W.toAffine.Point) {f : W.toAffine.FunctionField}
    (hf : f ≠ 0) : valuationPoint W P f = exp (-ordPoint W P f) := by
  cases P with
  | zero => exact valuationInfty_eq_exp W hf
  | some x y h => exact valuation_eq_exp_neg_ordAtIdeal W _ hf
end GroundTheory.Arith.Abelian
