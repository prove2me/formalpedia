-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.natDegree_weierstrassRHS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:44:07.628857+00:00
-- url     : https://prove2.me/submissions/9eedab89-fb57-4f03-bf00-d14848b102d9

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
theorem _root_.solution : (weierstrassRHS W).natDegree = 3 := by
  unfold weierstrassRHS; compute_degree!
end GroundTheory.Arith.Abelian
