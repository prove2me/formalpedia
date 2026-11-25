-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.natDegree_yPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:58.962127+00:00
-- url     : https://prove2.me/submissions/09d9b3bc-eb99-4edf-9ddf-97a2326fe8a3

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (x : F) : (yPoly E x).natDegree = 2 := by
  unfold yPoly; compute_degree!
end GroundTheory.Arith.Abelian
