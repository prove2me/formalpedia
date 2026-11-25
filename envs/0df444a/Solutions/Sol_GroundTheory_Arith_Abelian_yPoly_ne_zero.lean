-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.yPoly_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:49:09.921796+00:00
-- url     : https://prove2.me/submissions/9064bbb5-af1c-4edb-acbc-cc72d296ed0e

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_yPoly

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
theorem _root_.solution (x : F) : yPoly E x ≠ 0 := by
  intro h; have := natDegree_yPoly E x; rw [h, natDegree_zero] at this; exact absurd this (by norm_num)
end GroundTheory.Arith.Abelian
