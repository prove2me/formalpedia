-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.roots_toFinset_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:38:59.712846+00:00
-- url     : https://prove2.me/submissions/f8952f10-20e2-4abe-be19-8936644722ec

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
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [hp : Fact p.Prime] [CharP F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (q : F[X]) : (q ^ 2).roots.toFinset = q.roots.toFinset := by
  rw [roots_pow, Multiset.toFinset_nsmul _ _ two_ne_zero]
end GroundTheory.Arith.Abelian
