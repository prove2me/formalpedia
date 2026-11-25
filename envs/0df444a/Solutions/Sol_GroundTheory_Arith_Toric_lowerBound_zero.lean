-- Prove2me | solution 1 for GroundTheory.Arith.Toric.lowerBound_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:40:32.317064+00:00
-- url     : https://prove2.me/submissions/cad53ed0-f32f-4105-8e8f-78229c41652a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Polynomial
variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] (φ : G →+ ℤ)
variable {φ}
namespace GroundTheory.Arith.Toric
theorem _root_.solution (a : ℤ) : LowerBound φ (0 : AddMonoidAlgebra k G) a := by
  intro m hm; simp at hm
end GroundTheory.Arith.Toric
