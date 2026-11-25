-- Prove2me | solution 1 for GroundTheory.Arith.Toric.lowerBound_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:39:52.486263+00:00
-- url     : https://prove2.me/submissions/1810c9c3-25e2-4ac3-87fd-cb6a8f6d7e74

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
theorem _root_.solution : LowerBound φ (1 : AddMonoidAlgebra k G) 0 := by
  intro m hm
  have := support_coeff_one_subset hm
  simp only [Finset.mem_zero] at this
  rw [this, map_zero]
end GroundTheory.Arith.Toric
