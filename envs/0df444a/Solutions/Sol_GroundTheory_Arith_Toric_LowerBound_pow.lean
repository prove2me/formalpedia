-- Prove2me | solution 1 for GroundTheory.Arith.Toric.LowerBound.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:05.72099+00:00
-- url     : https://prove2.me/submissions/84c4d727-3565-4503-84e4-da07d1a43f6d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Affine
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_GroundTheory_Arith_Toric_lowerBound_one

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
namespace LowerBound
theorem _root_.solution {f : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a) (n : ℕ) :
    LowerBound φ (f ^ n) (n * a) := by
  induction n with
  | zero => simpa using lowerBound_one
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hf
    convert this using 1
    push_cast; ring
end LowerBound
end GroundTheory.Arith.Toric
