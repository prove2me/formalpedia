-- Prove2me | solution 1 for GroundTheory.Arith.Toric.LowerBound.coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:35.159797+00:00
-- url     : https://prove2.me/submissions/372ec090-0f8a-4bb7-b5cf-38a5484a14b8

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
namespace LowerBound
theorem _root_.solution {f : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a)
    {m : G} (hm : φ m < a) : f.coeff m = 0 := by
  by_contra h
  exact absurd (hf m (Finsupp.mem_support_iff.2 h)) (not_le.2 hm)
end LowerBound
end GroundTheory.Arith.Toric
