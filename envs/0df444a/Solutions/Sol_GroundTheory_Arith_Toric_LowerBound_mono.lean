-- Prove2me | solution 1 for GroundTheory.Arith.Toric.LowerBound.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:38:47.255207+00:00
-- url     : https://prove2.me/submissions/510cd2fd-d808-4bcf-aca6-7249015fbae3

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
theorem _root_.solution {f : AddMonoidAlgebra k G} {a b : ℤ} (h : LowerBound φ f a) (hab : b ≤ a) :
    LowerBound φ f b :=
  fun m hm => hab.trans (h m hm)
end LowerBound
end GroundTheory.Arith.Toric
