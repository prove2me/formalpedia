-- Prove2me | solution 1 for GlobalTheory.HopfShear.post_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:51:20.091802+00:00
-- url     : https://prove2.me/submissions/5ec3931b-2623-4103-83ae-c0b0e37affb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct WithConv
open GlobalTheory GlobalTheory.HopfShear
variable {R A B X Y : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R X] [Algebra R Y]
attribute [local instance] pointsGroup
namespace GlobalTheory.HopfShear
theorem _root_.solution (h : X →ₐ[R] Y) (x : WithConv (A →ₐ[R] X)) (a : A) :
    (post h x).ofConv a = h (x.ofConv a) := rfl
end GlobalTheory.HopfShear
