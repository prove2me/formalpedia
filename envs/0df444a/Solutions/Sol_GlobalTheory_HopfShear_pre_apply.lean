-- Prove2me | solution 1 for GlobalTheory.HopfShear.pre_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:24.764535+00:00
-- url     : https://prove2.me/submissions/610e7cf4-1b59-4401-aeb3-886356c6ce66

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
theorem _root_.solution (f : B →ₐc[R] A) (x : WithConv (A →ₐ[R] X)) (b : B) :
    (pre f x).ofConv b = x.ofConv (f b) := rfl
end GlobalTheory.HopfShear
