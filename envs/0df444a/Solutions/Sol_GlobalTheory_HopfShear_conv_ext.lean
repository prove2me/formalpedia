-- Prove2me | solution 1 for GlobalTheory.HopfShear.conv_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:24.087309+00:00
-- url     : https://prove2.me/submissions/3120ae62-e7e7-4670-8bca-2a0ca30d788d

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
theorem _root_.solution {x y : WithConv (A →ₐ[R] X)} (h : ∀ a, x.ofConv a = y.ofConv a) : x = y :=
  ofConv_injective (AlgHom.ext h)
end GlobalTheory.HopfShear
