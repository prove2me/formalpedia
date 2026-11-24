-- Prove2me | solution 1 for GlobalTheory.CubeLift.del_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:31.6831+00:00
-- url     : https://prove2.me/submissions/2f9557ae-1433-453c-b53a-221b80e498f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
namespace GlobalTheory.CubeLift
theorem _root_.solution (g g' : (A[X])ˣ) (a b c : X →+ Y) : del (g * g') a b c = del g a b c * del g' a b c := by
  apply Additive.ofMul.injective
  simp only [del, map_mul, ofMul_mul, ofMul_div]
  abel
end GlobalTheory.CubeLift
