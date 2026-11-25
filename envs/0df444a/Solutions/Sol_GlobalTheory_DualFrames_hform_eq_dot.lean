-- Prove2me | solution 1 for GlobalTheory.DualFrames.hform_eq_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:06.291793+00:00
-- url     : https://prove2.me/submissions/9df342fc-53d9-469c-99a9-d4108cc03d63

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DualOfDualFrames

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.UG
open GlobalTheory GlobalTheory.DualFrames
variable {A : Type} [CommRing A] {k : ℕ}
namespace GlobalTheory.DualFrames
theorem _root_.solution (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A) (x y : Fin k → A) :
    hform τ J x y = (τ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
end GlobalTheory.DualFrames
