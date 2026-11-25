-- Prove2me | solution 1 for GlobalTheory.DualFrames.exists_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:03.913304+00:00
-- url     : https://prove2.me/submissions/e9259652-4e38-4726-a0bb-4384bab22666

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
theorem _root_.solution (B : GL (Fin k) A) (y : Fin k → A) :
    ∃ z, (B : Matrix (Fin k) (Fin k) A) *ᵥ z = y := by
  refine ⟨((B⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) *ᵥ y, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
end GlobalTheory.DualFrames
