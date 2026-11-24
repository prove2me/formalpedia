-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.isInt_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:53:56.462937+00:00
-- url     : https://prove2.me/submissions/4cab5005-a2dd-4e53-a7d6-acfaeebfe272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
namespace GlobalTheory.FrameCompletion
theorem _root_.solution (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {ι κ : Type} {M : Matrix ι κ L} (hM : IsInt M) :
    IsInt (cT σ M) := fun i j => by
  show Valued.v (σ (M j i)) ≤ 1
  rw [hσ]
  exact hM j i
end GlobalTheory.FrameCompletion
