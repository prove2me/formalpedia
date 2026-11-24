-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.isInt_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:53:57.385477+00:00
-- url     : https://prove2.me/submissions/046a937c-75ab-4ac3-87fd-2d6b1afb0cc4

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
theorem _root_.solution {ι κ : Type} {M : Matrix ι κ L} (hM : IsInt M) : IsInt (-M) := fun i j => neg_mem (hM i j)
end GlobalTheory.FrameCompletion
