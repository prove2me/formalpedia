-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.isInt_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:10:58.995385+00:00
-- url     : https://prove2.me/submissions/b1305820-85b8-4055-bdf9-bcdf4f17a540

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
theorem _root_.solution {ι κ : Type} {M N : Matrix ι κ L} (hM : IsInt M) (hN : IsInt N) : IsInt (M - N) :=
  fun i j => sub_mem (hM i j) (hN i j)
end GlobalTheory.FrameCompletion
