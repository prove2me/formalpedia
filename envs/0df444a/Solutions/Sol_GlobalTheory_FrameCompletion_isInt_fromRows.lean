-- Prove2me | solution 1 for GlobalTheory.FrameCompletion.isInt_fromRows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:07:58.686235+00:00
-- url     : https://prove2.me/submissions/603f3b97-bb82-40f8-9edf-cb7c1a2fe82e

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
theorem _root_.solution {ι ι' κ : Type} {A : Matrix ι κ L} {B : Matrix ι' κ L} (hA : IsInt A) (hB : IsInt B) :
    IsInt (fromRows A B) := by
  rintro (i | i) j
  exacts [hA i j, hB i j]
end GlobalTheory.FrameCompletion
