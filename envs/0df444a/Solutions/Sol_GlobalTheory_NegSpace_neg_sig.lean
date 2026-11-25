-- Prove2me | solution 1 for GlobalTheory.NegSpace.neg_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:30.753841+00:00
-- url     : https://prove2.me/submissions/2c7a6db0-04ae-4162-8938-b2630bcaf51d

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_NegGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions NumberField
open GlobalTheory GlobalTheory.NegSpace
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace GlobalTheory.NegSpace
theorem _root_.solution (W : HSpace E) (τ : E →+* ℂ) : (neg W).sig τ = ((W.sig τ).2, (W.sig τ).1) := rfl
end GlobalTheory.NegSpace
