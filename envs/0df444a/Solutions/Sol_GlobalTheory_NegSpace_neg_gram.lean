-- Prove2me | solution 1 for GlobalTheory.NegSpace.neg_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:23.363707+00:00
-- url     : https://prove2.me/submissions/17ad37f3-3b55-417e-8f21-a42d45e34264

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
theorem _root_.solution (W : HSpace E) : (neg W).gram = -W.gram := rfl
end GlobalTheory.NegSpace
