-- Prove2me | solution 1 for GlobalTheory.compositeValuationSubring_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:03.25466+00:00
-- url     : https://prove2.me/submissions/fbd7379c-c4cf-44b1-a5ba-4b000ebe9b2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsValuationSubringLeDominatingOfFractionFiel
import Theorems.Thm_GlobalTheory_mem_compositeValuationSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {L : Type*} [Field L] (W : ValuationSubring L)
    (V : ValuationSubring (ResidueField W)) : compositeValuationSubring W V ≤ W :=
  fun x hx => ((mem_compositeValuationSubring W V x).1 hx).1
end GlobalTheory
