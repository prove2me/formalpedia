-- Prove2me | solution 1 for GlobalTheory.T.infinitePlace_completion_nhdsNE_zero_neBot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:14:56.220081+00:00
-- url     : https://prove2.me/submissions/4d53ada7-cbce-4bc9-a575-9694a1bd28ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfinitePlaceCompletionNhdsNEZeroNeBot
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InfinitePlaceCompletionNhdsNEZeroNeBotStatement
import Theorems.Thm_GlobalTheory_QSA_infinitePlace_completion_nhdsNE_neBot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  first | exact @GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | exact GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot | (intros; apply GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot <;> assumption)
end _root_.GlobalTheory.T
