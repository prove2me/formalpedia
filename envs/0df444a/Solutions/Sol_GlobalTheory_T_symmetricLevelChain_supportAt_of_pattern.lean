-- Prove2me | solution 1 for GlobalTheory.T.symmetricLevelChain_supportAt_of_pattern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:45.142949+00:00
-- url     : https://prove2.me/submissions/fef840b1-2f99-4d3f-936a-0bf023d7f3bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainSupportAtOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainSupportAtOfPatternStatement
import Theorems.Thm_GlobalTheory_SymSupportP_supportAt_of_pattern


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.SupportAt t := by
  first | exact @GlobalTheory.SymSupportP.supportAt_of_pattern | exact GlobalTheory.SymSupportP.supportAt_of_pattern | (intros; apply GlobalTheory.SymSupportP.supportAt_of_pattern <;> assumption)
end _root_.GlobalTheory.T
