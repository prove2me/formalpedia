-- Prove2me | solution 1 for GlobalTheory.T.symmetricChain_supportOne_of_pattern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:26:44.479614+00:00
-- url     : https://prove2.me/submissions/8b97bfe0-e000-4ec1-8b99-db550d670960

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPatternStatement
import Theorems.Thm_GlobalTheory_SymSupport_supportOne_of_pattern


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.SupportOne t := by
  first | exact @GlobalTheory.SymSupport.supportOne_of_pattern | exact GlobalTheory.SymSupport.supportOne_of_pattern | (intros; apply GlobalTheory.SymSupport.supportOne_of_pattern <;> assumption)
end _root_.GlobalTheory.T
