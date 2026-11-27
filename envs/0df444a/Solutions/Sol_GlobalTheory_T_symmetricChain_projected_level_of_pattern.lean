-- Prove2me | solution 1 for GlobalTheory.T.symmetricChain_projected_level_of_pattern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:14.790558+00:00
-- url     : https://prove2.me/submissions/e964c0c4-5803-4932-979c-b5e98badc30a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainProjectedLevelOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainProjectedLevelOfPatternStatement
import Theorems.Thm_GlobalTheory_SymChain_PrImage_prLevel_of_pattern


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.PrLevel t := by
  first | exact @GlobalTheory.SymChain.PrImage.prLevel_of_pattern | exact GlobalTheory.SymChain.PrImage.prLevel_of_pattern | (intros; apply GlobalTheory.SymChain.PrImage.prLevel_of_pattern <;> assumption)
end _root_.GlobalTheory.T
