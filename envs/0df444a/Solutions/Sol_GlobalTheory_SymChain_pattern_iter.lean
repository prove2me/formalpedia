-- Prove2me | solution 1 for GlobalTheory.SymChain.pattern_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:26.254946+00:00
-- url     : https://prove2.me/submissions/43ee5842-4e98-451b-83e0-6210524a8d70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPatternStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Theorems.Thm_GlobalTheory_SymChain_IterPattern_iter_iff
import Theorems.Thm_GlobalTheory_T_mem_level_iff_symmetricPosition_entry_pattern


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
namespace GlobalTheory.SymChain
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] :
    S.Pattern t := by
  intro j g
  exact IterPattern.iter_iff S.P S.μ S.tame (GlobalTheory.T.mem_level_iff_symmetricPosition_entry_pattern k s κ S) j g
end GlobalTheory.SymChain
