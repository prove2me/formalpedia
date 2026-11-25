-- Prove2me | solution 1 for GlobalTheory.T.rootExchangeRowUnipotent_mem_sourceLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:35:45.687165+00:00
-- url     : https://prove2.me/submissions/1a3b0d82-3a19-4da9-92c1-183695b1c8b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentMemSourceLevel
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentMemSourceLevelStatement
import Theorems.Thm_GlobalTheory_SymChain_rowE_mem_symLev_of_box


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ u : XIx (Fin κ) t j → k, u ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev j (c + 1 + 1) (by omega)).J := by
  first | exact @GlobalTheory.SymChain.rowE_mem_symLev_of_box | exact GlobalTheory.SymChain.rowE_mem_symLev_of_box | (intros; apply GlobalTheory.SymChain.rowE_mem_symLev_of_box <;> assumption)
end _root_.GlobalTheory.T
