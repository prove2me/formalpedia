-- Prove2me | solution 1 for GlobalTheory.TwistVertex.embX_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:23:18.536259+00:00
-- url     : https://prove2.me/submissions/ff35b93b-cbe5-462c-8725-8fc9e2f59f86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwist
import Theorems.Thm_GlobalTheory_TwistVertex_val_embX
import Theorems.Thm_GlobalTheory_StepData_intM_fromBlocks
import Theorems.Thm_GlobalTheory_StepData_intM_one
import Theorems.Thm_GlobalTheory_StepData_intM_zero
import Theorems.Thm_GlobalTheory_StepData_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.TwistVertex
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.TwistVertex
theorem _root_.solution {g : GL n k} (hg : g ∈ KO k n) : embX c g ∈ KO k (n ⊕ Fin c) := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hg
  refine mem_KO.2 ⟨?_, ?_⟩
  · rw [val_embX]; exact intM_fromBlocks.2 ⟨h1, intM_zero, intM_zero, intM_one⟩
  · rw [← map_inv, val_embX]; exact intM_fromBlocks.2 ⟨h2, intM_zero, intM_zero, intM_one⟩
end GlobalTheory.TwistVertex
