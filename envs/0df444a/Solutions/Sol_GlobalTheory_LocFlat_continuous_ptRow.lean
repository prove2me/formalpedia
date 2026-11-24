-- Prove2me | solution 1 for GlobalTheory.LocFlat.continuous_ptRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:38.5728+00:00
-- url     : https://prove2.me/submissions/0be13b47-c532-405f-9c71-d9a5a7685716

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Theorems.Thm_GlobalTheory_RootEx_continuous_affPt_uncurry
import Theorems.Thm_GlobalTheory_StepData_IntM_add
import Theorems.Thm_GlobalTheory_StepData_MaxM_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.LocFlat
theorem _root_.solution (p : ℕ) :
    Continuous fun q : Matrix (n ⊕ Unit) n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
      ptRow p q.1 q.2 := by
  refine ((continuous_affPt_uncurry p).comp (Continuous.prodMk ?_ continuous_snd)).add ?_
  · exact continuous_matrix fun r s => continuous_fst.matrix_elem _ _
  · refine continuous_matrix fun r s => ?_
    rcases r with r | r <;> rcases s with s | s
    · simp only [rowAt, fromBlocks_apply₁₁, Matrix.zero_apply]; exact continuous_const
    · simp only [rowAt, fromBlocks_apply₁₂, Matrix.zero_apply]; exact continuous_const
    · by_cases h : r.val + 1 = p
      · simp only [rowAt, fromBlocks_apply₂₁, Matrix.of_apply, h, if_true]
        exact continuous_fst.matrix_elem _ _
      · simp only [rowAt, fromBlocks_apply₂₁, Matrix.of_apply, h, if_false]; exact continuous_const
    · simp only [rowAt, fromBlocks_apply₂₂, Matrix.zero_apply]; exact continuous_const
end GlobalTheory.LocFlat
