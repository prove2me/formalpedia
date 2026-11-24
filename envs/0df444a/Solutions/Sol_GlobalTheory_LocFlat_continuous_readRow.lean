-- Prove2me | solution 1 for GlobalTheory.LocFlat.continuous_readRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:27.236478+00:00
-- url     : https://prove2.me/submissions/e032fdae-b14f-4d60-a362-e60f05017958

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective

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
theorem _root_.solution (p : ℕ) (hp : p - 1 < c) :
    Continuous (readRow (k := k) (n := n) (n' := n') p hp) := by
  refine continuous_matrix fun r s => ?_
  rcases r with r | r
  · exact continuous_id.matrix_elem _ _
  · exact continuous_id.matrix_elem _ _
end GlobalTheory.LocFlat
