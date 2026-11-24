-- Prove2me | solution 1 for GlobalTheory.LocFlat.restOf_ptRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:36.335006+00:00
-- url     : https://prove2.me/submissions/e07314be-40b5-4f03-ad6a-bc87833cf6d7

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
theorem _root_.solution (p : ℕ) (x : Matrix (n ⊕ Unit) n' k) e :
    restOf (rdRow p) (ptRow (c := c) p x e) = freeMat p e := by
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · simp [restOf, rdRow, freeMat, Free]
  · simp [restOf, rdRow, freeMat, ptRow, affPt, basePt, rowAt]
  · by_cases h : r.val + 1 = p
    · simp [restOf, rdRow, freeMat, Free, h]
    · simp [restOf, rdRow, freeMat, ptRow, affPt, basePt, rowAt, Free, h]
  · simp [restOf, rdRow, freeMat, ptRow, affPt, basePt, rowAt]
end GlobalTheory.LocFlat
