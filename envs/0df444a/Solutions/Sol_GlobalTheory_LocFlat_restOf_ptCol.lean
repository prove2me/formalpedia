-- Prove2me | solution 1 for GlobalTheory.LocFlat.restOf_ptCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:35.503605+00:00
-- url     : https://prove2.me/submissions/0b8b808d-f0d5-4299-b496-8dc1ad691be1

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
theorem _root_.solution (p : ℕ) (x : Matrix n (n' ⊕ Unit) k) e :
    restOf (rdCol p) (ptCol (c := c) p x e) = freeMat p e := by
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · simp [restOf, rdCol, freeMat, Free]
  · by_cases h : s.val + 1 = p
    · simp [restOf, rdCol, freeMat, Free, h]
    · simp [restOf, rdCol, freeMat, ptCol, affPt, basePt, colAt, Free, h]
  · simp [restOf, rdCol, freeMat, ptCol, affPt, basePt, colAt]
  · simp [restOf, rdCol, freeMat, ptCol, affPt, basePt, colAt]
end GlobalTheory.LocFlat
