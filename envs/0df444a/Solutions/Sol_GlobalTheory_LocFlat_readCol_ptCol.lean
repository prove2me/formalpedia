-- Prove2me | solution 1 for GlobalTheory.LocFlat.readCol_ptCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:33.949126+00:00
-- url     : https://prove2.me/submissions/8b8542ea-c4ac-4579-bac7-be2fba53ad07

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
theorem _root_.solution (p : ℕ) (hp1 : 1 ≤ p) (hp : p - 1 < c + 1) (x : Matrix n (n' ⊕ Unit) k) e :
    readCol p hp (ptCol p x e) = x := by
  ext r s
  rcases s with s | s
  · simp [readCol, ptCol, affPt, basePt, colAt, Free, Matrix.toCols₁]
  · simp [readCol, ptCol, affPt, basePt, colAt, Free]
    have h1 : ¬ p < p - 1 + 1 := by omega
    have h2 : p - 1 + 1 = p := by omega
    simp [h1, h2]
end GlobalTheory.LocFlat
