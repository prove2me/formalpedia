-- Prove2me | solution 1 for GlobalTheory.LocFlat.readRow_ptRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:34.859849+00:00
-- url     : https://prove2.me/submissions/78c65902-c8e9-44f1-a709-0b9007e7eb70

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
theorem _root_.solution (p : ℕ) (hp1 : 1 ≤ p) (hp : p - 1 < c) (x : Matrix (n ⊕ Unit) n' k) e :
    readRow p hp (ptRow p x e) = x := by
  ext r s
  rcases r with r | r
  · simp [readRow, ptRow, affPt, basePt, rowAt, Free, Matrix.toRows₁]
  · have h1 : ¬ p - 1 + 1 < p := by omega
    have h2 : p - 1 + 1 = p := by omega
    simp [readRow, ptRow, affPt, basePt, rowAt, Free, h1, h2]
end GlobalTheory.LocFlat
