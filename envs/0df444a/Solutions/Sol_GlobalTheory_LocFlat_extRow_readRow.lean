-- Prove2me | solution 1 for GlobalTheory.LocFlat.extRow_readRow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:30:30.777143+00:00
-- url     : https://prove2.me/submissions/fa611b5c-cc96-4f69-9ede-6a5f5ab3957b

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
theorem _root_.solution (p : ℕ) (hp : p - 1 < c) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s)
    (h : rdRow p r s = true) : extRow (readRow p hp z) r s = z r s := by
  rcases r with r | r <;> rcases s with s | s
  · rfl
  · simp [rdRow] at h
  · simp only [rdRow, decide_eq_true_eq] at h
    simp only [extRow, readRow, Matrix.of_apply, Sum.elim_inr]
    congr 2; ext; simp; omega
  · simp [rdRow] at h
end GlobalTheory.LocFlat
