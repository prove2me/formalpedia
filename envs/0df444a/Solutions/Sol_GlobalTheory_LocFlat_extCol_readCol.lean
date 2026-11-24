-- Prove2me | solution 1 for GlobalTheory.LocFlat.extCol_readCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:05.80473+00:00
-- url     : https://prove2.me/submissions/7e160094-0519-4544-ae39-ee5d6527db03

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
theorem _root_.solution (p : ℕ) (hp : p - 1 < c + 1) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s)
    (h : rdCol p r s = true) : extCol (readCol p hp z) r s = z r s := by
  rcases r with r | r <;> rcases s with s | s
  · rfl
  · simp only [rdCol, decide_eq_true_eq] at h
    simp only [extCol, readCol, Matrix.of_apply, Sum.elim_inr]
    congr 2; ext; simp; omega
  · simp [rdCol] at h
  · simp [rdCol] at h
end GlobalTheory.LocFlat
