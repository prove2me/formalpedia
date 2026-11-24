-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.colMat_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:03:06.08931+00:00
-- url     : https://prove2.me/submissions/bf03ed3e-24aa-4e4f-b7dd-1bd165560a21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (r s) :
    colMat n' (col e) r s = open Classical in if h : Free 1 (r, s) then e ⟨(r, s), h⟩ else 0 := by
  rcases s with s | s
  · rw [dif_neg]
    · simp [colMat]
    · rcases r with r | r <;> simp [Free]
  · refine Fin.cases ?_ (fun i => ?_) s
    · rw [dif_neg]
      · simp [colMat]
      · rcases r with r | r <;> simp [Free]
    · simp [colMat, col]
end GlobalTheory.RootEx.UnfoldShape
