-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.col_uncol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:40.492636+00:00
-- url     : https://prove2.me/submissions/3b687ca5-8fac-4e95-9401-f581961827cf

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
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution {y : Fin c → (n ⊕ Fin c → k)} (hy : ∀ i, y i ∈ Yle k n c (i.val + 1)) :
    col (uncol n' y) = y := by
  ext i r
  rw [col]
  split_ifs with h
  · simp [uncol, colMat]
  · rcases r with r | r
    · simp [Free] at h
    · simp only [Free, Fin.val_succ] at h
      exact (hy i r (by omega)).symm
end GlobalTheory.RootEx.UnfoldShape
