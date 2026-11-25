-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.col_mem_Yle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:19.390116+00:00
-- url     : https://prove2.me/submissions/30da66e4-a43b-441f-ad64-1d03e0760307

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
theorem _root_.solution (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) :
    col e i ∈ Yle k n c (i.val + 1) := by
  intro l hl
  rw [col, dif_neg]
  simp only [Free, Fin.val_succ]
  omega
end GlobalTheory.RootEx.UnfoldShape
