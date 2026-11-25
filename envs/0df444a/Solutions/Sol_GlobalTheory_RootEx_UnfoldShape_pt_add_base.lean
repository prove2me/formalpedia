-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.pt_add_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:15:11.050724+00:00
-- url     : https://prove2.me/submissions/ee5c3fa2-2a73-43a5-9dc7-1c6d463a27c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_pt_eq

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
theorem _root_.solution (x₀ x₁ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) :
    pt (x₀ + x₁) y = pt x₀ y + fromBlocks x₁ 0 0 0 := by
  ext (r | r) (s | s) <;> simp [pt_eq, basePt, colMat]
end GlobalTheory.RootEx.UnfoldShape
