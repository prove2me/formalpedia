-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.pt_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:31.829008+00:00
-- url     : https://prove2.me/submissions/dd637e34-b30d-4700-a83c-70f01c5caab2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_pt_eq
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_colMat_add

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
theorem _root_.solution (x₀ : Matrix n n' k) (y z : Fin c → (n ⊕ Fin c → k)) :
    pt x₀ (y + z) = pt x₀ y + colMat n' z := by
  rw [pt_eq, pt_eq, colMat_add, add_assoc]
end GlobalTheory.RootEx.UnfoldShape
