-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.pt_mulVec_inX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:38.1317+00:00
-- url     : https://prove2.me/submissions/adca92d4-24b2-458a-a71a-f541fd0de774

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_inX_apply
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_pt_eq
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_colMat_mulVec
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_basePt_mulVec

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
omit [Fintype n] [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution (x₀ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) (v : n' → k) :
    pt x₀ y *ᵥ inX k n' (c + 1) v = inX k n c (x₀ *ᵥ v) := by
  rw [pt_eq, Matrix.add_mulVec, colMat_mulVec, basePt_mulVec]
  ext (r | r) <;> simp [inX_apply]
end GlobalTheory.RootEx.UnfoldShape
