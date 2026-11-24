-- Prove2me | solution 1 for GlobalTheory.FunObj.stepPt_joinVars
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:44.591596+00:00
-- url     : https://prove2.me/submissions/80b91205-5275-42e4-8821-620986144758

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Theorems.Thm_GlobalTheory_FunObj_keptPart_joinVars
import Theorems.Thm_GlobalTheory_FunObj_stepPt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}
namespace GlobalTheory.FunObj
theorem _root_.solution (x₀ : Matrix n n' k) (w : KeptVar n c n' → k) (f : FreeVar n c n' → k) :
    stepPt x₀ (joinVars (w, f)) = affPt (c / 2 + 1) x₀ f + keptPt w := by
  rw [stepPt_eq]
  congr 2
  · funext rs
    exact congrArg (Sum.elim w f) ((stepVarEquiv n c n').symm_apply_apply (.inr rs))
  · exact keptPart_joinVars w f
end GlobalTheory.FunObj
