-- Prove2me | solution 1 for GlobalTheory.FunObj.stepPt_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:45.867293+00:00
-- url     : https://prove2.me/submissions/590b43e8-c738-4923-bbaf-b3e55b40c315

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
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
theorem _root_.solution (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (s : n') {l : Fin c} (hl : l.val = c / 2) :
    stepPt x₀ e (.inr l) (.inl s) = keptPt (keptPart e) (.inr l) (.inl s) := by
  rw [stepPt_eq, Matrix.add_apply, affPt, Matrix.add_apply, of_apply, dif_neg (by simp [Free, hl])]
  simp [basePt]; rfl
end GlobalTheory.FunObj
