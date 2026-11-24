-- Prove2me | solution 1 for GlobalTheory.FunObj.stepPt_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:43.895719+00:00
-- url     : https://prove2.me/submissions/27454c90-3b1e-48f4-9092-a0c05347fbad

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
theorem _root_.solution (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (r : n) {i : Fin (c + 1)} (hi : i.val = c / 2) :
    stepPt x₀ e (.inl r) (.inr i) = keptPt (keptPart e) (.inl r) (.inr i) := by
  rw [stepPt_eq, Matrix.add_apply, affPt, Matrix.add_apply, of_apply, dif_neg (by simp [Free, hi])]
  simp [basePt]; rfl
end GlobalTheory.FunObj
