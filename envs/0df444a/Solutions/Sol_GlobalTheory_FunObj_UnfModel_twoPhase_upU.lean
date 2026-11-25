-- Prove2me | solution 1 for GlobalTheory.FunObj.UnfModel.twoPhase_upU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:46:10.895909+00:00
-- url     : https://prove2.me/submissions/bde0bfa8-8cf1-40d8-a4b0-d924e700bae9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem

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
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type*} [Field k] {n n' n'' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype n''] [DecidableEq n'']
namespace GlobalTheory.FunObj.UnfModel
theorem _root_.solution (x₀ : Matrix n n' k) (e : StepVar n 2 n' → k) (x' : Matrix (n'' ⊕ Fin 1) (n ⊕ Fin 2) k)
    (β : n → k) : twoPhase ((colE 2 2 β).val * stepPt x₀ e) (x' * (colE 2 2 (-β)).val) = twoPhase (stepPt x₀ e) x' := by
  simp [twoPhase, ch, colE, upU, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, stepPt, basePt, Free, Kept,
    one_apply, mul_add, Finset.sum_add_distrib]
  rw [Finset.filter_singleton, if_neg (Fin.succ_ne_zero _).symm]
  simp only [Finset.card_empty, Nat.cast_zero]
  ring
end GlobalTheory.FunObj.UnfModel
