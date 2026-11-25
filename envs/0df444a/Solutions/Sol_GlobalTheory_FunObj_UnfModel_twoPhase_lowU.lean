-- Prove2me | solution 1 for GlobalTheory.FunObj.UnfModel.twoPhase_lowU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:46:04.74866+00:00
-- url     : https://prove2.me/submissions/a9648227-42cd-4b2f-b876-0dd9ac09fc75

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
theorem _root_.solution (x : Matrix (n ⊕ Fin 2) (n' ⊕ Fin 3) k) (x₀ : Matrix n'' n k) (e : StepVar n'' 1 n → k)
    (u : n → k) : twoPhase ((rowE 2 1 u).val * x) (stepPt x₀ e * (rowE 2 1 (-u)).val) = twoPhase x (stepPt x₀ e) := by
  simp [twoPhase, ch, rowE, lowU, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, stepPt, basePt, Free, Kept,
    one_apply, add_mul, Finset.sum_add_distrib]
  ring
end GlobalTheory.FunObj.UnfModel
