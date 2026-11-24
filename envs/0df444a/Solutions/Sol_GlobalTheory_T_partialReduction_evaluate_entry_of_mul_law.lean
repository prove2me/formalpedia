-- Prove2me | solution 1 for GlobalTheory.T.partialReduction_evaluate_entry_of_mul_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:14.172536+00:00
-- url     : https://prove2.me/submissions/d780e92b-4381-4b4f-baf3-9e986fe8d417

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLaw
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLawStatement
import Theorems.Thm_GlobalTheory_PartRedEval_kills_insert_of_evalLaw


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ I → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.EvalLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β (insert e E) I := by
  first | exact @GlobalTheory.PartRedEval.kills_insert_of_evalLaw | exact GlobalTheory.PartRedEval.kills_insert_of_evalLaw | (intros; apply GlobalTheory.PartRedEval.kills_insert_of_evalLaw <;> assumption)
end _root_.GlobalTheory.T
