-- Prove2me | solution 1 for GlobalTheory.FunObj.stepPt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:06.079512+00:00
-- url     : https://prove2.me/submissions/2ce8bb02-85e2-4e52-8f89-54bb448cf53b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Theorems.Thm_GlobalTheory_FunObj_Kept_not_free

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
variable (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c : ℕ)
variable {k n c}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.FunObj
theorem _root_.solution (x₀ : Matrix n n' k) (e : StepVar n c n' → k) : stepPt x₀ e =
    affPt (c / 2 + 1) x₀ (fun rs => e ⟨rs.1, Or.inl rs.2⟩) + keptPt fun rs => e ⟨rs.1, Or.inr rs.2⟩ := by
  ext r s
  by_cases h : Kept (r, s)
  · simp [stepPt, affPt, keptPt, h, h.not_free]
  · by_cases h' : Free (c / 2 + 1) (r, s) <;> simp [stepPt, affPt, keptPt, h, h']
end GlobalTheory.FunObj
