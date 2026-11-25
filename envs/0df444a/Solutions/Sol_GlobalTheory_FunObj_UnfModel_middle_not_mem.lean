-- Prove2me | solution 1 for GlobalTheory.FunObj.UnfModel.middle_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:45:53.244123+00:00
-- url     : https://prove2.me/submissions/e51e54bb-6abe-4c38-a8f6-e4f23e10cd84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
import Theorems.Thm_GlobalTheory_FunObj_symN_odd
import Theorems.Thm_GlobalTheory_RootEx_Model_rowE_not_mem


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
theorem _root_.solution (ρ : ℕ) (u : n → k) (hu : u ≠ 0) : rowE (2 * ρ + 1) (ρ + 1) u ∉ symN k n (2 * ρ + 1) := by
  rw [symN_odd]
  exact RootEx.Model.rowE_not_mem (c := 2 * ρ + 1) ⟨ρ, by omega⟩ u hu
end GlobalTheory.FunObj.UnfModel
