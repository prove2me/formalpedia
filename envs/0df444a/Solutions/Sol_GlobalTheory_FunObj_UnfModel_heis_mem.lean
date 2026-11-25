-- Prove2me | solution 1 for GlobalTheory.FunObj.UnfModel.heis_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:45:49.442025+00:00
-- url     : https://prove2.me/submissions/926b999d-9e44-49f7-a895-950448b3ca93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
import Theorems.Thm_GlobalTheory_FunObj_symN_even
import Theorems.Thm_GlobalTheory_RootEx_Model_colE_mem
import Theorems.Thm_GlobalTheory_RootEx_Model_rowE_mem


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
theorem _root_.solution (ρ : ℕ) (u β : n → k) : rowE (2 * ρ) ρ u ∈ symN k n (2 * ρ) ∧ colE (2 * ρ) (ρ + 1) β ∈ symN k n (2 * ρ) := by
  rw [symN_even]
  exact ⟨Subgroup.mem_sup_right (RootEx.Model.rowE_mem ρ u), Subgroup.mem_sup_left (RootEx.Model.colE_mem ρ β)⟩
end GlobalTheory.FunObj.UnfModel
