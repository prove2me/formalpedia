-- Prove2me | solution 1 for GlobalTheory.StepData.exists_mem_KO_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:58:48.604955+00:00
-- url     : https://prove2.me/submissions/9403ca82-72b4-4391-8eb8-57016c13a363

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_KOne_le_KO
import Theorems.Thm_GlobalTheory_StepData_exists_mem_KOne
import Theorems.Thm_GlobalTheory_SplitWeil_Model_KOne_le_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
theorem _root_.solution {A A' : Matrix n n k} (hA : IntM A) (hA' : IntM A') (h : MaxM (A * A' - 1)) :
    ∃ g ∈ KO k n, g.val = A := by
  obtain ⟨u, hu, hu'⟩ := exists_mem_KOne h
  have e : A * (A' * (u⁻¹).val) = 1 := by rw [← Matrix.mul_assoc, ← hu', Units.mul_inv]
  exact ⟨⟨A, A' * (u⁻¹).val, e, mul_eq_one_comm.1 e⟩,
    mem_KO.2 ⟨hA, hA'.mul (mem_KO.1 (KOne_le_KO hu)).2⟩, rfl⟩
end GlobalTheory.StepData
