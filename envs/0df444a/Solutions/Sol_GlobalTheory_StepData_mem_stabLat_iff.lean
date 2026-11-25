-- Prove2me | solution 1 for GlobalTheory.StepData.mem_stabLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:13.53746+00:00
-- url     : https://prove2.me/submissions/287eba6e-8bc4-4f3f-a622-ab6bf50060e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_mem_stabLat
import Theorems.Thm_GlobalTheory_StepData_latOf_le_iff
import Theorems.Thm_GlobalTheory_StepData_mem_KO


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
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
variable [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData
theorem _root_.solution {g h : GL Y k} : h ∈ stabLat g ↔ latOf (h * g) = latOf g := by
  rw [mem_stabLat, mem_KO, le_antisymm_iff, latOf_le_iff, latOf_le_iff]
  simp [mul_assoc]
end GlobalTheory.StepData
