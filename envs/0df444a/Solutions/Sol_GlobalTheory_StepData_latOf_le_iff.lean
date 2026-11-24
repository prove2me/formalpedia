-- Prove2me | solution 1 for GlobalTheory.StepData.latOf_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:41.470954+00:00
-- url     : https://prove2.me/submissions/28d6980a-42bd-42f5-b27d-e289221020a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_mem_latOf_one
import Theorems.Thm_GlobalTheory_StepData_mulVec_mem_latOf

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
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData
theorem _root_.solution {g g' : GL Y k} : latOf g ≤ latOf g' ↔ IntM (g'⁻¹ * g).val := by
  constructor
  · intro h i j
    have : g.val *ᵥ Pi.single j 1 ∈ latOf g := by
      have := (mulVec_mem_latOf g (g := 1) (y := Pi.single j 1)).2 (mem_latOf_one.2 fun l => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _])
      rwa [mul_one] at this
    have := h this i
    rwa [mulVec_mulVec, mulVec_single_one] at this
  · intro h y hy i
    have : (g'⁻¹).val *ᵥ y = (g'⁻¹ * g).val *ᵥ ((g⁻¹).val *ᵥ y) := by
      simp [mulVec_mulVec, Matrix.mul_assoc]
    rw [this]
    exact sum_mem fun l _ => mul_mem (h i l) (hy l)
end GlobalTheory.StepData
