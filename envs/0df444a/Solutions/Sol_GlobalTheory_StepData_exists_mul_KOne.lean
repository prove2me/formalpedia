-- Prove2me | solution 1 for GlobalTheory.StepData.exists_mul_KOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:54.421381+00:00
-- url     : https://prove2.me/submissions/ac91fe9b-92c3-4379-a2ef-abd54626f53b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_IntM_mul_maxM
import Theorems.Thm_GlobalTheory_StepData_mem_KO
import Theorems.Thm_GlobalTheory_StepData_exists_mem_KOne

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
namespace GlobalTheory.StepData
theorem _root_.solution {g : GL n k} (hg : g ∈ KO k n) {M : Matrix n n k} (h : MaxM (M - g.val)) :
    ∃ u ∈ KOne k n, (g * u).val = M := by
  obtain ⟨u, hu, hu'⟩ := exists_mem_KOne (M := (g⁻¹).val * M) (by
    have := (mem_KO.1 hg).2.mul_maxM h
    rwa [Matrix.mul_sub, Units.inv_mul] at this)
  exact ⟨u, hu, by rw [Units.val_mul, hu', ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩
end GlobalTheory.StepData
