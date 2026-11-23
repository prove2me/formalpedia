-- Prove2me | solution 1 for GlobalTheory.StepData.inv_mul_mem_KOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:21.352635+00:00
-- url     : https://prove2.me/submissions/1f83f5ea-a1e6-45b5-a660-e65b1a5c9d37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_exists_mul_KOne

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
theorem _root_.solution {g g' : GL n k} (hg : g ∈ KO k n) (h : MaxM (g'.val - g.val)) : g⁻¹ * g' ∈ KOne k n := by
  obtain ⟨u, hu, hu'⟩ := exists_mul_KOne hg h
  rwa [← Units.ext hu', inv_mul_cancel_left]
end GlobalTheory.StepData
