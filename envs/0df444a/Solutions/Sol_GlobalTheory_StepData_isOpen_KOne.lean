-- Prove2me | solution 1 for GlobalTheory.StepData.isOpen_KOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:37.151111+00:00
-- url     : https://prove2.me/submissions/d263195d-9d1f-4b2f-9dff-949bbedc7915

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Theorems.Thm_GlobalTheory_StepData_mem_KOne

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
theorem _root_.solution : IsOpen (KOne k n : Set (GL n k)) := by
  have e : (KOne k n : Set (GL n k)) = ⋂ i, ⋂ j, (fun g : GL n k => (g.val - 1) i j) ⁻¹' {x | valuation k x < 1} := by
    ext g; simp only [SetLike.mem_coe, mem_KOne, Set.mem_iInter]; rfl
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · have := Units.continuous_val (M := Matrix n n k)
    fun_prop
  · simpa using (valuation k).isOpen_ball 1
end GlobalTheory.StepData
