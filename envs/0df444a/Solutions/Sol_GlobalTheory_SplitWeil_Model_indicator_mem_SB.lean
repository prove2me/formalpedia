-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.indicator_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:13.61487+00:00
-- url     : https://prove2.me/submissions/a056e20c-43f5-44fc-8f03-f033d6e3938f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_Model_isCompact_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil.Model
theorem _root_.solution : (𝒪[k] : Set k).indicator (fun _ => (1 : ℂ)) ∈ SB k := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have hcl : IsClopen (𝒪[k] : Set k) := ⟨isCompact_int.isClosed, isOpen_int⟩
  refine ⟨?_, HasCompactSupport.intro isCompact_int fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const k (1 : ℂ)) hcl).isLocallyConstant
end GlobalTheory.SplitWeil.Model
