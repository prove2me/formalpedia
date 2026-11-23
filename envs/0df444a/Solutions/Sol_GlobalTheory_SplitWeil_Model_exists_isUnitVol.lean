-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.exists_isUnitVol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:31.554962+00:00
-- url     : https://prove2.me/submissions/b702d96b-9298-4351-97a6-69dc7aa840c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
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
namespace GlobalTheory.SplitWeil.Model
theorem _root_.solution : ∃ ν : Measure k, IsUnitVol ν := by
  let K : TopologicalSpace.PositiveCompacts k := ⟨⟨(𝒪[k] : Set k), isCompact_int⟩, by
    rw [show interior ((⟨(𝒪[k] : Set k), isCompact_int⟩ : TopologicalSpace.Compacts k).carrier) =
      (𝒪[k] : Set k) from isOpen_int.interior_eq]
    exact ⟨0, zero_mem _⟩⟩
  exact ⟨Measure.addHaarMeasure K, inferInstance, Measure.addHaarMeasure_self⟩
end GlobalTheory.SplitWeil.Model
