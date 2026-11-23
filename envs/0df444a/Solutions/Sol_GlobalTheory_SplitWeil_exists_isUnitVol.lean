-- Prove2me | solution 1 for GlobalTheory.SplitWeil.exists_isUnitVol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:20.391357+00:00
-- url     : https://prove2.me/submissions/f6bb20be-82cc-4a23-b36e-d63ec3c8f182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable [MeasurableSpace k] [BorelSpace k]
variable (k)
namespace GlobalTheory.SplitWeil
theorem _root_.solution : ∃ ν : Measure k, IsUnitVol ν := by
  let K : TopologicalSpace.PositiveCompacts k :=
    ⟨⟨𝒪[k], isCompact_int k⟩, by
      simp only [(isOpen_int k).interior_eq]
      exact ⟨0, zero_mem _⟩⟩
  exact ⟨Measure.addHaarMeasure K, inferInstance, Measure.addHaarMeasure_self⟩
end GlobalTheory.SplitWeil
