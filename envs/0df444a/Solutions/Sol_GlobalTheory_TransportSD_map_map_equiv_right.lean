-- Prove2me | solution 1 for GlobalTheory.TransportSD.map_map_equiv_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:39:04.887548+00:00
-- url     : https://prove2.me/submissions/9c4b1a63-832c-43ff-905b-c96065c355c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TransportSelfDualHaarMeasureKernelAddEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TransportSD
namespace GlobalTheory.TransportSD
theorem _root_.solution {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (T : α → β) (e : β ≃ᵐ γ) : (μ.map T).map e = μ.map (e ∘ T) := by
  by_cases hT : AEMeasurable T μ
  · exact AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hT
  · have hT' : ¬ AEMeasurable (e ∘ T) μ := by
      intro h
      apply hT
      have := e.symm.measurable.comp_aemeasurable h
      simpa [Function.comp_def] using this
    rw [Measure.map_of_not_aemeasurable hT, Measure.map_of_not_aemeasurable hT', Measure.map_zero]
end GlobalTheory.TransportSD
