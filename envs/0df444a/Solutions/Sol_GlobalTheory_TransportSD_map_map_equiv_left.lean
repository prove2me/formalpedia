-- Prove2me | solution 1 for GlobalTheory.TransportSD.map_map_equiv_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:39:03.754648+00:00
-- url     : https://prove2.me/submissions/6256530f-c302-427a-9b39-7eb01416ab21

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
    (μ : Measure α) (e : α ≃ᵐ β) (g : β → γ) : (μ.map e).map g = μ.map (g ∘ e) := by
  by_cases hg : AEMeasurable g (μ.map e)
  · exact AEMeasurable.map_map_of_aemeasurable hg e.measurable.aemeasurable
  · have hg' : ¬ AEMeasurable (g ∘ e) μ := by rwa [← aemeasurable_map_equiv_iff e]
    rw [Measure.map_of_not_aemeasurable hg, Measure.map_of_not_aemeasurable hg']
end GlobalTheory.TransportSD
