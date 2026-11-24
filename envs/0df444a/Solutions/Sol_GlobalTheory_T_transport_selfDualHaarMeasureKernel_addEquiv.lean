-- Prove2me | solution 1 for GlobalTheory.T.transport_selfDualHaarMeasureKernel_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:34.706053+00:00
-- url     : https://prove2.me/submissions/94530cdc-0af1-4536-8d7b-67f537a23c5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TransportSelfDualHaarMeasureKernelAddEquiv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TransportSelfDualHaarMeasureKernelAddEquivStatement
import Theorems.Thm_GlobalTheory_transport_selfDual_fourB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ), (SelfDual μ B → SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y))) ∧ ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by
  first | exact @GlobalTheory.transport_selfDual_fourB | exact GlobalTheory.transport_selfDual_fourB | (intros; apply GlobalTheory.transport_selfDual_fourB <;> assumption)
end _root_.GlobalTheory.T
