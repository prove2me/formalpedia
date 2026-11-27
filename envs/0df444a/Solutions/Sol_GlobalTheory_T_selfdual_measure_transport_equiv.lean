-- Prove2me | solution 1 for GlobalTheory.T.selfdual_measure_transport_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:34:16.251751+00:00
-- url     : https://prove2.me/submissions/5454ceb2-cdb0-4d7e-aeac-eab791e11889

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SelfdualMeasureTransportEquiv
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SelfdualMeasureTransportEquivStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_selfDual_transport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V'] (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ), SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_transport | exact GlobalTheory.CompanionTheory.SW.selfDual_transport | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_transport <;> assumption)
end _root_.GlobalTheory.T
