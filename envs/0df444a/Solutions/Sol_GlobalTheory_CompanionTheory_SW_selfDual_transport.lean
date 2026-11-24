-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.selfDual_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:58:40.830845+00:00
-- url     : https://prove2.me/submissions/76e4cd47-cce6-46c1-99cd-efe4e22e335d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SelfdualMeasureTransportEquiv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_selfDual_map_of_comp

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution (V V' : Type) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ) :
    SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by
  refine ⟨selfDual_map_of_comp e μ χ, fun h => ?_⟩
  have h2 := selfDual_map_of_comp e.symm (μ.map e) (fun x y => χ (e x) (e y)) (by simpa using h)
  have hm : (μ.map e).map e.symm = μ := by
    have m1 : Measurable (e.symm : V' → V) := e.symm.continuous.measurable
    have m2 : Measurable (e : V → V') := e.continuous.measurable
    rw [Measure.map_map m1 m2]
    have : (e.symm : V' → V) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  rwa [hm] at h2
end GlobalTheory.CompanionTheory.SW
