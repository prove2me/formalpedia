-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreUniq.lintegral_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:13.64385+00:00
-- url     : https://prove2.me/submissions/4ab91e03-c8bd-4575-a956-0f095bbe32c3

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_ae_eq_of_isFibreFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreUniq
namespace GlobalTheory.CompanionTheory.SW.FibreUniq
theorem _root_.solution {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → Y} {g : V → X} {ι : X → Y} (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) {O U : Set V} {B : Set X} {fib : X → Measure V}
    (hO : IsOpen O) (hU : O ⊆ U) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ O → φ v = 0)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v in O, (g ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((g ⁻¹' S).indicator φ) (hφ.indicator (hg.measurable hS))
  have e1 : ∫⁻ v in U, (g ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in O, (g ⁻¹' S).indicator φ v ∂μ := by
    have : (g ⁻¹' S).indicator φ = O.indicator ((g ⁻¹' S).indicator φ) := by
      funext v
      by_cases hv : v ∈ O
      · rw [indicator_of_mem hv]
      · rw [indicator_of_notMem hv]
        exact indicator_apply_eq_zero.2 fun _ => hs v hv
    conv_lhs => rw [this]
    rw [lintegral_indicator hO.measurableSet, Measure.restrict_restrict hO.measurableSet,
      inter_eq_left.2 hU]
  rw [← e1, h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb := ae_eq_of_isFibreFamily hι hf h b
  by_cases hbS : b ∈ S
  · rw [indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_mem (by simpa [mem_preimage, hv.1] using hbS) _
  · rw [indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_notMem (by simpa [mem_preimage, hv.1] using hbS) _
end GlobalTheory.CompanionTheory.SW.FibreUniq
