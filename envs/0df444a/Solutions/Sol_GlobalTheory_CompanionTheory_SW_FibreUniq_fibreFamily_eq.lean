-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:35:43.56398+00:00
-- url     : https://prove2.me/submissions/c6e32392-c117-4879-850e-c27051fe915a

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_measure_eq_of_lintegral_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_ae_eq_of_isFibreFamily
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_lintegral_preimage
import Theorems.Thm_GlobalTheory_T_continuous_densities_eq_of_integrals_on_compacts


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
theorem _root_.solution (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (B B' : Set X) (hB : IsOpen B) (hB' : IsOpen B') (hBB : B' ⊆ B)
    (fib fib' : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    (h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B') ν B' fib')
    (b : X) (hb : b ∈ B') : fib' b = fib b := by
  have hO : IsOpen (g ⁻¹' B') := hB'.preimage hg
  have hOU : g ⁻¹' B' ⊆ g ⁻¹' B := preimage_mono hBB
  have carried : ∀ n : Measure V, (∀ᵐ v ∂n, g v = b) → n (g ⁻¹' B')ᶜ = 0 := by
    intro n hn
    have : ∀ᵐ v ∂n, v ∈ g ⁻¹' B' := by
      filter_upwards [hn] with v hv
      simpa [mem_preimage, hv] using hb
    exact this
  refine measure_eq_of_lintegral_eq _ _ (g ⁻¹' B') hO
    (carried _ ((ae_eq_of_isFibreFamily hι hf h' b).mono fun _ hv => hv.1))
    (carried _ ((ae_eq_of_isFibreFamily hι hf h b).mono fun _ hv => hv.1)) ?_
  intro φ hφ hc hs h0
  obtain ⟨hi, hc1⟩ := h.2.2 φ hφ hc (hs.trans hOU)
  obtain ⟨hi', hc2⟩ := h'.2.2 φ hφ hc hs
  refine ⟨hi' b hb, ?_⟩
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hφ0 : ∀ v, v ∉ g ⁻¹' B' → ENNReal.ofReal (φ v) = 0 := by
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport fun h => hv (hs h), ENNReal.ofReal_zero]
  have c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) B' :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hc1.mono hBB)).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi b (hBB hb)) (Filter.Eventually.of_forall h0)).symm
  have c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) B' :=
    (ENNReal.continuous_ofReal.comp_continuousOn hc2).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm
  refine GlobalTheory.T.continuous_densities_eq_of_integrals_on_compacts X ν B' hB' _ _ c' c (fun S hS _ => ?_) b hb
  rw [← lintegral_preimage hι hg hf hO subset_rfl h' _ hφm hφ0 S hS.measurableSet,
    ← lintegral_preimage hι hg hf hO hOU h _ hφm hφ0 S hS.measurableSet]
end GlobalTheory.CompanionTheory.SW.FibreUniq
