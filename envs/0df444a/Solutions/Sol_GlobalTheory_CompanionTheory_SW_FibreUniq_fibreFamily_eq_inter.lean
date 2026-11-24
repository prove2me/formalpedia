-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreUniq.fibreFamily_eq_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:21:26.434264+00:00
-- url     : https://prove2.me/submissions/4ee5cb4f-827a-49ba-a47b-0ffeff4d7bc2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableEmbeddingOfInjectiveProper
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_lintegral_preimage
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_measure_eq_of_lintegral_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreUniq
namespace GlobalTheory.CompanionTheory.SW.FibreUniq
theorem _root_.solution (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (W : Set V) (hW : IsOpen W)
    (B B' : Set X) (hB : IsOpen B) (hB' : IsOpen B') (hBB : B' ⊆ B)
    (fib fib' : X → Measure V)
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B ∩ W) ν B fib)
    (h' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B' ∩ W) ν B' fib')
    (b : X) (hb : b ∈ B') : fib' b = fib b := by
  have hO : IsOpen (g ⁻¹' B' ∩ W) := (hB'.preimage hg).inter hW
  have hOU : g ⁻¹' B' ∩ W ⊆ g ⁻¹' B ∩ W := Set.inter_subset_inter_left _ (Set.preimage_mono hBB)
  have hbB : b ∈ B := hBB hb
  refine measure_eq_of_lintegral_eq (fib' b) (fib b) (g ⁻¹' B' ∩ W) hO ?_ ?_ ?_
  · refine measure_mono_null ?_ (h'.1 b)
    intro v hv hv'
    exact hv hv'.2
  · refine measure_mono_null ?_ (h.1 b)
    intro v hv hv'
    have hgv : g v = b := hι (by rw [← hf v]; exact hv'.1)
    exact hv ⟨show g v ∈ B' from hgv ▸ hb, hv'.2.2⟩
  · intro φ hφc hφs hφO hφnn
    have hφU : tsupport φ ⊆ g ⁻¹' B ∩ W := hφO.trans hOU
    obtain ⟨hint', hcont'⟩ := h'.2.2 φ hφc hφs hφO
    obtain ⟨hint, hcont⟩ := h.2.2 φ hφc hφs hφU
    refine ⟨hint' b hb, ?_⟩
    have hψm : Measurable (fun v => ENNReal.ofReal (φ v)) := hφc.measurable.ennreal_ofReal
    have hψ0 : ∀ v, v ∉ g ⁻¹' B' ∩ W → ENNReal.ofReal (φ v) = 0 := by
      intro v hv
      have hz : φ v = 0 := by
        by_contra hne
        exact hv (hφO (subset_tsupport φ (Function.mem_support.mpr hne)))
      simp [hz]
    have hF : ∀ c ∈ B, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) = ENNReal.ofReal (∫ v, φ v ∂(fib c)) :=
      fun c hc => (ofReal_integral_eq_lintegral_ofReal (hint c hc) (ae_of_all _ hφnn)).symm
    have hF' : ∀ c ∈ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) =
        ENNReal.ofReal (∫ v, φ v ∂(fib' c)) :=
      fun c hc => (ofReal_integral_eq_lintegral_ofReal (hint' c hc) (ae_of_all _ hφnn)).symm
    have hset : ∀ S, MeasurableSet S →
        ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) ∂ν =
          ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) ∂ν := by
      intro S hS
      have hS' : MeasurableSet (S ∩ B') := hS.inter hB'.measurableSet
      have e1 := lintegral_preimage hι hg hf hO hOU h (fun v => ENNReal.ofReal (φ v)) hψm hψ0 _ hS'
      have e2 := lintegral_preimage hι hg hf hO Set.Subset.rfl h' (fun v => ENNReal.ofReal (φ v))
        hψm hψ0 _ hS'
      exact e1.symm.trans e2
    have key : ∀ (k k' : X → ℝ≥0∞) (T : Set X), MeasurableSet T → (∀ c ∈ T, k c = k' c) →
        ∫⁻ c in T, k c ∂ν = ∫⁻ c in T, k' c ∂ν := fun k k' T hT hkk =>
      lintegral_congr_ae ((ae_restrict_iff' hT).2 (Filter.Eventually.of_forall hkk))
    have hae : (fun c => ENNReal.ofReal (∫ v, φ v ∂(fib c))) =ᵐ[ν.restrict B']
        (fun c => ENNReal.ofReal (∫ v, φ v ∂(fib' c))) := by
      refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ ?_ ?_ ?_
      · exact ((hcont.mono hBB).aemeasurable hB'.measurableSet).ennreal_ofReal
      · exact (hcont'.aemeasurable hB'.measurableSet).ennreal_ofReal
      · intro S hS _
        rw [Measure.restrict_restrict hS]
        have hT : MeasurableSet (S ∩ B') := hS.inter hB'.measurableSet
        calc ∫⁻ c in S ∩ B', ENNReal.ofReal (∫ v, φ v ∂(fib c)) ∂ν
            = ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib c) ∂ν :=
              key _ _ _ hT (fun c hc => (hF c (hBB hc.2)).symm)
          _ = ∫⁻ c in S ∩ B', ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' c) ∂ν := hset S hS
          _ = ∫⁻ c in S ∩ B', ENNReal.ofReal (∫ v, φ v ∂(fib' c)) ∂ν :=
              key _ _ _ hT (fun c hc => hF' c hc.2)
    have heq := Measure.eqOn_open_of_ae_eq hae hB'
      (ENNReal.continuous_ofReal.comp_continuousOn (hcont.mono hBB))
      (ENNReal.continuous_ofReal.comp_continuousOn hcont') hb
    rw [hF' b hb, hF b hbB]
    exact heq.symm
end GlobalTheory.CompanionTheory.SW.FibreUniq
