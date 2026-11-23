-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreUniq.measure_eq_of_lintegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:43.729284+00:00
-- url     : https://prove2.me/submissions/011f5959-39fd-4d0b-a751-5acb389e3cbf

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists

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
theorem _root_.solution {V : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (m m' : Measure V) (O : Set V) (hO : IsOpen O) (hm : m Oᶜ = 0) (hm' : m' Oᶜ = 0)
    (h : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ O → (∀ v, 0 ≤ φ v) →
      Integrable φ m ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂m = ∫⁻ v, ENNReal.ofReal (φ v) ∂m') :
    m = m' := by
  have hK : ∀ K : Set V, IsCompact K → K ⊆ O → m.restrict K = m'.restrict K := by
    intro K hK hKO
    obtain ⟨χ, h1, hc, hs, h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
    have hχm : Measurable fun v => ENNReal.ofReal (χ v) :=
      ENNReal.measurable_ofReal.comp χ.continuous.measurable
    have hint := (h χ χ.continuous hc hs (fun v => (h01 v).1)).1
    haveI : IsFiniteMeasure (m.withDensity fun v => ENNReal.ofReal (χ v)) :=
      isFiniteMeasure_withDensity_ofReal hint.2
    have key : (m.withDensity fun v => ENNReal.ofReal (χ v)) =
        m'.withDensity fun v => ENNReal.ofReal (χ v) := by
      apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
      intro g
      have hg : Measurable fun v => (g v : ℝ≥0∞) :=
        measurable_coe_nnreal_ennreal.comp g.continuous.measurable
      rw [lintegral_withDensity_eq_lintegral_mul _ hχm hg,
        lintegral_withDensity_eq_lintegral_mul _ hχm hg]
      have := (h (fun v => χ v * (g v : ℝ))
        (χ.continuous.mul (NNReal.continuous_coe.comp g.continuous))
        (HasCompactSupport.mul_right (f := fun v => χ v) hc)
        ((tsupport_mul_subset_left (f := fun v => χ v)).trans hs)
        (fun v => mul_nonneg (h01 v).1 (g v).2)).2
      have e : ∀ v, ENNReal.ofReal (χ v * (g v : ℝ)) = ENNReal.ofReal (χ v) * (g v : ℝ≥0∞) := by
        intro v
        rw [ENNReal.ofReal_mul (h01 v).1, ENNReal.ofReal_coe_nnreal]
      simpa only [e, Pi.mul_apply] using this
    have aux : ∀ n : Measure V, (n.withDensity fun v => ENNReal.ofReal (χ v)).restrict K
        = n.restrict K := by
      intro n
      rw [restrict_withDensity hK.measurableSet]
      have : (fun v => ENNReal.ofReal (χ v)) =ᵐ[n.restrict K] 1 := by
        filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
        simp [h1 hv]
      rw [withDensity_congr_ae this, withDensity_one]
    rw [← aux m, ← aux m', key]
  have hx : ∀ x ∈ O, ∃ K : Set V, K ∈ 𝓝[O] x ∧ IsCompact K ∧ K ⊆ O := by
    intro x hx
    obtain ⟨K, hK1, hK2, hK3⟩ := local_compact_nhds (hO.mem_nhds hx)
    exact ⟨K, mem_nhdsWithin_of_mem_nhds hK1, hK3, hK2⟩
  choose! K hK1 hK2 hK3 using hx
  obtain ⟨s, hsO, hsc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin hK1
  have hU : m.restrict (⋃ x ∈ s, K x) = m'.restrict (⋃ x ∈ s, K x) :=
    (Measure.restrict_biUnion_congr hsc).2 fun x hx => hK _ (hK2 x (hsO hx)) (hK3 x (hsO hx))
  have r : ∀ n : Measure V, n Oᶜ = 0 → n.restrict (⋃ x ∈ s, K x) = n := by
    intro n hn
    apply Measure.restrict_eq_self_of_ae_mem
    have : ∀ᵐ v ∂n, v ∈ O := hn
    filter_upwards [this] with v hv using hcov hv
  rw [← r m hm, ← r m' hm', hU]
end GlobalTheory.CompanionTheory.SW.FibreUniq
