-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocGauss.fibre_lintegral_eq_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:14:08.243903+00:00
-- url     : https://prove2.me/submissions/6051e280-a7b7-4bb9-99b6-5691d7abb125

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompacts
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsSizeMulLe
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianLocalContinuousCongruenceSectionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGramFiberContinuousDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_lintegral_preimage
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreUniq_lintegral_preimage
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_eq_of_setLIntegral_compact_eq


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocGauss
namespace GlobalTheory.CompanionTheory.SW.LocGauss
theorem _root_.solution {V X Y : Type}
    [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (B : Set X) (fib : X → Measure V)
    (hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    (b₀ : X) (O : Set X) (hO : IsOpen O) (hOB : O ⊆ B) (hb₀ : b₀ ∈ O)
    (T : X → V → V) (κ : X → ℝ≥0)
    (hT : ContinuousOn (fun p : X × V => T p.1 p.2) (O ×ˢ Set.univ))
    (hκ : ContinuousOn κ O) (hκ0 : ∀ b ∈ O, κ b ≠ 0)
    (hm : ∀ b ∈ O, fib b = (κ b : ℝ≥0∞) • (fib b₀).map (T b))
    (w u : V → ℝ≥0∞) (hw : Measurable w) (hu : Continuous u) (hwμ : ∫⁻ v, w v ∂μ < ∞)
    (C : ℝ≥0) (huw : ∀ v, u v ≤ C * w v)
    (hwT : ∀ L : Set X, IsCompact L → L ⊆ O → ∃ c : ℝ≥0, ∀ b ∈ L, ∀ v,
      w (T b v) ≤ c * w v ∧ w v ≤ c * w (T b v))
    (d : X → ℝ≥0∞) (hd : ContinuousOn d O)
    (hdens : ∀ L : Set X, IsCompact L → L ⊆ O → ∫⁻ v in g ⁻¹' L, u v ∂μ = ∫⁻ b in L, d b ∂ν) :
    ∫⁻ v, u v ∂(fib b₀) = d b₀ := by
  have hum : Measurable u := hu.measurable
  have hAt : ∀ b ∈ O, ∀ v, ContinuousAt (fun p : X × V => T p.1 p.2) (b, v) := fun b hb v =>
    hT.continuousAt ((hO.prod isOpen_univ).mem_nhds ⟨hb, Set.mem_univ v⟩)
  have hTc : ∀ b ∈ O, Continuous (T b) := fun b hb =>
    continuous_iff_continuousAt.2 fun v =>
      ContinuousAt.comp (f := fun v : V => (b, v)) (g := fun p : X × V => T p.1 p.2)
        (hAt b hb v) (by fun_prop)
  have hTm : ∀ b ∈ O, Measurable (T b) := fun b hb => (hTc b hb).measurable

  have hint : ∀ b ∈ O, ∀ h : V → ℝ≥0∞, Measurable h →
      ∫⁻ v, h v ∂(fib b) = (κ b : ℝ≥0∞) * ∫⁻ v, h (T b v) ∂(fib b₀) := by
    intro b hb h hh
    rw [hm b hb, lintegral_smul_measure, lintegral_map hh (hTm b hb), smul_eq_mul]
  obtain ⟨L, hLn, hLO, hLc⟩ := local_compact_nhds (hO.mem_nhds hb₀)
  obtain ⟨c, hc⟩ := hwT L hLc hLO
  have hLB : L ⊆ B := hLO.trans hOB

  have hex : ∃ b₁ ∈ L, ∫⁻ v, w v ∂(fib b₁) < ∞ := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∫⁻ v in g ⁻¹' L, w v ∂μ = ∫⁻ b in L, ∫⁻ v, w v ∂(fib b) ∂ν :=
      FibreDensity.lintegral_preimage hι hf hg hfib hLc hLB hw
    have h2 : ∫⁻ b in L, ∫⁻ v, w v ∂(fib b) ∂ν = ∞ := by
      rw [setLIntegral_congr_fun hLc.measurableSet (g := fun _ => ∞)
        (fun b hb => top_le_iff.1 (hcon b hb)), setLIntegral_const,
        ENNReal.top_mul (Measure.measure_pos_of_mem_nhds ν hLn).ne']
    have h3 : ∫⁻ v in g ⁻¹' L, w v ∂μ ≤ ∫⁻ v, w v ∂μ := setLIntegral_le_lintegral _ _
    rw [h1, h2] at h3
    exact absurd (h3.trans_lt hwμ) (lt_irrefl _)
  obtain ⟨b₁, hb₁, hb₁f⟩ := hex

  have hI : ∫⁻ v, w v ∂(fib b₀) < ∞ := by
    have h1 := hint b₁ (hLO hb₁) w hw
    have hk : (κ b₁ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hκ0 b₁ (hLO hb₁)
    have h2 : ∫⁻ v, w (T b₁ v) ∂(fib b₀) < ∞ := by
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      rw [h1, hcon, ENNReal.mul_top hk] at hb₁f
      exact lt_irrefl _ hb₁f
    calc ∫⁻ v, w v ∂(fib b₀) ≤ ∫⁻ v, (c : ℝ≥0∞) * w (T b₁ v) ∂(fib b₀) :=
          lintegral_mono fun v => (hc b₁ hb₁ v).2
      _ = (c : ℝ≥0∞) * ∫⁻ v, w (T b₁ v) ∂(fib b₀) :=
          lintegral_const_mul _ (hw.comp (hTm b₁ (hLO hb₁)))
      _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top h2

  have hbound : ∀ b ∈ L, ∀ v, u (T b v) ≤ ((C : ℝ≥0∞) * c) * w v := by
    intro b hb v
    calc u (T b v) ≤ C * w (T b v) := huw _
      _ ≤ C * (c * w v) := by gcongr; exact (hc b hb v).1
      _ = _ := by rw [mul_assoc]
  have hbfin : ∫⁻ v, ((C : ℝ≥0∞) * c) * w v ∂(fib b₀) ≠ ∞ := by
    rw [lintegral_const_mul _ hw]
    exact (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top) hI).ne
  set H : X → ℝ≥0∞ := fun b => ∫⁻ v, u (T b v) ∂(fib b₀) with hH
  have hHfin : ∀ b ∈ L, H b ≠ ∞ := fun b hb =>
    ne_top_of_le_ne_top hbfin (lintegral_mono fun v => hbound b hb v)
  have hHc : ∀ b ∈ interior L, ContinuousAt H b := by
    intro b hb
    have hbL : L ∈ 𝓝 b := mem_interior_iff_mem_nhds.1 hb
    have hbO : b ∈ O := hLO (interior_subset hb)
    refine tendsto_lintegral_filter_of_dominated_convergence (fun v => ((C : ℝ≥0∞) * c) * w v)
      ?_ ?_ hbfin ?_
    · filter_upwards [hbL] with b' hb'
      exact hum.comp (hTm b' (hLO hb'))
    · filter_upwards [hbL] with b' hb'
      exact Filter.Eventually.of_forall fun v => hbound b' hb' v
    · refine Filter.Eventually.of_forall fun v => ?_
      have h1 : ContinuousAt (fun b' : X => T b' v) b :=
        ContinuousAt.comp (f := fun b' : X => (b', v)) (g := fun p : X × V => T p.1 p.2)
          (hAt b hbO v) (by fun_prop)
      exact (hu.continuousAt.comp h1).tendsto
  set G : X → ℝ≥0∞ := fun b => ∫⁻ v, u v ∂(fib b) with hG
  have hGc : ContinuousOn G (interior L) := by
    intro b hb
    have hbL : L ∈ 𝓝 b := mem_interior_iff_mem_nhds.1 hb
    have hbO : b ∈ O := hLO (interior_subset hb)
    have h1 : ContinuousAt (fun b' => (κ b' : ℝ≥0∞) * H b') b := by
      have hk : ContinuousAt (fun b' => (κ b' : ℝ≥0∞)) b :=
        ENNReal.continuous_coe.continuousAt.comp (hκ.continuousAt (hO.mem_nhds hbO))
      exact ENNReal.Tendsto.mul hk (Or.inr (hHfin b (interior_subset hb))) (hHc b hb)
        (Or.inr ENNReal.coe_ne_top)
    refine (h1.congr ?_).continuousWithinAt
    filter_upwards [hbL] with b' hb'
    exact (hint b' (hLO hb') u hum).symm
  have key := eq_of_setLIntegral_compact_eq X ν (interior L) isOpen_interior G d hGc
    (hd.mono (interior_subset.trans hLO)) (fun S hS hSL => ?_) b₀ (mem_interior_iff_mem_nhds.2 hLn)
  · exact key
  · have hSO : S ⊆ O := hSL.trans (interior_subset.trans hLO)
    rw [← hdens S hS hSO]
    exact (FibreDensity.lintegral_preimage hι hf hg hfib hS (hSO.trans hOB) hum).symm
end GlobalTheory.CompanionTheory.SW.LocGauss
