-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.DensInt.density_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:52.860823+00:00
-- url     : https://prove2.me/submissions/087092a1-d2ee-4ab7-886f-6d4a43ee4289

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivity
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DensInt_exists_cutoff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_exists_cutoff


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DensInt
namespace GlobalTheory.CompanionTheory.SW.DensInt
theorem _root_.solution {V X Y : Type} [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (f : V → Y) (ι : X → Y)
    (B : Set X) (m : X → Measure V)
    (H : ∀ ψ : V → ℂ, Continuous ψ → HasCompactSupport ψ →
      HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B ψ (fun S => ∫ x, ψ x ∂(m S)) ∧ ∀ S, Integrable ψ (m S))
    (φ : V → ℂ) (hφc : Continuous φ) (hφ : Integrable φ μ) (hφS : ∀ S ∈ B, Integrable φ (m S))
    (hD : ContinuousOn (fun S => ∫ x, ‖φ x‖ ∂(m S)) B) (K : Set X) (hK : IsCompact K) (hKB : K ⊆ B) :
    ∫ v in f ⁻¹' (ι '' K), φ v ∂μ = ∫ b in K, (∫ x, φ x ∂(m b)) ∂ν := by
  obtain ⟨χ, hχc, hχs, hχb, hχ1⟩ := exists_cutoff V
  set ψ : ℕ → V → ℂ := fun k x => φ x * (χ k x : ℂ) with hψ
  have hψc : ∀ k, Continuous (ψ k) := fun k =>
    hφc.mul (Complex.continuous_ofReal.comp (hχc k))
  have hψs : ∀ k, HasCompactSupport (ψ k) := fun k => by
    have : HasCompactSupport (fun x => (χ k x : ℂ)) := (hχs k).comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    exact this.mul_left
  have hψn : ∀ k x, ‖ψ k x‖ ≤ ‖φ x‖ := fun k x => by
    simp only [hψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχb k x).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hχb k x).2
  have hψl : ∀ x, Filter.Tendsto (fun k => ψ k x) Filter.atTop (𝓝 (φ x)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχ1 x] with k hk
    simp [hψ, hk]
  have hmeas : ∀ k (ρ : Measure V), AEStronglyMeasurable (ψ k) ρ := fun k ρ =>
    (hψc k).aestronglyMeasurable

  have hL : Filter.Tendsto (fun k => ∫ v in f ⁻¹' (ι '' K), ψ k v ∂μ) Filter.atTop
      (𝓝 (∫ v in f ⁻¹' (ι '' K), φ v ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖) (fun k => hmeas k _) hφ.norm.integrableOn
      (fun k => Filter.Eventually.of_forall (hψn k)) (Filter.Eventually.of_forall hψl)

  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ S ∈ K, ‖∫ x, ‖φ x‖ ∂(m S)‖ ≤ C :=
    hK.exists_bound_of_continuousOn (hD.mono hKB)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hR : Filter.Tendsto (fun k => ∫ b in K, (∫ x, ψ k x ∂(m b)) ∂ν) Filter.atTop
      (𝓝 (∫ b in K, (∫ x, φ x ∂(m b)) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((H _ (hψc k) (hψs k)).1.1.mono hKB).aestronglyMeasurable hKm
    · haveI : IsFiniteMeasure (ν.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := ν)⟩
      exact integrable_const _
    · refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun S hS => ?_)
      calc ‖∫ x, ψ k x ∂(m S)‖ ≤ ∫ x, ‖ψ k x‖ ∂(m S) := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖φ x‖ ∂(m S) := integral_mono ((H _ (hψc k) (hψs k)).2 S).norm (hφS S (hKB hS)).norm (hψn k)
        _ ≤ ‖∫ x, ‖φ x‖ ∂(m S)‖ := Real.le_norm_self _
        _ ≤ C := hC S hS
    · refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun S hS => ?_)
      exact tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖) (fun k => hmeas k _)
        (hφS S (hKB hS)).norm (fun k => Filter.Eventually.of_forall (hψn k))
        (Filter.Eventually.of_forall hψl)
  refine tendsto_nhds_unique hL (hR.congr fun k => ?_)
  exact ((H _ (hψc k) (hψs k)).1.2 K hK hKB).symm
end GlobalTheory.CompanionTheory.SW.DensInt
