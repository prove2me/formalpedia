-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:18:27.604002+00:00
-- url     : https://prove2.me/submissions/f62739ff-35b3-4fd8-82be-0eb0c6214725

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ClosedSubgroupQuotientMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Averaging_setLIntegral_mul_right_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Averaging_lintegral_sum_cosets_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatticeUnimod_unimodular_of_isFundamentalDomain
import Theorems.Thm_GlobalTheory_T_closed_subgroup_quotient_measure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Averaging
namespace GlobalTheory.CompanionTheory.SW.Averaging
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕 : Set G) (𝓕₁ : Set G₁), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (Q : Type) [Countable Q] (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ u ∈ Γ₁, ∀ g, φ (ι u * g) = φ g) → ∫⁻ h in 𝓕, ∑' q, φ (r q * h) ∂μ = ∫⁻ h in 𝓕, ∑' q, (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * (r q * h)) ∂μ₁ ∂μ := by
  intro G _ _ _ _ _ _ _ _ G₁ _ _ _ _ _ _ _ ι hιce μ _ μ₁ _ Γ _ Γ₁ _ 𝓕 𝓕₁ h𝓕 h𝓕₁ hfin hΓ Q _ r hr hQ φ hφ hinv
  haveI : T2Space G₁ := hιce.isEmbedding.t2Space
  obtain ⟨hne, hright, hinvinv⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin
  haveI := hright
  haveI := hinvinv
  obtain ⟨w, hw, hw1⟩ := GlobalTheory.T.closed_subgroup_quotient_measure G G₁ ι hιce μ₁
  have hιc : Continuous ι := hιce.continuous
  have hι : Function.Injective ι := hιce.injective
  have hm : Measurable (fun p : G × G₁ => φ (ι p.2 * p.1)) :=
    hφ.comp ((hιc.comp continuous_snd).mul continuous_fst).measurable
  have hAm : Measurable (fun g : G => ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁) := hm.lintegral_prod_right'
  have hAinv : ∀ (v : G₁) (g : G),
      ∫⁻ u in 𝓕₁, φ (ι u * (ι v * g)) ∂μ₁ = ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁ := by
    intro v g
    have h := setLIntegral_mul_right_eq μ₁ Γ₁ 𝓕₁ h𝓕₁ (fun u => φ (ι u * g)) (fun γ hγ u => by
      simp only [map_mul, mul_assoc]
      exact hinv γ hγ _) v
    simpa only [map_mul, mul_assoc] using h
  have hA := lintegral_sum_cosets_eq ι hιc hι μ μ₁ Γ Γ₁ 𝓕 𝓕₁ h𝓕 h𝓕₁ hΓ r hr hQ w hw hw1 φ hφ hinv
  have hB := lintegral_sum_cosets_eq ι hιc hι μ μ₁ Γ Γ₁ 𝓕 𝓕₁ h𝓕 h𝓕₁ hΓ r hr hQ w hw hw1
    (fun g => (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁) (hAm.const_mul _)
    (fun u _ g => by simp only [hAinv])
  rw [hA, hB]
  refine lintegral_congr fun g => ?_
  congr 1
  simp only [hAinv]
  rw [setLIntegral_const, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hne hfin.ne, one_mul]
end GlobalTheory.CompanionTheory.SW.Averaging
