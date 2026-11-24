-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:27:50.868411+00:00
-- url     : https://prove2.me/submissions/1a34cafb-f6dd-44ea-a181-45d3b5ce3981

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ClosedSubgroupQuotientMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Averaging_bijective_pair

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {G₁ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
namespace GlobalTheory.CompanionTheory.SW.Averaging
theorem _root_.solution (ι : G₁ →* G) (hιc : Continuous ι) (hι : Function.Injective ι)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (μ₁ : Measure G₁) [SFinite μ₁] [μ₁.IsMulLeftInvariant] [μ₁.IsInvInvariant]
    (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁]
    (𝓕 : Set G) (𝓕₁ : Set G₁)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕₁ : IsFundamentalDomain Γ₁ 𝓕₁ μ₁)
    (hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ) {Q : Type} [Countable Q] (r : Q → G) (hr : ∀ q, r q ∈ Γ)
    (hQ : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q)
    (w : G → ℝ≥0∞) (hw : Measurable w) (hw1 : ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1)
    (ψ : G → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ u ∈ Γ₁, ∀ g, ψ (ι u * g) = ψ g) :
    ∫⁻ h in 𝓕, ∑' q, ψ (r q * h) ∂μ = ∫⁻ g, w g * ∫⁻ u in 𝓕₁, ψ (ι u * g) ∂μ₁ ∂μ := by
  have hιm : Measurable ι := hιc.measurable
  have hm1 : Measurable (fun p : G × G₁ => ι p.2 * p.1) :=
    ((hιc.comp continuous_snd).mul continuous_fst).measurable
  have hm2 : Measurable (fun p : G₁ × G => (ι p.1)⁻¹ * p.2) :=
    ((hιc.comp continuous_fst).inv.mul continuous_snd).measurable
  have hm3 : Measurable (fun p : G × G₁ => (ι p.2)⁻¹ * p.1) :=
    ((hιc.comp continuous_snd).inv.mul continuous_fst).measurable
  have hWm : Measurable (fun g : G => ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) ∂μ₁) :=
    (hw.comp hm3).lintegral_prod_right'
  have hFm : Measurable (fun g : G => ψ g * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) ∂μ₁) := hψ.mul hWm
  have hsumW : ∀ x : G, ∑' v : Γ₁, ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (ι (v : G₁)⁻¹ * x)) ∂μ₁ = 1 := by
    intro x
    have h0 : ∫⁻ y, w ((ι y)⁻¹ * x) ∂μ₁ = 1 := by
      have h := lintegral_inv_eq_self (μ := μ₁) (fun y => w (ι y * x))
      simp only [map_inv] at h
      rw [h, hw1 x]
    rw [← h0, h𝓕₁.lintegral_eq_tsum'' (fun y => w ((ι y)⁻¹ * x))]
    refine tsum_congr fun v => lintegral_congr fun u => ?_
    simp only [Subgroup.smul_def, smul_eq_mul, map_mul, map_inv, mul_inv_rev, mul_assoc]
  have key : ∀ u : G₁, ∫⁻ g, w g * ψ (ι u * g) ∂μ = ∫⁻ g, w ((ι u)⁻¹ * g) * ψ g ∂μ := by
    intro u
    have h := lintegral_mul_left_eq_self (μ := μ) (fun x => w ((ι u)⁻¹ * x) * ψ x) (ι u)
    simp only [inv_mul_cancel_left] at h
    exact h
  have hpt : ∀ h : G, ∑' γ : Γ, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁ =
      ∑' q, ψ (r q * h) := by
    intro h
    let E := Equiv.ofBijective _ (bijective_pair ι hι Γ Γ₁ hΓ r hr hQ)
    let F : G → ℝ≥0∞ := fun x => ψ x * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * x) ∂μ₁
    calc ∑' γ : Γ, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁
        = ∑' p : Q × Γ₁, F (E p • h) := (E.tsum_eq (fun γ => F (γ • h))).symm
      _ = ∑' q, ∑' v : Γ₁, F (E (q, v) • h) := ENNReal.tsum_prod (f := fun q v => F (E (q, v) • h))
      _ = ∑' q, ψ (r q * h) * ∑' v : Γ₁, ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (ι (v : G₁)⁻¹ * (r q * h))) ∂μ₁ := by
          refine tsum_congr fun q => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun v => ?_
          show ψ ((ι (v : G₁)⁻¹ * r q) * h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * ((ι (v : G₁)⁻¹ * r q) * h)) ∂μ₁ = _
          rw [mul_assoc, hinv _ (Γ₁.inv_mem v.2)]
      _ = ∑' q, ψ (r q * h) := by simp only [hsumW, mul_one]
  symm
  calc ∫⁻ g, w g * ∫⁻ u in 𝓕₁, ψ (ι u * g) ∂μ₁ ∂μ
      = ∫⁻ g, ∫⁻ u in 𝓕₁, w g * ψ (ι u * g) ∂μ₁ ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul (w g) (f := fun u => ψ (ι u * g)) (hψ.comp (hιm.mul_const g))]
    _ = ∫⁻ u in 𝓕₁, ∫⁻ g, w g * ψ (ι u * g) ∂μ ∂μ₁ :=
        lintegral_lintegral_swap ((hw.comp measurable_fst).mul (hψ.comp hm1)).aemeasurable
    _ = ∫⁻ u in 𝓕₁, ∫⁻ g, w ((ι u)⁻¹ * g) * ψ g ∂μ ∂μ₁ := lintegral_congr fun u => key u
    _ = ∫⁻ g, ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) * ψ g ∂μ₁ ∂μ :=
        lintegral_lintegral_swap ((hw.comp hm2).mul (hψ.comp measurable_snd)).aemeasurable
    _ = ∫⁻ g, ψ g * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) ∂μ₁ ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const (ψ g) (f := fun u => w ((ι u)⁻¹ * g)) (hw.comp (hιm.inv.mul_const g))]
        exact mul_comm _ _
    _ = ∑' γ : Γ, ∫⁻ h in 𝓕, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁ ∂μ :=
        h𝓕.lintegral_eq_tsum'' _
    _ = ∫⁻ h in 𝓕, ∑' γ : Γ, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁ ∂μ :=
        (lintegral_tsum fun γ : Γ => (hFm.comp (measurable_const_mul (γ : G))).aemeasurable).symm
    _ = ∫⁻ h in 𝓕, ∑' q, ψ (r q * h) ∂μ := lintegral_congr fun h => hpt h
end GlobalTheory.CompanionTheory.SW.Averaging
