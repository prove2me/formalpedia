-- Prove2me | solution 1 for MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5f60eeee-4123-5b2b-992d-dc42b39a933f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives

set_option autoImplicit false

open MeasureTheory Function
open scoped Pointwise ENNReal

namespace RS11C1B

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [MeasurableSpace G] [MeasurableSMul G X]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

theorem subgroup_smul_set (Γ : Subgroup G) (γ : Γ) (s : Set X) : γ • s = (γ : G) • s := rfl

theorem setLIntegral_smul_set (g : G) (s : Set X) (f : X → ℝ≥0∞) :
    ∫⁻ x in g • s, f x ∂μ = ∫⁻ x in s, f (g • x) ∂μ := by
  have he : MeasurePreserving (MeasurableEquiv.smul g : X ≃ᵐ X) μ μ := measurePreserving_smul g μ
  rw [← he.setLIntegral_comp_preimage_emb (MeasurableEquiv.smul g).measurableEmbedding]
  congr 1
  show μ.restrict ((fun x => g • x) ⁻¹' (g • s)) = μ.restrict s
  rw [Set.preimage_smul, inv_smul_smul]

theorem setIntegral_smul_set {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : G) (s : Set X) (f : X → E) :
    ∫ x in g • s, f x ∂μ = ∫ x in s, f (g • x) ∂μ := by
  have he : MeasurePreserving (MeasurableEquiv.smul g : X ≃ᵐ X) μ μ := measurePreserving_smul g μ
  rw [← he.setIntegral_preimage_emb (MeasurableEquiv.smul g).measurableEmbedding]
  congr 1
  show μ.restrict ((fun x => g • x) ⁻¹' (g • s)) = μ.restrict s
  rw [Set.preimage_smul, inv_smul_smul]

end RS11C1B

theorem solution
    {G X ι : Type*} [Group G] [MulAction G X] [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (Γ₁ Γ₂ : Subgroup G) (hle : Γ₂ ≤ Γ₁) [Countable Γ₁]
    [MeasurableSpace G] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
    (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ₁ 𝓕 μ)
    (R : ι → Γ₁) (hR : ∀ γ : Γ₁, ∃! i, ((R i)⁻¹ * γ : G) ∈ Γ₂) :
    (∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, f x ∂μ = ∫⁻ x in 𝓕, ∑' i, f ((R i : G)⁻¹ • x) ∂μ) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (h : X → E),
      AEStronglyMeasurable h μ →
      ∫⁻ x in 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ < ∞ →
      IntegrableOn h (⋃ i, ((R i : G)⁻¹) • 𝓕) μ ∧
      (∀ᵐ x ∂μ.restrict 𝓕, Summable fun i => ‖h ((R i : G)⁻¹ • x)‖) ∧
      ∫ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, h x ∂μ = ∫ x in 𝓕, ∑' i, h ((R i : G)⁻¹ • x) ∂μ := by
  classical

  have hnull : ∀ i, NullMeasurableSet (((R i : G)⁻¹) • 𝓕) μ := by
    intro i
    have h := h𝓕.nullMeasurableSet_smul (R i)⁻¹
    rwa [RS11C1B.subgroup_smul_set, Subgroup.coe_inv] at h
  have hdist : ∀ i j, i ≠ j → ((R i)⁻¹ : Γ₁) ≠ (R j)⁻¹ := by
    intro i j hij heq
    apply hij
    have hRi : R i = R j := inv_injective heq
    obtain ⟨k, -, hk⟩ := hR (R i)
    have hii : ((R i)⁻¹ * R i : G) ∈ Γ₂ := by rw [Subgroup.coe_inv, inv_mul_cancel]; exact one_mem _
    have hji : ((R j)⁻¹ * R i : G) ∈ Γ₂ := by rw [← hRi, Subgroup.coe_inv, inv_mul_cancel]; exact one_mem _
    exact (hk i hii).trans (hk j hji).symm
  have hdisj : Pairwise (AEDisjoint μ on fun i => ((R i : G)⁻¹) • 𝓕) := by
    intro i j hij
    have h := h𝓕.aedisjoint (hdist i j hij)
    simpa only [Function.onFun, RS11C1B.subgroup_smul_set, Subgroup.coe_inv] using h
  have hmp : ∀ i, MeasurePreserving (fun x : X => (R i : G)⁻¹ • x) μ μ := fun i => measurePreserving_smul _ μ
  refine ⟨fun f hf => ?_, ?_⟩
  ·
    have hfm : ∀ i, AEMeasurable (fun x => f ((R i : G)⁻¹ • x)) (μ.restrict 𝓕) := fun i =>
      ((hf.comp (measurable_const_smul ((R i : G)⁻¹)) : Measurable fun x => f ((R i : G)⁻¹ • x))).aemeasurable
    rw [lintegral_iUnion₀ hnull hdisj, lintegral_tsum hfm]
    exact tsum_congr fun i => RS11C1B.setLIntegral_smul_set μ _ _ _
  · intro E _ _ _ h hh hfin
    have hae : ∀ i, AEStronglyMeasurable (fun x => h ((R i : G)⁻¹ • x)) (μ.restrict 𝓕) := fun i =>
      (hh.comp_measurePreserving (hmp i)).restrict

    have hnorm : ∫⁻ x in ⋃ i, ((R i : G)⁻¹) • 𝓕, ‖h x‖ₑ ∂μ = ∫⁻ x in 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ := by
      rw [lintegral_iUnion₀ hnull hdisj, lintegral_tsum fun i => (hae i).enorm]
      exact tsum_congr fun i => RS11C1B.setLIntegral_smul_set μ _ _ _
    have hint : IntegrableOn h (⋃ i, ((R i : G)⁻¹) • 𝓕) μ :=
      ⟨hh.restrict, by rw [HasFiniteIntegral, hnorm]; exact hfin⟩
    refine ⟨hint, ?_, ?_⟩
    ·
      have hlt : ∀ᵐ x ∂μ.restrict 𝓕, ∑' i, ‖h ((R i : G)⁻¹ • x)‖ₑ < ∞ :=
        ae_lt_top' (AEMeasurable.ennreal_tsum fun i => (hae i).enorm) hfin.ne
      filter_upwards [hlt] with x hx
      have hx' : ∑' i, (‖h ((R i : G)⁻¹ • x)‖₊ : ℝ≥0∞) ≠ ∞ := by
        simpa only [enorm_eq_nnnorm] using hx.ne
      have hs := ENNReal.tsum_coe_ne_top_iff_summable.mp hx'
      exact (NNReal.summable_coe.mpr hs)
    ·
      rw [integral_iUnion_ae hnull hdisj hint]
      have hfin' : ∑' i, ∫⁻ x, ‖h ((R i : G)⁻¹ • x)‖ₑ ∂μ.restrict 𝓕 ≠ ∞ := by
        rw [← lintegral_tsum fun i => (hae i).enorm]
        exact hfin.ne
      rw [integral_tsum hae hfin']
      exact tsum_congr fun i => RS11C1B.setIntegral_smul_set μ _ _ _

end S_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
end P2MW
export P2MW.S_MeasureTheory_IsFundamentalDomain_setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives (solution)
