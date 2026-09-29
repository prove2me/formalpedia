-- Prove2me | solution 1 for NumberField.setLIntegral_comp_idelicNorm_fundamentalDomain_eq_measure_mul_lintegral_haarQuotient_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a908bdd9-bc1b-54ba-8abd-5c1723679345

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_measurable_lintegral_mul_out
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_setLIntegral_comp_idelicNorm_fundamentalDomain_eq_measure_mul_lintegral_haarQuotient_ker
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal Pointwise

namespace StagesSol

theorem secondCountableTopology_units (M : Type*) [Monoid M] [TopologicalSpace M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem countable_units (F : Type*) [Field F] [NumberField F] : Countable Fˣ := by
  haveI : Countable F :=
    Countable.of_equiv _ (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.symm
  exact Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective

section Norm

variable {R E S F : Type*} [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E] [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F] [IsFractionRing S F]
  [Algebra E F]

theorem adelicNorm_algebraMap_algEquiv (B : M4aHerbrand.AdeleBaseChange R E S F) (σ : F ≃ₐ[E] F)
    (x : F) :
    B.adelicNorm (algebraMap F (AdeleRing S F) (σ x)) = B.adelicNorm (algebraMap F (AdeleRing S F) x) := by
  letI := B.β.toAlgebra
  rw [← M4aHerbrand.actOf_algebraMap R E S F B.tensorEquiv B.tensorEquiv_one_tmul σ x]
  exact Algebra.norm_eq_of_algEquiv
    (B.tensorEquiv.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans B.tensorEquiv))
    (algebraMap F (AdeleRing S F) x)

theorem range_le_ker_idelicNorm (B : M4aHerbrand.AdeleBaseChange R E S F) (σ : F ≃ₐ[E] F) :
    ((Units.map (algebraMap F (AdeleRing S F) : F →* AdeleRing S F)).comp
        (Units.map ((σ : F →+* F) : F →* F) / MonoidHom.id Fˣ)).range ≤ B.idelicNorm.ker := by
  rintro _ ⟨w, rfl⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.id_apply, map_div,
    map_div, div_eq_one]
  ext
  simp only [M4aHerbrand.AdeleBaseChange.idelicNorm, Units.coe_map, MonoidHom.coe_coe]
  exact adelicNorm_algebraMap_algEquiv B σ (w : F)

end Norm

section Core

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (N : Subgroup G) (hNc : IsClosed (N : Set G))
  (μN : Measure N) [μN.IsHaarMeasure]

def slice (Θ : Set G) (w : G) : Set N := {n : N | (n : G) * w ∈ Θ}

omit hNc in
omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem measurableSet_slice {Θ : Set G} (hΘ : MeasurableSet Θ) (w : G) : MeasurableSet (slice N Θ w) :=
  (continuous_subtype_val.mul continuous_const).measurable hΘ

omit hNc in
omit [LocallyCompactSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [BorelSpace G]
  [TopologicalSpace G] in

theorem measurable_comp_out {β : Type*} [MeasurableSpace β] (F : G → β) (hF : Measurable F)
    (hFinv : ∀ (n : N) (x : G), F ((n : G) * x) = F x) :
    Measurable (fun q : MulAction.orbitRel.Quotient N G => F q.out) := by
  rw [measurable_from_quotient]
  have : ((fun q : MulAction.orbitRel.Quotient N G => F q.out) ∘ Quotient.mk'') = F := by
    funext w
    simp only [Function.comp_apply]
    have hrel : (MulAction.orbitRel N G) ((Quotient.mk'' w : MulAction.orbitRel.Quotient N G).out) w :=
      Quotient.exact (Quotient.out_eq _)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨n, hn⟩ := hrel
    rw [← hn, Subgroup.smul_def, smul_eq_mul, hFinv]
  rw [this]
  exact hF

include hNc in

theorem measure_eq_lintegral_slice {B : Set G} (hB : MeasurableSet B) :
    μ B = ∫⁻ q, μN (slice N B q.out) ∂(HaarQuotient.measure μ N μN) := by
  have h := HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ N hNc μN (B.indicator 1)
    (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB] at h
  rw [h]
  refine lintegral_congr fun q => ?_
  rw [← lintegral_indicator_one (measurableSet_slice N hB q.out)]
  rfl

include hNc in

theorem ae_measure_slice_eq_zero {B : Set G} (hB : MeasurableSet B) (hB0 : μ B = 0) :
    ∀ᵐ q ∂(HaarQuotient.measure μ N μN), μN (slice N B q.out) = 0 := by
  have hmeas : Measurable fun q : MulAction.orbitRel.Quotient N G => μN (slice N B q.out) := by
    have := HaarQuotient.measurable_lintegral_mul_out N hNc μN (B.indicator 1) (measurable_one.indicator hB)
    have hfun : (fun q : MulAction.orbitRel.Quotient N G => ∫⁻ x : N, B.indicator 1 ((x : G) * q.out) ∂μN) =
        fun q => μN (slice N B q.out) := by
      funext q
      rw [← lintegral_indicator_one (measurableSet_slice N hB q.out)]
      rfl
    rw [hfun] at this
    exact this
  have h := measure_eq_lintegral_slice μ N hNc μN hB
  rw [hB0, eq_comm, lintegral_eq_zero_iff hmeas] at h
  exact h

omit hNc in
omit [LocallyCompactSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [BorelSpace G]
  [TopologicalSpace G] [MeasurableSpace G] in

theorem slice_smul (Θ : Set G) (w : G) (γ : N) :
    slice N (((γ : G)) • Θ) w = γ • slice N Θ w := by
  ext n
  simp only [slice, Set.mem_setOf_eq]
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, smul_eq_mul,
    Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]

include hNc in

theorem core (Γ : Subgroup G) [Countable Γ] (hΓ : Γ ≤ N)
    (Θ : Set G) (hΘm : MeasurableSet Θ)
    (hcov : ∀ᵐ x ∂μ, ∃ γ : Γ, γ • x ∈ Θ)
    (hdisj : ∀ γ γ' : Γ, γ ≠ γ' → μ (((γ : G)) • Θ ∩ ((γ' : G)) • Θ) = 0)
    (Θ₁ : Set N) (hΘ₁ : IsFundamentalDomain (Γ.subgroupOf N) Θ₁ μN)
    (F : G → ℝ≥0∞) (hF : Measurable F) (hFinv : ∀ (n : N) (x : G), F ((n : G) * x) = F x) :
    ∫⁻ z in Θ, F z ∂μ = μN Θ₁ * ∫⁻ q, F q.out ∂(HaarQuotient.measure μ N μN) := by
  classical

  let toN : Γ → Γ.subgroupOf N := fun γ =>
    ⟨⟨(γ : G), hΓ γ.2⟩, Subgroup.mem_subgroupOf.2 (by simpa using γ.2)⟩
  have toN_coe : ∀ γ : Γ, (((toN γ) : N) : G) = (γ : G) := fun γ => rfl
  have toN_surj : Function.Surjective toN := by
    intro δ
    refine ⟨⟨((δ : N) : G), Subgroup.mem_subgroupOf.1 δ.2⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; rfl
  haveI : Countable (Γ.subgroupOf N) := toN_surj.countable

  have smul_slice : ∀ (δ : Γ.subgroupOf N) (w : G),
      δ • slice N Θ w = slice N ((((δ : N) : G)) • Θ) w := by
    intro δ w
    rw [slice_smul, Subgroup.smul_def]

  have h1 : ∫⁻ z in Θ, F z ∂μ =
      ∫⁻ q, F q.out * μN (slice N Θ q.out) ∂(HaarQuotient.measure μ N μN) := by
    rw [← lintegral_indicator hΘm,
      HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ N hNc μN (Θ.indicator F) (hF.indicator hΘm)]
    refine lintegral_congr fun q => ?_
    have hind : (fun x : N => Θ.indicator F ((x : G) * q.out)) =
        (slice N Θ q.out).indicator (fun _ => F q.out) := by
      funext x
      by_cases hx : (x : G) * q.out ∈ Θ
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ slice N Θ q.out from hx), hFinv]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ slice N Θ q.out from hx)]
    rw [hind, lintegral_indicator_const (measurableSet_slice N hΘm q.out)]

  have hcovN : ∀ᵐ q ∂(HaarQuotient.measure μ N μN),
      ∀ᵐ n ∂μN, ∃ δ : Γ.subgroupOf N, δ • n ∈ slice N Θ q.out := by
    have hBadm : MeasurableSet {x : G | ¬ ∃ γ : Γ, γ • x ∈ Θ} := by
      have : {x : G | ¬ ∃ γ : Γ, γ • x ∈ Θ} = (⋃ γ : Γ, (fun x : G => (γ : G) * x) ⁻¹' Θ)ᶜ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage,
          Subgroup.smul_def, smul_eq_mul]
      rw [this]
      exact (MeasurableSet.iUnion fun γ => (continuous_const.mul continuous_id).measurable hΘm).compl
    have hBad0 : μ {x : G | ¬ ∃ γ : Γ, γ • x ∈ Θ} = 0 := ae_iff.1 hcov
    have h := ae_measure_slice_eq_zero μ N hNc μN hBadm hBad0
    refine h.mono fun q hq => ?_
    have hq' := measure_eq_zero_iff_ae_notMem.1 hq
    refine hq'.mono fun n hn => ?_
    simp only [slice, Set.mem_setOf_eq, not_not] at hn
    obtain ⟨γ, hγ⟩ := hn
    refine ⟨toN γ, ?_⟩
    show (((toN γ • n : N)) : G) * q.out ∈ Θ
    rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, toN_coe, mul_assoc]
    simpa [Subgroup.smul_def, smul_eq_mul] using hγ

  have hdisjN : ∀ᵐ q ∂(HaarQuotient.measure μ N μN),
      ∀ p : Γ.subgroupOf N × Γ.subgroupOf N, p.1 ≠ p.2 →
        μN (p.1 • slice N Θ q.out ∩ p.2 • slice N Θ q.out) = 0 := by
    rw [ae_all_iff]
    rintro ⟨δ, δ'⟩
    by_cases hδ : δ = δ'
    · exact Filter.Eventually.of_forall fun q h => (h hδ).elim
    · have hne : (⟨((δ : N) : G), Subgroup.mem_subgroupOf.1 δ.2⟩ : Γ) ≠
          ⟨((δ' : N) : G), Subgroup.mem_subgroupOf.1 δ'.2⟩ := by
        intro h
        apply hδ
        have : ((δ : N) : G) = ((δ' : N) : G) := congrArg (fun γ : Γ => (γ : G)) h
        exact Subtype.ext (Subtype.ext this)
      have hB0 := hdisj _ _ hne
      have hBm : MeasurableSet ((((δ : N) : G)) • Θ ∩ (((δ' : N) : G)) • Θ) :=
        (hΘm.const_smul _).inter (hΘm.const_smul _)
      have h := ae_measure_slice_eq_zero μ N hNc μN hBm hB0
      refine h.mono fun q hq _ => ?_
      rw [smul_slice, smul_slice]
      convert hq using 2
      exact Set.ext fun _ => Iff.rfl

  have hmeasΘ₁ : ∀ᵐ q ∂(HaarQuotient.measure μ N μN), μN (slice N Θ q.out) = μN Θ₁ := by
    filter_upwards [hcovN, hdisjN] with q hc hd
    have hfd : IsFundamentalDomain (Γ.subgroupOf N) (slice N Θ q.out) μN :=
      { nullMeasurableSet := (measurableSet_slice N hΘm q.out).nullMeasurableSet
        ae_covers := hc
        aedisjoint := fun δ δ' hne => by
          show μN (δ • slice N Θ q.out ∩ δ' • slice N Θ q.out) = 0
          exact hd (δ, δ') hne }
    exact hfd.measure_eq hΘ₁

  rw [h1]
  calc ∫⁻ q, F q.out * μN (slice N Θ q.out) ∂(HaarQuotient.measure μ N μN)
      = ∫⁻ q, F q.out * μN Θ₁ ∂(HaarQuotient.measure μ N μN) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hmeasΘ₁] with q hq
        rw [hq]
    _ = (∫⁻ q, F q.out ∂(HaarQuotient.measure μ N μN)) * μN Θ₁ :=
        lintegral_mul_const _ (measurable_comp_out N F hF hFinv)
    _ = μN Θ₁ * ∫⁻ q, F q.out ∂(HaarQuotient.measure μ N μN) := mul_comm _ _

include hNc in

theorem core' (Γ : Subgroup G) [Countable Γ] (hΓ : Γ ≤ N)
    (Θ : Set G) (hΘ : IsFundamentalDomain Γ Θ μ)
    (Θ₁ : Set N) (hΘ₁ : IsFundamentalDomain (Γ.subgroupOf N) Θ₁ μN)
    (F : G → ℝ≥0∞) (hF : Measurable F) (hFinv : ∀ (n : N) (x : G), F ((n : G) * x) = F x) :
    ∫⁻ z in Θ, F z ∂μ = μN Θ₁ * ∫⁻ q, F q.out ∂(HaarQuotient.measure μ N μN) := by
  obtain ⟨Θ', hsub, hΘ'm, hae⟩ := hΘ.nullMeasurableSet.exists_measurable_superset_ae_eq
  have hdiff : μ (Θ' \ Θ) = 0 := (ae_eq_set.1 hae).1
  rw [← setLIntegral_congr hae]
  refine core μ N hNc μN Γ hΓ Θ' hΘ'm ?_ ?_ Θ₁ hΘ₁ F hF hFinv
  · exact hΘ.ae_covers.mono fun x ⟨γ, hγ⟩ => ⟨γ, hsub hγ⟩
  · intro γ γ' hne
    have h0 : μ (((γ : G)) • Θ ∩ ((γ' : G)) • Θ) = 0 := by
      have := hΘ.aedisjoint hne
      exact this
    have h1 : ∀ δ : Γ, μ (((δ : G)) • (Θ' \ Θ)) = 0 := fun δ => by
      rw [measure_smul]; exact hdiff
    have hsubset : ((γ : G)) • Θ' ∩ ((γ' : G)) • Θ' ⊆
        (((γ : G)) • Θ ∩ ((γ' : G)) • Θ) ∪ (((γ : G)) • (Θ' \ Θ) ∪ ((γ' : G)) • (Θ' \ Θ)) := by
      intro x hx
      rw [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem] at hx
      by_cases h1x : (γ : G)⁻¹ • x ∈ Θ
      · by_cases h2x : (γ' : G)⁻¹ • x ∈ Θ
        · left
          exact ⟨Set.mem_smul_set_iff_inv_smul_mem.2 h1x, Set.mem_smul_set_iff_inv_smul_mem.2 h2x⟩
        · right; right
          exact Set.mem_smul_set_iff_inv_smul_mem.2 ⟨hx.2, h2x⟩
      · right; left
        exact Set.mem_smul_set_iff_inv_smul_mem.2 ⟨hx.1, h1x⟩
    refine measure_mono_null hsubset ?_
    exact measure_union_null h0 (measure_union_null (h1 γ) (h1 γ'))

end Core

section Target

variable {α β γT : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γT]

theorem map_eq_smul_map_of_forall_lintegral {μ : Measure α} {Q : Measure β} {f : α → γT} {fb : β → γT}
    (hf : Measurable f) (hfb : Measurable fb) (c : ℝ≥0∞)
    (h : ∀ g : γT → ℝ≥0∞, Measurable g → ∫⁻ a, g (f a) ∂μ = c * ∫⁻ b, g (fb b) ∂Q) :
    Measure.map f μ = c • Measure.map fb Q := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg hf, lintegral_smul_measure, lintegral_map hg hfb, h g hg, smul_eq_mul]

theorem integrable_iff_of_map_eq_smul {μ : Measure α} {Q : Measure β} {f : α → γT} {fb : β → γT}
    (hf : Measurable f) (hfb : Measurable fb) {c : ℝ≥0∞} (hc : c < ∞)
    (h : Measure.map f μ = c • Measure.map fb Q) (g : γT → ℂ) (hg : Measurable g) :
    Integrable (fun a => g (f a)) μ ↔ (c = 0 ∨ Integrable (fun b => g (fb b)) Q) := by
  have h1 : Integrable (fun a => g (f a)) μ ↔ Integrable g (Measure.map f μ) :=
    (integrable_map_measure hg.aestronglyMeasurable hf.aemeasurable).symm
  have h2 : Integrable (fun b => g (fb b)) Q ↔ Integrable g (Measure.map fb Q) :=
    (integrable_map_measure hg.aestronglyMeasurable hfb.aemeasurable).symm
  rw [h1, h2, h]
  by_cases hc0 : c = 0
  · simp only [hc0, zero_smul, true_or, iff_true]
    exact integrable_zero_measure
  · rw [integrable_smul_measure hc0 hc.ne]
    simp [hc0]

theorem integral_eq_of_map_eq_smul {μ : Measure α} {Q : Measure β} {f : α → γT} {fb : β → γT}
    (hf : Measurable f) (hfb : Measurable fb) {c : ℝ≥0∞}
    (h : Measure.map f μ = c • Measure.map fb Q) (g : γT → ℂ) (hg : Measurable g) :
    ∫ a, g (f a) ∂μ = c.toReal * ∫ b, g (fb b) ∂Q := by
  rw [← integral_map hf.aemeasurable hg.aestronglyMeasurable, h, integral_smul_measure,
    integral_map hfb.aemeasurable hg.aestronglyMeasurable, Complex.real_smul]

end Target

end StagesSol

open StagesSol in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (Θ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΘ : IsFundamentalDomain
      ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range Θ νZL)
    (Θ₁ : Set N1)
    (hΘ₁ : IsFundamentalDomain
      ((((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
        (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range).subgroupOf N1) Θ₁ μN) :
    (∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
        μN Θ₁ *
          ∫⁻ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN)) ∧
    (μN Θ₁ < ∞ →
      ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
        (IntegrableOn (fun z => g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) Θ νZL ↔
          (μN Θ₁ = 0 ∨
            Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
              g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)))
              (HaarQuotient.measure νZL N1 μN))) ∧
        ∫ z in Θ, g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) ∂νZL =
          (μN Θ₁).toReal *
            ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
              g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
              ∂(HaarQuotient.measure νZL N1 μN)) := by
  set B := M4aHerbrand.GenuineDescent.genuineBaseChange K L with hB
  set Γ : Subgroup (AdeleRing (𝓞 L) L)ˣ :=
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).comp
      (Units.map ((σ : L →+* L) : L →* L) / MonoidHom.id Lˣ)).range with hΓ

  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_units (AdeleRing (𝓞 L) L)

  have hNc : Continuous B.idelicNorm :=
    Continuous.units_map B.adelicNorm
      (M4aHerbrand.GenuineDescent.continuous_adelicNorm_genuineBaseChange K L)
  have hNm : Measurable B.idelicNorm := hNc.measurable
  have hinv : ∀ (n : N1) (x : (AdeleRing (𝓞 L) L)ˣ), B.idelicNorm ((n : (AdeleRing (𝓞 L) L)ˣ) * x) =
      B.idelicNorm x := fun n x => by
    rw [map_mul, (hN1 n).1 n.2, one_mul]
  have hFm : Measurable (fun q : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ => B.idelicNorm q.out) :=
    measurable_comp_out N1 B.idelicNorm hNm hinv

  haveI : Countable Lˣ := countable_units L
  haveI : Countable Γ := Function.Surjective.countable (MonoidHom.rangeRestrict_surjective _)
  have hΓN : Γ ≤ N1 := fun γ hγ => (hN1 γ).2 (by
    have := range_le_ker_idelicNorm B σ hγ
    rwa [MonoidHom.mem_ker] at this)

  have hmain : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable g →
      ∫⁻ z in Θ, g (B.idelicNorm z) ∂νZL =
        μN Θ₁ * ∫⁻ q, g (B.idelicNorm q.out) ∂(HaarQuotient.measure νZL N1 μN) := fun g hg =>
    core' νZL N1 hN1c μN Γ hΓN Θ hΘ Θ₁ hΘ₁ (fun z => g (B.idelicNorm z)) (hg.comp hNm)
      (fun n x => by simp only [hinv])
  refine ⟨hmain, fun hfin g hg => ?_⟩

  have hmap : Measure.map B.idelicNorm (νZL.restrict Θ) =
      μN Θ₁ • Measure.map (fun q : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ => B.idelicNorm q.out)
        (HaarQuotient.measure νZL N1 μN) :=
    map_eq_smul_map_of_forall_lintegral hNm hFm (μN Θ₁) hmain
  exact ⟨integrable_iff_of_map_eq_smul hNm hFm hfin hmap g hg, integral_eq_of_map_eq_smul hNm hFm hmap g hg⟩

end S_NumberField_setLIntegral_comp_idelicNorm_fundamentalDomain_eq_measure_mul_lintegral_haarQuotient_ker
end P2MW
export P2MW.S_NumberField_setLIntegral_comp_idelicNorm_fundamentalDomain_eq_measure_mul_lintegral_haarQuotient_ker (solution)
