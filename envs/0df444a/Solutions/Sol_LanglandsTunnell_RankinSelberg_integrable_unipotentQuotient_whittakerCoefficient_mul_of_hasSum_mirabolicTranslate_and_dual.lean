-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.integrable_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/237a8147-0c42-5aa4-8ec5-61e8446e9360

import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_LanglandsTunnell_CubicInduction_setLIntegral_eq_setLIntegral_tsum_mirabolicRep
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_setLIntegral_adelicGLHaar_eq_lintegral_unipotentQuotientMeasure
import Theorems.Thm_AutomorphicForm_measurable_lintegral_unipotentGL2_mul_out
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_integrable_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

namespace Ws23J3Int
namespace RSU

section FibreTransfer

open MeasureTheory ENNReal

theorem integral_eq_smul_integral_integral_of_forall_lintegral_eq
    {α : Type} [MeasurableSpace α] (m : Measure α)
    {Q : Type} [MeasurableSpace Q] (μQ : Measure Q)
    {T : Type} [MeasurableSpace T] (ν : Measure T)
    (Θ : T → Q → α) (hΘ : ∀ q, Measurable fun t => Θ t q)
    (P : (α → ℝ≥0∞) → Prop) (c : ℝ≥0∞) (hc0 : c ≠ 0)
    (hD2 : ∀ h : α → ℝ≥0∞, Measurable h → P h →
      Measurable (fun q => ∫⁻ t, h (Θ t q) ∂ν) ∧
        ∫⁻ x, h x ∂m = c * ∫⁻ q, ∫⁻ t, h (Θ t q) ∂ν ∂μQ)
    (f : α → ℂ) (hf : Measurable f)
    (hP : ∀ k : ℂ → ℝ≥0∞, Measurable k → P (fun x => k (f x)))
    (hfin : ∫⁻ x, ‖f x‖ₑ ∂m < ∞) :
    Integrable (fun q => ∫ t, f (Θ t q) ∂ν) μQ ∧
      ∫ x, f x ∂m = c.toReal • ∫ q, ∫ t, f (Θ t q) ∂ν ∂μQ := by

  have hk₀ : Measurable fun z : ℂ => ‖z‖ₑ := measurable_enorm
  have hk₁ : Measurable fun z : ℂ => ENNReal.ofReal (RCLike.re z) :=
    ENNReal.measurable_ofReal.comp RCLike.measurable_re
  have hk₂ : Measurable fun z : ℂ => ENNReal.ofReal (-RCLike.re z) :=
    ENNReal.measurable_ofReal.comp RCLike.measurable_re.neg
  have hk₃ : Measurable fun z : ℂ => ENNReal.ofReal (RCLike.im z) :=
    ENNReal.measurable_ofReal.comp RCLike.measurable_im
  have hk₄ : Measurable fun z : ℂ => ENNReal.ofReal (-RCLike.im z) :=
    ENNReal.measurable_ofReal.comp RCLike.measurable_im.neg
  obtain ⟨M₀, I₀⟩ := hD2 (fun x => ‖f x‖ₑ) (hk₀.comp hf) (hP _ hk₀)
  obtain ⟨M₁, I₁⟩ := hD2 (fun x => ENNReal.ofReal (RCLike.re (f x))) (hk₁.comp hf) (hP _ hk₁)
  obtain ⟨M₂, I₂⟩ := hD2 (fun x => ENNReal.ofReal (-RCLike.re (f x))) (hk₂.comp hf) (hP _ hk₂)
  obtain ⟨M₃, I₃⟩ := hD2 (fun x => ENNReal.ofReal (RCLike.im (f x))) (hk₃.comp hf) (hP _ hk₃)
  obtain ⟨M₄, I₄⟩ := hD2 (fun x => ENNReal.ofReal (-RCLike.im (f x))) (hk₄.comp hf) (hP _ hk₄)

  set Λ₀ : Q → ℝ≥0∞ := fun q => ∫⁻ t, ‖f (Θ t q)‖ₑ ∂ν
  set Λ₁ : Q → ℝ≥0∞ := fun q => ∫⁻ t, ENNReal.ofReal (RCLike.re (f (Θ t q))) ∂ν
  set Λ₂ : Q → ℝ≥0∞ := fun q => ∫⁻ t, ENNReal.ofReal (-RCLike.re (f (Θ t q))) ∂ν
  set Λ₃ : Q → ℝ≥0∞ := fun q => ∫⁻ t, ENNReal.ofReal (RCLike.im (f (Θ t q))) ∂ν
  set Λ₄ : Q → ℝ≥0∞ := fun q => ∫⁻ t, ENNReal.ofReal (-RCLike.im (f (Θ t q))) ∂ν

  have hb₁ : ∀ z : ℂ, ENNReal.ofReal (RCLike.re z) ≤ ‖z‖ₑ := fun z => by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm z)
  have hb₂ : ∀ z : ℂ, ENNReal.ofReal (-RCLike.re z) ≤ ‖z‖ₑ := fun z => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (RCLike.abs_re_le_norm z))
  have hb₃ : ∀ z : ℂ, ENNReal.ofReal (RCLike.im z) ≤ ‖z‖ₑ := fun z => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (RCLike.abs_im_le_norm z))
  have hb₄ : ∀ z : ℂ, ENNReal.ofReal (-RCLike.im z) ≤ ‖z‖ₑ := fun z => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (RCLike.abs_im_le_norm z))
  have hΛ₁le : Λ₁ ≤ Λ₀ := fun q => lintegral_mono fun t => hb₁ _
  have hΛ₂le : Λ₂ ≤ Λ₀ := fun q => lintegral_mono fun t => hb₂ _
  have hΛ₃le : Λ₃ ≤ Λ₀ := fun q => lintegral_mono fun t => hb₃ _
  have hΛ₄le : Λ₄ ≤ Λ₀ := fun q => lintegral_mono fun t => hb₄ _

  have hΛ₀fin : ∫⁻ q, Λ₀ q ∂μQ < ∞ :=
    ENNReal.lt_top_of_mul_ne_top_right (I₀ ▸ hfin.ne) hc0
  have hΛ₁fin : ∫⁻ q, Λ₁ q ∂μQ ≠ ∞ := ((lintegral_mono hΛ₁le).trans_lt hΛ₀fin).ne
  have hΛ₂fin : ∫⁻ q, Λ₂ q ∂μQ ≠ ∞ := ((lintegral_mono hΛ₂le).trans_lt hΛ₀fin).ne
  have hΛ₃fin : ∫⁻ q, Λ₃ q ∂μQ ≠ ∞ := ((lintegral_mono hΛ₃le).trans_lt hΛ₀fin).ne
  have hΛ₄fin : ∫⁻ q, Λ₄ q ∂μQ ≠ ∞ := ((lintegral_mono hΛ₄le).trans_lt hΛ₀fin).ne
  have hae₀ : ∀ᵐ q ∂μQ, Λ₀ q < ∞ := ae_lt_top M₀ hΛ₀fin.ne
  have hae₁ : ∀ᵐ q ∂μQ, Λ₁ q < ∞ := hae₀.mono fun q hq => (hΛ₁le q).trans_lt hq
  have hae₂ : ∀ᵐ q ∂μQ, Λ₂ q < ∞ := hae₀.mono fun q hq => (hΛ₂le q).trans_lt hq
  have hae₃ : ∀ᵐ q ∂μQ, Λ₃ q < ∞ := hae₀.mono fun q hq => (hΛ₃le q).trans_lt hq
  have hae₄ : ∀ᵐ q ∂μQ, Λ₄ q < ∞ := hae₀.mono fun q hq => (hΛ₄le q).trans_lt hq

  set R : Q → ℝ := fun q => (Λ₁ q).toReal - (Λ₂ q).toReal with hR
  set J : Q → ℝ := fun q => (Λ₃ q).toReal - (Λ₄ q).toReal with hJ
  have hRi : Integrable R μQ :=
    (integrable_toReal_of_lintegral_ne_top M₁.aemeasurable hΛ₁fin).sub
      (integrable_toReal_of_lintegral_ne_top M₂.aemeasurable hΛ₂fin)
  have hJi : Integrable J μQ :=
    (integrable_toReal_of_lintegral_ne_top M₃.aemeasurable hΛ₃fin).sub
      (integrable_toReal_of_lintegral_ne_top M₄.aemeasurable hΛ₄fin)

  set G : Q → ℂ := fun q =>
    (RCLike.ofReal (R q) : ℂ) + (RCLike.ofReal (J q) : ℂ) * (RCLike.I : ℂ)
  have hA : Integrable (fun q => (RCLike.ofReal (R q) : ℂ)) μQ := hRi.ofReal (𝕜 := ℂ)
  have hB : Integrable (fun q => (RCLike.ofReal (J q) : ℂ) * (RCLike.I : ℂ)) μQ :=
    (hJi.ofReal (𝕜 := ℂ)).mul_const _
  have hGi : Integrable G μQ := hA.add hB

  have hFG : (fun q => ∫ t, f (Θ t q) ∂ν) =ᵐ[μQ] G := by
    filter_upwards [hae₀] with q hq
    have hint : Integrable (fun t => f (Θ t q)) ν :=
      ⟨(hf.comp (hΘ q)).aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 hq⟩
    have hq' := integral_re_add_im hint
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint.re,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint.im] at hq'
    exact hq'.symm

  have hfm : Integrable f m := ⟨hf.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 hfin⟩
  have hre : ∫ x, RCLike.re (f x) ∂m = c.toReal * ∫ q, R q ∂μQ := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfm.re, I₁, I₂,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_sub, hR, integral_sub
        (integrable_toReal_of_lintegral_ne_top M₁.aemeasurable hΛ₁fin)
        (integrable_toReal_of_lintegral_ne_top M₂.aemeasurable hΛ₂fin),
      integral_toReal M₁.aemeasurable hae₁, integral_toReal M₂.aemeasurable hae₂]
  have him : ∫ x, RCLike.im (f x) ∂m = c.toReal * ∫ q, J q ∂μQ := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfm.im, I₃, I₄,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_sub, hJ, integral_sub
        (integrable_toReal_of_lintegral_ne_top M₃.aemeasurable hΛ₃fin)
        (integrable_toReal_of_lintegral_ne_top M₄.aemeasurable hΛ₄fin),
      integral_toReal M₃.aemeasurable hae₃, integral_toReal M₄.aemeasurable hae₄]
  have h1 : ∫ q, ∫ t, f (Θ t q) ∂ν ∂μQ = ∫ q, G q ∂μQ := integral_congr_ae hFG
  have h2 : ∫ q, G q ∂μQ =
      (RCLike.ofReal (∫ q, R q ∂μQ) : ℂ) + (RCLike.ofReal (∫ q, J q ∂μQ) : ℂ) * (RCLike.I : ℂ) :=
    calc ∫ q, G q ∂μQ
        = ∫ q, (RCLike.ofReal (R q) : ℂ) + (RCLike.ofReal (J q) : ℂ) * (RCLike.I : ℂ) ∂μQ := rfl
      _ = ∫ q, (RCLike.ofReal (R q) : ℂ) ∂μQ +
            ∫ q, (RCLike.ofReal (J q) : ℂ) * (RCLike.I : ℂ) ∂μQ := integral_add hA hB
      _ = (RCLike.ofReal (∫ q, R q ∂μQ) : ℂ) +
            (RCLike.ofReal (∫ q, J q ∂μQ) : ℂ) * (RCLike.I : ℂ) := by
          rw [integral_mul_const, integral_ofReal, integral_ofReal]
  have h3 : ∫ x, f x ∂m = (RCLike.ofReal (∫ x, RCLike.re (f x) ∂m) : ℂ) +
      (RCLike.ofReal (∫ x, RCLike.im (f x) ∂m) : ℂ) * (RCLike.I : ℂ) :=
    (integral_re_add_im hfm).symm
  refine ⟨hGi.congr hFG.symm, ?_⟩
  rw [h3, hre, him, h1, h2, RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

end FibreTransfer

section SumTransfer

open NumberField MeasureTheory AutomorphicForm

theorem setIntegral_eq_setIntegral_of_forall_setLIntegral_eq
    {G : Type} [MeasurableSpace G] (μ : Measure G) (DΓ DN : Set G)
    {ι : Type} [Countable ι] (L : ι → G → G) (hL : ∀ i, Measurable (L i))
    (P : (G → ENNReal) → Prop)
    (hD1 : ∀ h : G → ENNReal, Measurable h → P h →
      ∫⁻ g in DN, h g ∂μ = ∫⁻ g in DΓ, ∑' i : ι, h (L i g) ∂μ)
    (f : G → ℂ) (hf : Measurable f)
    (hP : ∀ r : ℂ → ENNReal, Measurable r → P (fun g => r (f g)))
    (Φf : G → ℂ) (hΦf : Measurable Φf)
    (hsum : ∀ g, HasSum (fun i : ι => f (L i g)) (Φf g))
    (hconv : ∫⁻ g in DΓ, ∑' i : ι, ‖f (L i g)‖ₑ ∂μ < ⊤) :
    IntegrableOn Φf DΓ μ ∧ IntegrableOn f DN μ ∧
      ∫ g in DΓ, Φf g ∂μ = ∫ g in DN, f g ∂μ := by
  have henorm : Measurable fun z : ℂ => ‖z‖ₑ := measurable_id.enorm
  have hmeas_i : ∀ i, Measurable fun g => f (L i g) := fun i => hf.comp (hL i)

  have hsum_side : ∀ r : ℂ → ENNReal, Measurable r →
      ∫⁻ g, r (f g) ∂(Measure.sum fun i : ι => (μ.restrict DΓ).map (L i)) =
        ∫⁻ g in DΓ, ∑' i : ι, r (f (L i g)) ∂μ := by
    intro r hr
    have hrf : Measurable fun g => r (f g) := hr.comp hf
    have hi : ∀ i, ∫⁻ g, r (f g) ∂((μ.restrict DΓ).map (L i)) = ∫⁻ g in DΓ, r (f (L i g)) ∂μ :=
      fun i => lintegral_map hrf (hL i)
    have hri : ∀ i, Measurable fun g => r (f (L i g)) := fun i => hr.comp (hmeas_i i)
    rw [lintegral_sum_measure]
    simp_rw [hi]
    exact (lintegral_tsum (f := fun i g => r (f (L i g))) fun i => (hri i).aemeasurable).symm

  have key : ∀ r : ℂ → ENNReal, Measurable r →
      ∫⁻ g, r (f g) ∂(μ.restrict DN) =
        ∫⁻ g, r (f g) ∂(Measure.sum fun i : ι => (μ.restrict DΓ).map (L i)) := by
    intro r hr
    rw [hsum_side r hr]
    exact hD1 _ (hr.comp hf) (hP r hr)

  have hint_sum : Integrable f (Measure.sum fun i : ι => (μ.restrict DΓ).map (L i)) := by
    refine ⟨hf.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 ?_⟩
    rw [hsum_side _ henorm]
    exact hconv
  have hint_DN : IntegrableOn f DN μ := by
    refine ⟨hf.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 ?_⟩
    rw [key _ henorm, hsum_side _ henorm]
    exact hconv

  have hint_DΓ : IntegrableOn Φf DΓ μ := by
    refine ⟨hΦf.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 (lt_of_le_of_lt ?_ hconv)⟩
    refine lintegral_mono fun g => ?_
    rw [← (hsum g).tsum_eq]
    exact enorm_tsum_le_tsum_enorm
  refine ⟨hint_DΓ, hint_DN, ?_⟩

  have hmap : (μ.restrict DN).map f =
      (Measure.sum fun i : ι => (μ.restrict DΓ).map (L i)).map f := by
    refine Measure.ext_of_lintegral _ fun r hr => ?_
    rw [lintegral_map hr hf, lintegral_map hr hf]
    exact key r hr
  have h_DN : ∫ g in DN, f g ∂μ = ∫ z, id z ∂((μ.restrict DN).map f) :=
    (integral_map hf.aemeasurable aestronglyMeasurable_id).symm
  have h_sum : ∫ g, f g ∂(Measure.sum fun i : ι => (μ.restrict DΓ).map (L i)) =
      ∫ z, id z ∂((Measure.sum fun i : ι => (μ.restrict DΓ).map (L i)).map f) :=
    (integral_map hf.aemeasurable aestronglyMeasurable_id).symm

  have h_unfold : ∫ g, f g ∂(Measure.sum fun i : ι => (μ.restrict DΓ).map (L i)) =
      ∫ g in DΓ, ∑' i : ι, f (L i g) ∂μ := by
    have hi : ∀ i, ∫ g, f g ∂((μ.restrict DΓ).map (L i)) = ∫ g in DΓ, f (L i g) ∂μ :=
      fun i => integral_map (hL i).aemeasurable hf.aestronglyMeasurable
    have hsm : ∀ i, AEStronglyMeasurable (fun g => f (L i g)) (μ.restrict DΓ) :=
      fun i => (hmeas_i i).aestronglyMeasurable
    have hne : ∑' i : ι, ∫⁻ g in DΓ, ‖f (L i g)‖ₑ ∂μ ≠ ⊤ := by
      rw [← lintegral_tsum (f := fun i g => ‖f (L i g)‖ₑ) fun i => (hmeas_i i).enorm.aemeasurable]
      exact hconv.ne
    rw [integral_sum_measure hint_sum]
    simp_rw [hi]
    exact (integral_tsum (f := fun i g => f (L i g)) hsm hne).symm
  have h_fold : ∫ g in DΓ, Φf g ∂μ = ∫ g in DΓ, ∑' i : ι, f (L i g) ∂μ :=
    integral_congr_ae (ae_of_all _ fun g => ((hsum g).tsum_eq).symm)
  rw [h_fold, ← h_unfold, h_sum, ← hmap, ← h_DN]

theorem globalPoints_unipotentGL2' (F : Type) [Field F] [NumberField F] (x : F) :
    globalPoints (𝓞 F) F (unipotentGL2 x) =
      unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints]

theorem setIntegral_mul_eq_setIntegral_whittaker_mul
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψK : ∀ x : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) x) = 1)
    [MeasurableSpace (AdelicGL2 (𝓞 F) F)] [MeasurableMul (AdelicGL2 (𝓞 F) F)]
    (μ : Measure (AdelicGL2 (𝓞 F) F))
    (DΓ DN : Set (AdelicGL2 (𝓞 F) F))
    (ι : Type) [Countable ι] (rep : ι → AdelicGL2 (𝓞 F) F)
    (hrep_mem : ∀ i, rep i ∈ (globalPoints (𝓞 F) F).range)
    (hD1 : ∀ h : AdelicGL2 (𝓞 F) F → ENNReal, Measurable h →
      (∀ (x : F) (g : AdelicGL2 (𝓞 F) F),
        h (globalPoints (𝓞 F) F (unipotentGL2 x) * g) = h g) →
      ∫⁻ g in DN, h g ∂μ = ∫⁻ g in DΓ, ∑' i : ι, h (rep i * g) ∂μ)
    (W₃ Φ : AdelicGL2 (𝓞 F) F → ℂ) (hW₃ : Measurable W₃) (hΦ : Measurable Φ)
    (hE1 : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      W₃ (unipotentGL2 x * g) = ψ x * W₃ g)
    (hE2 : ∀ g : AdelicGL2 (𝓞 F) F, HasSum (fun i : ι => W₃ (rep i * g)) (Φ g))
    (φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₂ : Measurable φ₂)
    (hG1 : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ₂ (globalPoints (𝓞 F) F γ * g) = φ₂ g)
    (hE3 : ∫⁻ g in DΓ,
      (∑' i : ι, (‖W₃ (rep i * g)‖₊ : ENNReal)) * (‖φ₂ g‖₊ : ENNReal) ∂μ < ⊤) :
    IntegrableOn (fun g => Φ g * φ₂ g) DΓ μ ∧
      IntegrableOn (fun g => W₃ g * φ₂ g) DN μ ∧
      ∫ g in DΓ, Φ g * φ₂ g ∂μ = ∫ g in DN, W₃ g * φ₂ g ∂μ := by

  have hφ₂_rep : ∀ (i : ι) (g : AdelicGL2 (𝓞 F) F), φ₂ (rep i * g) = φ₂ g := by
    intro i g
    obtain ⟨γ, hγ⟩ := hrep_mem i
    rw [← hγ, hG1]

  have hf_inv : ∀ (x : F) (g : AdelicGL2 (𝓞 F) F),
      W₃ (globalPoints (𝓞 F) F (unipotentGL2 x) * g) *
          φ₂ (globalPoints (𝓞 F) F (unipotentGL2 x) * g) = W₃ g * φ₂ g := by
    intro x g
    rw [hG1, globalPoints_unipotentGL2', hE1, hψK x, one_mul]

  have hterm : ∀ (i : ι) (g : AdelicGL2 (𝓞 F) F),
      W₃ (rep i * g) * φ₂ (rep i * g) = W₃ (rep i * g) * φ₂ g := by
    intro i g
    rw [hφ₂_rep]
  have hsum : ∀ g : AdelicGL2 (𝓞 F) F,
      HasSum (fun i : ι => W₃ (rep i * g) * φ₂ (rep i * g)) (Φ g * φ₂ g) := by
    intro g
    simp only [hterm]
    exact (hE2 g).mul_right (φ₂ g)
  have hconv : ∫⁻ g in DΓ, ∑' i : ι, ‖W₃ (rep i * g) * φ₂ (rep i * g)‖ₑ ∂μ < ⊤ := by
    simpa only [hterm, enorm_eq_nnnorm, nnnorm_mul, ENNReal.coe_mul, ENNReal.tsum_mul_right]
      using hE3
  exact setIntegral_eq_setIntegral_of_forall_setLIntegral_eq μ DΓ DN
    (fun i g => rep i * g) (fun i => measurable_const_mul (rep i))
    (fun h => ∀ (x : F) (g : AdelicGL2 (𝓞 F) F),
      h (globalPoints (𝓞 F) F (unipotentGL2 x) * g) = h g)
    hD1 (fun g => W₃ g * φ₂ g) (hW₃.mul hφ₂)
    (fun r _ x g => by simp only [hf_inv x g])
    (fun g => Φ g * φ₂ g) (hΦ.mul hφ₂) hsum hconv

end SumTransfer

section Unfolding

open NumberField MeasureTheory AutomorphicForm

theorem integral_mul_eq_integral_whittaker_mul_whittaker
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψK : ∀ x : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) x) = 1)

    [MeasurableSpace (AdelicGL2 (𝓞 F) F)] [MeasurableMul (AdelicGL2 (𝓞 F) F)]
    (μ : Measure (AdelicGL2 (𝓞 F) F))
    (DΓ DN : Set (AdelicGL2 (𝓞 F) F))

    (ι : Type) [Countable ι] (rep : ι → AdelicGL2 (𝓞 F) F)
    (hrep_mem : ∀ i, rep i ∈ (globalPoints (𝓞 F) F).range)

    (Q : Type) [MeasurableSpace Q] (μQ : Measure Q) (σ : Q → AdelicGL2 (𝓞 F) F)
    (T : Type) [MeasurableSpace T] (ν : Measure T) (τ : T → AdeleRing (𝓞 F) F)
    (hτu : Measurable fun t : T => (unipotentGL2 (τ t) : AdelicGL2 (𝓞 F) F))

    (hD1 : ∀ h : AdelicGL2 (𝓞 F) F → ENNReal, Measurable h →
      (∀ (x : F) (g : AdelicGL2 (𝓞 F) F),
        h (globalPoints (𝓞 F) F (unipotentGL2 x) * g) = h g) →
      ∫⁻ g in DN, h g ∂μ = ∫⁻ g in DΓ, ∑' i : ι, h (rep i * g) ∂μ)
    (hD2 : ∀ h : AdelicGL2 (𝓞 F) F → ENNReal, Measurable h →
      (∀ (x : F) (g : AdelicGL2 (𝓞 F) F),
        h (globalPoints (𝓞 F) F (unipotentGL2 x) * g) = h g) →
      Measurable (fun q : Q => ∫⁻ t, h (unipotentGL2 (τ t) * σ q) ∂ν) ∧
        ∫⁻ g in DN, h g ∂μ = ∫⁻ q, ∫⁻ t, h (unipotentGL2 (τ t) * σ q) ∂ν ∂μQ)

    (W₃ Φ : AdelicGL2 (𝓞 F) F → ℂ) (hW₃ : Measurable W₃) (hΦ : Measurable Φ)
    (hE1 : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      W₃ (unipotentGL2 x * g) = ψ x * W₃ g)
    (hE2 : ∀ g : AdelicGL2 (𝓞 F) F, HasSum (fun i : ι => W₃ (rep i * g)) (Φ g))

    (φ₂ W₂ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₂ : Measurable φ₂)
    (hG1 : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ₂ (globalPoints (𝓞 F) F γ * g) = φ₂ g)
    (hG3 : ∀ g : AdelicGL2 (𝓞 F) F,
      ∫ t, φ₂ (unipotentGL2 (τ t) * g) * ψ (τ t) ∂ν = W₂ g)

    (hE3 : ∫⁻ g in DΓ,
      (∑' i : ι, (‖W₃ (rep i * g)‖₊ : ENNReal)) * (‖φ₂ g‖₊ : ENNReal) ∂μ < ⊤) :
    IntegrableOn (fun g => Φ g * φ₂ g) DΓ μ ∧
      Integrable (fun q => W₃ (σ q) * W₂ (σ q)) μQ ∧
      ∫ g in DΓ, Φ g * φ₂ g ∂μ = ∫ q, W₃ (σ q) * W₂ (σ q) ∂μQ := by

  obtain ⟨hIΓ, hIN, hfold⟩ :=
    setIntegral_mul_eq_setIntegral_whittaker_mul F ψ hψK μ DΓ DN ι rep hrep_mem hD1 W₃ Φ hW₃ hΦ
      hE1 hE2 φ₂ hφ₂ hG1 hE3

  have hf_inv : ∀ (x : F) (g : AdelicGL2 (𝓞 F) F),
      W₃ (globalPoints (𝓞 F) F (unipotentGL2 x) * g) *
          φ₂ (globalPoints (𝓞 F) F (unipotentGL2 x) * g) = W₃ g * φ₂ g := by
    intro x g
    rw [hG1, globalPoints_unipotentGL2', hE1, hψK x, one_mul]

  have hfin : ∫⁻ g, ‖W₃ g * φ₂ g‖ₑ ∂(μ.restrict DN) < ⊤ :=
    hasFiniteIntegral_iff_enorm.1 hIN.integrable.hasFiniteIntegral
  obtain ⟨hIq, hId⟩ :=
    integral_eq_smul_integral_integral_of_forall_lintegral_eq (μ.restrict DN) μQ ν
      (fun t q => unipotentGL2 (τ t) * σ q) (fun q => hτu.mul_const (σ q))
      (fun h => ∀ (x : F) (g : AdelicGL2 (𝓞 F) F),
        h (globalPoints (𝓞 F) F (unipotentGL2 x) * g) = h g)
      1 one_ne_zero
      (fun h hh hP => ⟨(hD2 h hh hP).1, by rw [one_mul]; exact (hD2 h hh hP).2⟩)
      (fun g => W₃ g * φ₂ g) (hW₃.mul hφ₂)
      (fun k _ x g => by simp only [hf_inv x g]) hfin

  have hfib : ∀ q : Q,
      ∫ t, W₃ (unipotentGL2 (τ t) * σ q) * φ₂ (unipotentGL2 (τ t) * σ q) ∂ν =
        W₃ (σ q) * W₂ (σ q) := by
    intro q
    have hpt : ∀ t : T, W₃ (unipotentGL2 (τ t) * σ q) * φ₂ (unipotentGL2 (τ t) * σ q) =
        W₃ (σ q) * (φ₂ (unipotentGL2 (τ t) * σ q) * ψ (τ t)) := by
      intro t
      rw [hE1]
      ring
    simp_rw [hpt]
    rw [integral_const_mul, hG3]
  have hIq' : Integrable (fun q => W₃ (σ q) * W₂ (σ q)) μQ := by
    refine hIq.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [hfib]
  have hId' : ∫ g in DN, W₃ g * φ₂ g ∂μ = ∫ q, W₃ (σ q) * W₂ (σ q) ∂μQ := by
    have h := hId
    simp only [hfib, ENNReal.toReal_one, one_smul] at h
    exact h
  exact ⟨hIΓ, hIq', hfold.trans hId'⟩

end Unfolding

end Ws23J3Int.RSU

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

namespace Ws23J3Int

open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg Matrix
open scoped ENNReal Pointwise

abbrev G2 : Type := AdelicGL2 (𝓞 ℚ) ℚ
local notation "μG" => NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ

scoped instance countable_mirabolicIndex' : Countable (MirabolicIndex ℚ) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  haveI : Countable (GL (Fin 2) ℚ) :=
    Function.Injective.countable (f := (Units.val : GL (Fin 2) ℚ → Matrix (Fin 2) (Fin 2) ℚ)) Units.val_injective
  unfold MirabolicIndex; infer_instance

theorem globalPoints_apply_coe (g : GL (Fin 2) ℚ) (i j : Fin 2) :
    ((globalPoints (𝓞 ℚ) ℚ g : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) ((g : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

theorem globalPoints_injective : Function.Injective (globalPoints (𝓞 ℚ) ℚ) := by
  intro a b hab
  apply Units.ext
  ext i j
  have h := congrArg (fun g : G2 => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j) hab
  simp only [globalPoints_apply_coe] at h
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ h

theorem subgroup_smul_set_eq_image {H : Subgroup G2} (h : H) (S : Set G2) :
    h • S = (fun g => (h : G2) * g) '' S := by
  ext x
  simp only [Set.mem_smul_set, Subgroup.smul_def, smul_eq_mul, Set.mem_image]

theorem isFundamentalDomain_iUnion_mirabolicRep_smul {D : Set G2}
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D μG) :
    IsFundamentalDomain ((globalPoints (𝓞 ℚ) ℚ).comp (unipotentGL2Hom (R := ℚ))).range
      (⋃ i : MirabolicIndex ℚ, (fun g => globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g) '' D) μG := by
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  have hmp : ∀ a : G2, MeasurePreserving (fun g : G2 => a * g) μG μG := fun a => measurePreserving_mul_left μG a

  have hrep : ∀ (i : MirabolicIndex ℚ) (g : GL (Fin 2) ℚ), (Quotient.mk _ g : MirabolicIndex ℚ) = i →
      g * (mirabolicRep ℚ i)⁻¹ ∈ (unipotentGL2Hom (R := ℚ)).range := by
    intro i g hg
    have h := (mirabolicRep_spec ℚ i).trans hg.symm
    exact QuotientGroup.rightRel_apply.1 (Quotient.exact h)
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  ·
    refine NullMeasurableSet.iUnion fun i => ?_
    rw [Set.image_mul_left]
    exact hD.nullMeasurableSet.preimage (hmp _).quasiMeasurePreserving
  ·
    filter_upwards [hD.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    obtain ⟨g₀, hg₀⟩ := g.2
    set i : MirabolicIndex ℚ := Quotient.mk _ g₀⁻¹ with hi
    obtain ⟨t, ht⟩ := hrep i g₀⁻¹ rfl

    have hγ : (unipotentGL2Hom (R := ℚ) t)⁻¹ = mirabolicRep ℚ i * g₀ := by
      rw [ht, _root_.mul_inv_rev, inv_inv, inv_inv]
    refine ⟨⟨globalPoints (𝓞 ℚ) ℚ (unipotentGL2Hom (R := ℚ) t)⁻¹, ⟨t⁻¹, by rw [map_inv, MonoidHom.comp_apply, map_inv]⟩⟩, ?_⟩
    rw [Subgroup.smul_def, smul_eq_mul, Set.mem_iUnion]
    refine ⟨i, (g : G2) * x, hg, ?_⟩
    simp only
    rw [hγ, map_mul, mul_assoc, hg₀]
  ·
    intro n hn
    rw [Set.smul_set_iUnion]
    simp_rw [subgroup_smul_set_eq_image, Set.image_image, ← mul_assoc]
    refine AEDisjoint.iUnion_left_iff.2 fun i => AEDisjoint.iUnion_right_iff.2 fun j => ?_
    obtain ⟨t, ht⟩ := n.2

    let a : (globalPoints (𝓞 ℚ) ℚ).range := ⟨(n : G2) * globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i),
      ⟨unipotentGL2Hom (R := ℚ) t * mirabolicRep ℚ i, by rw [map_mul, ← ht, MonoidHom.comp_apply]⟩⟩
    let b : (globalPoints (𝓞 ℚ) ℚ).range := ⟨globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ j), ⟨mirabolicRep ℚ j, rfl⟩⟩
    have hab : a ≠ b := by
      intro h
      have h' : globalPoints (𝓞 ℚ) ℚ (unipotentGL2Hom (R := ℚ) t * mirabolicRep ℚ i)
          = globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ j) := by
        have := congrArg Subtype.val h
        simp only [a, b] at this
        rw [map_mul, ← MonoidHom.comp_apply, ht]
        exact this
      have h'' := globalPoints_injective h'

      have hij : j = i := by
        rw [← mirabolicRep_spec ℚ j, ← mirabolicRep_spec ℚ i]
        apply Quotient.sound
        refine QuotientGroup.rightRel_apply.mpr ?_

        rw [← h'', _root_.mul_inv_rev, mul_inv_cancel_left]
        exact inv_mem ⟨t, rfl⟩
      subst hij
      have ht1 : unipotentGL2Hom (R := ℚ) t = 1 := mul_right_cancel (h''.trans (one_mul _).symm)
      apply hn
      apply Subtype.ext
      rw [← ht, MonoidHom.comp_apply, ht1, map_one]
      rfl
    have key := hD.aedisjoint hab
    simp only [Function.onFun, subgroup_smul_set_eq_image, a, b] at key
    exact key
  ·
    intro n
    have : (fun x : G2 => n • x) = fun x => (n : G2) * x := funext fun x => by rw [Subgroup.smul_def, smul_eq_mul]
    rw [this]
    exact (hmp _).quasiMeasurePreserving

theorem detNorm_globalPoints_mul (γ : GL (Fin 2) ℚ) (g : G2) :
    detNorm (globalPoints (𝓞 ℚ) ℚ γ * g) = detNorm g := by
  unfold detNorm
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem det_unipotentGL2 (x : AdeleRing (𝓞 ℚ) ℚ) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 x : G2) = 1 := by
  refine Units.ext ?_
  change Matrix.det ((unipotentGL2 x : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = 1
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]
  ring

theorem detNorm_unipotentGL2_mul (x : AdeleRing (𝓞 ℚ) ℚ) (g : G2) :
    detNorm (unipotentGL2 x * g) = detNorm g := by
  unfold detNorm
  rw [map_mul, det_unipotentGL2, one_mul]

theorem iota_unipotentGL2 (x : AdeleRing (𝓞 ℚ) ℚ) :
    iota (𝓞 ℚ) ℚ (unipotentGL2 x) = upperUnipotent3 x 0 0 :=
  iotaGL_unipotentGL2 x

theorem continuous_embedMat2 {A : Type*} [CommRing A] [TopologicalSpace A] :
    Continuous (embedMat2 : Matrix (Fin 2) (Fin 2) A → Matrix (Fin 3) (Fin 3) A) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [embedMat2] <;> fun_prop

theorem continuous_iota : Continuous (iota (𝓞 ℚ) ℚ : G2 → AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_embedMat2.comp Units.continuous_val
  · have : (fun g : G2 => (((iota (𝓞 ℚ) ℚ g)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun g => embedMat2 ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact continuous_embedMat2.comp (Units.continuous_val.comp continuous_inv)

theorem continuous_det_GL2 : Continuous (Matrix.GeneralLinearGroup.det : G2 → (AdeleRing (𝓞 ℚ) ℚ)ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · have : (fun g : G2 => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)) =
        fun g => Matrix.det ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem detNorm_pos (g : G2) : 0 < detNorm g := NumberField.TateGlobal.ideleNorm_pos _

theorem continuous_detNorm : Continuous (detNorm : G2 → ℝ) :=
  (NumberField.TateGlobal.continuous_ideleNorm ℚ).comp continuous_det_GL2

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μA" => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ

scoped instance isAddHaarMeasure_adelicAddHaar' : (μA).IsAddHaarMeasure :=
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ

scoped instance countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) := by
  show Countable {x : 𝔸 // x ∈ Set.range (algebraMap ℚ 𝔸)}
  exact (Set.countable_range _).to_subtype

theorem globalPoints_unipotentGL2 (k : ℚ) :
    globalPoints (𝓞 ℚ) ℚ (unipotentGL2 k) = unipotentGL2 (algebraMap ℚ 𝔸 k) := by
  refine Units.ext ?_
  change (algebraMap ℚ 𝔸).mapMatrix ((unipotentGL2 k : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = _
  rw [unipotentGL2_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

scoped instance vaddInvariantMeasure_principalSubgroup :
    VAddInvariantMeasure (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) 𝔸 μA :=
  ⟨fun k s _ => measure_preimage_add _ (k : 𝔸) s⟩

theorem integral_cond_adelicBox_comp_add_right (P : 𝔸 → ℂ)
    (hP : ∀ (k : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : 𝔸), P ((k : 𝔸) + x) = P x) (a : 𝔸) :
    ∫ x, P (x + a) ∂(ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ)) =
      ∫ x, P x ∂(ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ)) := by
  have hcond : ProbabilityTheory.cond μA (AdelicBox.adelicBox ℚ) =
      ((μA) (AdelicBox.adelicBox ℚ))⁻¹ • (μA).restrict (AdelicBox.adelicBox ℚ) := rfl
  rw [hcond, integral_smul_measure, integral_smul_measure]
  congr 1

  rw [← (measurePreserving_add_right (μA) a).setIntegral_image_emb (measurableEmbedding_addRight a) P
    (AdelicBox.adelicBox ℚ)]
  have hbox := AdelicBox.isAddFundamentalDomain_adelicBox ℚ (μA)
  have himg : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ)
      ((fun x : 𝔸 => x + a) '' AdelicBox.adelicBox ℚ) μA := by
    refine hbox.image_of_equiv (ν := μA) (Equiv.addRight a)
      (by simpa using (measurePreserving_add_right (μA) (-a)).quasiMeasurePreserving) (Equiv.refl _) ?_
    intro k x
    show (k : 𝔸) + x + a = (k : 𝔸) + (x + a)
    rw [add_assoc]
  exact MeasureTheory.IsAddFundamentalDomain.setIntegral_eq himg hbox (f := P) (fun k x => hP k x)

theorem continuous_transposeInv3 :
    Continuous (transposeInv3 : AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵀ
    exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · show Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ((g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵀ
    exact Units.continuous_val.matrix_transpose

theorem continuous_dualForm {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦ : Continuous Φ) : Continuous (dualForm Φ) :=
  hΦ.comp continuous_transposeInv3

theorem unfold
    (Dp : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ ψc : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (hψK : ∀ x : ℚ, ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) x) = 1)
    (hψc : ∀ x : AdeleRing (𝓞 ℚ) ℚ, ψc (-x) = ψ x)
    (W Φ₃ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hWlaw' : IsGL3PsiWhittakerFn ψ W)
    (hexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Φ₃ g))
    (hhp : HasWhittakerHalfPlane W)
    (hΦ₃c : Continuous Φ₃) (hW3c : Continuous W)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
      (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
    (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
    (hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun q : UnipotentQuotient ℚ => (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
              whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψc φ 1 g *
                W (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q))
          (unipotentQuotientMeasure ℚ) := by
  obtain ⟨σ₁, hσ₁⟩ := hhp
  obtain ⟨Cφ, hCφ⟩ := hφb
  refine ⟨σ₁ + 1, fun s hs => ?_⟩
  set Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun g => φ g * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2) with hΦ
  set Wc : AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
    whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψc φ 1 with hWc
  set W₂ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun g => Wc g * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2) with hW₂
  have hWlaw : ∀ (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      W (upperUnipotent3 x y z * g) = ψ (x + y) * W g := hWlaw'

  have e1 : ∀ g', Wc g' = ∫ t, φ (unipotentGL2 t * g') * ψ t
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)) := by
    intro g'
    rw [hWc]
    show (∫ x, φ (unipotentGL2 x * g') * ψc (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x))
      ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))) = _
    congr 1
    funext x
    rw [map_one, one_mul, hψc]
  have hΦinv : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), Φ (globalPoints (𝓞 ℚ) ℚ γ * g) = Φ g := by
    intro γ g
    simp only [hΦ, hφ, detNorm_globalPoints_mul]
  have hΦm : Measurable Φ := by
    rw [hΦ]
    exact hφc.measurable.mul ((Complex.continuous_ofReal.comp continuous_detNorm).measurable.pow_const _)

  have hCφ0 : 0 ≤ Cφ :=
    le_trans (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (detNorm_pos 1).le _)) (hCφ 1)
  have hΦbd : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖Φ g‖ ≤ Cφ * detNorm g ^ s.re := by
    intro g
    have hpos := detNorm_pos g
    have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    simp only [hΦ, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, hre]
    have h1 : ‖φ g‖ ≤ Cφ * detNorm g ^ (1 / 2 : ℝ) := by
      have h2 := hCφ g
      have h3 : ‖φ g‖ = ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) * detNorm g ^ (1 / 2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hpos]; norm_num
      rw [h3]
      exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hpos.le _)
    calc ‖φ g‖ * detNorm g ^ (s.re - 1 / 2)
        ≤ Cφ * detNorm g ^ (1 / 2 : ℝ) * detNorm g ^ (s.re - 1 / 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hpos.le _)
      _ = Cφ * detNorm g ^ s.re := by
          rw [mul_assoc, ← Real.rpow_add hpos]; congr 2; ring

  have hE3 : ∫⁻ g in D, (∑' i : MirabolicIndex ℚ,
      (‖W (iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g))‖₊ : ℝ≥0∞)) *
        (‖Φ g‖₊ : ℝ≥0∞) ∂μG < ⊤ := by
    have hpt : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, (∑' i : MirabolicIndex ℚ,
        (‖W (iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g))‖₊ : ℝ≥0∞)) * (‖Φ g‖₊ : ℝ≥0∞) ≤
        ENNReal.ofReal Cφ * ((∑' i : MirabolicIndex ℚ,
          (‖W (iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g))‖₊ : ℝ≥0∞)) *
            ENNReal.ofReal (detNorm g ^ s.re)) := by
      intro g
      have hΦe : (‖Φ g‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal Cφ * ENNReal.ofReal (detNorm g ^ s.re) := by
        rw [← ENNReal.ofReal_mul hCφ0, ← enorm_eq_nnnorm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hΦbd g)
      calc (∑' i : MirabolicIndex ℚ,
            (‖W (iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g))‖₊ : ℝ≥0∞)) * (‖Φ g‖₊ : ℝ≥0∞)
          ≤ (∑' i : MirabolicIndex ℚ,
            (‖W (iota (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i) * g))‖₊ : ℝ≥0∞)) *
              (ENNReal.ofReal Cφ * ENNReal.ofReal (detNorm g ^ s.re)) := mul_le_mul_right hΦe _
        _ = _ := by ring
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hσ₁ s.re (by linarith) D hD)

  have hG3 : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ∫ t, Φ (unipotentGL2 t * g) * ψ t ∂(ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
        (AdelicBox.adelicBox ℚ)) = W₂ g := by
    intro g
    rw [hW₂]
    show _ = Wc g * _
    rw [e1, ← integral_mul_const]
    congr 1
    funext t
    simp only [hΦ, detNorm_unipotentGL2_mul]
    ring

  have hE1 : ∀ (x : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      (fun y : AdelicGL2 (𝓞 ℚ) ℚ => W (iota (𝓞 ℚ) ℚ y)) (unipotentGL2 x * g) =
        ψ x * (fun y : AdelicGL2 (𝓞 ℚ) ℚ => W (iota (𝓞 ℚ) ℚ y)) g := by
    intro x g
    simp only [map_mul, iota_unipotentGL2]
    simpa only [add_zero] using hWlaw x 0 0 (iota (𝓞 ℚ) ℚ g)
  have hE2 : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      HasSum (fun i : MirabolicIndex ℚ =>
          (fun x : AdelicGL2 (𝓞 ℚ) ℚ => W (iota (𝓞 ℚ) ℚ x))
            ((fun j : MirabolicIndex ℚ => globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ j)) i * g))
        ((fun x : AdelicGL2 (𝓞 ℚ) ℚ => Φ₃ (iota (𝓞 ℚ) ℚ x)) g) := by
    intro g
    simp only [map_mul]
    exact hexp (iota (𝓞 ℚ) ℚ g)

  have hDNfd := isFundamentalDomain_iUnion_mirabolicRep_smul hD
  have hD1 := LanglandsTunnell.CubicInduction.setLIntegral_eq_setLIntegral_tsum_mirabolicRep D _ hD hDNfd
  obtain ⟨-, hIq, -⟩ :=
    Ws23J3Int.RSU.integral_mul_eq_integral_whittaker_mul_whittaker ℚ ψ hψK
      μG D _
      (MirabolicIndex ℚ) (fun i => globalPoints (𝓞 ℚ) ℚ (mirabolicRep ℚ i))
      (fun i => MonoidHom.mem_range.mpr ⟨mirabolicRep ℚ i, rfl⟩)
      (UnipotentQuotient ℚ) (unipotentQuotientMeasure ℚ) (fun q => q.out)
      (AdeleRing (𝓞 ℚ) ℚ)
      (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
      (fun t => t)
      (AutomorphicForm.continuous_unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ)).measurable
      hD1
      (fun h hh hinv =>
        ⟨AutomorphicForm.measurable_lintegral_unipotentGL2_mul_out ℚ h hh hinv,
          AutomorphicForm.setLIntegral_adelicGLHaar_eq_lintegral_unipotentQuotientMeasure ℚ h hh hinv _ hDNfd⟩)
      (fun x => W (iota (𝓞 ℚ) ℚ x)) (fun x => Φ₃ (iota (𝓞 ℚ) ℚ x))
      (hW3c.measurable.comp continuous_iota.measurable) (hΦ₃c.measurable.comp continuous_iota.measurable)
      hE1 hE2 Φ W₂ hΦm hΦinv hG3 hE3

  have hT : ∀ q : UnipotentQuotient ℚ,
      W (iota (𝓞 ℚ) ℚ q.out) * W₂ q.out =
        Wc (σq q) * W (iota (𝓞 ℚ) ℚ (σq q)) * ((detNorm (σq q) : ℝ) : ℂ) ^ (s - 1 / 2) := by

    set I : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun g => Wc g * W (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2) with hI
    have hWcinv : ∀ (b : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), Wc (unipotentGL2 b * g) = ψ (-b) * Wc g := by
      intro b g
      set P : AdeleRing (𝓞 ℚ) ℚ → ℂ := fun t => φ (unipotentGL2 t * g) * ψ t with hP
      have hPer : ∀ (k : AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (x : AdeleRing (𝓞 ℚ) ℚ),
          P ((k : AdeleRing (𝓞 ℚ) ℚ) + x) = P x := by
        rintro ⟨_, k, rfl⟩ x
        simp only [hP]
        rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hφ, AddChar.map_add_eq_mul, hψK, one_mul]
      have hshift : ∀ t : AdeleRing (𝓞 ℚ) ℚ,
          φ (unipotentGL2 t * (unipotentGL2 b * g)) * ψ t = ψ (-b) * P (t + b) := by
        intro t
        simp only [hP]
        rw [← mul_assoc, ← unipotentGL2_add, mul_left_comm, ← AddChar.map_add_eq_mul]
        congr 2
        ring
      rw [e1, e1]
      simp_rw [hshift]
      rw [integral_const_mul, integral_cond_adelicBox_comp_add_right P hPer b]
    have hIinv : ∀ (b : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), I (unipotentGL2 b * g) = I g := by
      intro b g
      simp only [hI]
      rw [hWcinv, map_mul, iota_unipotentGL2, hWlaw, add_zero, detNorm_unipotentGL2_mul]
      have : ψ (-b) * ψ b = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      linear_combination (Wc g * W (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) * this
    intro q

    have hrel : (MulAction.orbitRel (adelicUnipotent ℚ) (AdelicGL2 (𝓞 ℚ) ℚ)) (σq q) q.out :=
      Quotient.exact' ((hσq q).trans (Quotient.out_eq' q).symm)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨⟨n, a, rfl⟩, hn⟩ := hrel
    have hσ : σq q = unipotentGL2 (Multiplicative.toAdd a) * q.out := hn.symm
    have hR : Wc (σq q) * W (iota (𝓞 ℚ) ℚ (σq q)) * ((detNorm (σq q) : ℝ) : ℂ) ^ (s - 1 / 2) = I (σq q) := rfl
    rw [hR, hσ, hIinv, hW₂]
    simp only [hI]
    ring

  exact hIq.congr (Filter.Eventually.of_forall hT)

theorem main
    (Dp : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) :
      (∀ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
        (Θ W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (_hΘc : Continuous Θ) (_hWc : Continuous W) (_hWg : IsGaugeMajorised3 ℚ W)
        (_hWlaw : IsGL3PsiWhittakerFn ψ W)
        (_hWexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Θ g))
        (_hWhp : HasWhittakerHalfPlane W)
        (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hφc : Continuous φ)
        (_hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
        (_hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
        (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
        (_hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
        (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q),
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun q : UnipotentQuotient ℚ => (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
                  whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ φ 1 g *
                    W (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q))
              (unipotentQuotientMeasure ℚ)) ∧
      (∀ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
        (Θ W' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (_hΘc : Continuous Θ) (_hW'c : Continuous W') (_hW'g : IsGaugeMajorised3 ℚ W')
        (_hW'law : IsGL3PsiWhittakerFn ψ⁻¹ W')
        (_hW'exp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W' (mirabolicTranslate i * g)) (dualForm Θ g))
        (_hW'hp : HasWhittakerHalfPlane W')
        (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hφc : Continuous φ)
        (_hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
        (_hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
        (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
        (_hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
        (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q),
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun q : UnipotentQuotient ℚ => (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
                  whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψ φ 1 g *
                    W' (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q))
              (unipotentQuotientMeasure ℚ)) := by
  refine ⟨?_, ?_⟩
  · intro ψ hψ Θ W hΘc hWc _hWg hWlaw hWexp hWhp φ hφc hφ hφb D hD σq hσq
    exact unfold Dp U gen ψ ψ⁻¹ hψ.principalInvariant (fun x => by rw [AddChar.inv_apply, neg_neg])
      W Θ hWlaw hWexp hWhp hΘc hWc φ hφc hφ hφb D hD σq hσq
  · intro ψ hψ Θ W' hΘc hW'c _hW'g hW'law hW'exp hW'hp φ hφc hφ hφb D hD σq hσq
    exact unfold Dp U gen ψ⁻¹ ψ
      (fun x => by rw [AddChar.inv_apply, ← map_neg]; exact hψ.principalInvariant (-x))
      (fun x => by rw [AddChar.inv_apply])
      W' (dualForm Θ) hW'law hW'exp hW'hp (continuous_dualForm hΘc) hW'c φ hφc hφ hφb D hD σq hσq

end Ws23J3Int
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integrable_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual.Ws23J3Int"

theorem solution
    (Dp : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) :
      (∀ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
        (Θ W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (_hΘc : Continuous Θ) (_hWc : Continuous W) (_hWg : IsGaugeMajorised3 ℚ W)
        (_hWlaw : IsGL3PsiWhittakerFn ψ W)
        (_hWexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Θ g))
        (_hWhp : HasWhittakerHalfPlane W)
        (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hφc : Continuous φ)
        (_hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
        (_hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
        (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
        (_hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
        (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q),
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun q : UnipotentQuotient ℚ => (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
                  whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ φ 1 g *
                    W (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q))
              (unipotentQuotientMeasure ℚ)) ∧
      (∀ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
        (Θ W' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (_hΘc : Continuous Θ) (_hW'c : Continuous W') (_hW'g : IsGaugeMajorised3 ℚ W')
        (_hW'law : IsGL3PsiWhittakerFn ψ⁻¹ W')
        (_hW'exp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W' (mirabolicTranslate i * g)) (dualForm Θ g))
        (_hW'hp : HasWhittakerHalfPlane W')
        (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hφc : Continuous φ)
        (_hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
        (_hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
        (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
        (_hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
        (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q),
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun q : UnipotentQuotient ℚ => (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
                  whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψ φ 1 g *
                    W' (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q))
              (unipotentQuotientMeasure ℚ)) :=
  Ws23J3Int.main Dp U gen

end S_LanglandsTunnell_RankinSelberg_integrable_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_integrable_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual (solution)
