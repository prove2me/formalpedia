-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_lintegral_torus_whittaker3_sq_le_mul_lintegral_quotientMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e2671516-20e4-5578-80c2-34c2ff7b4386

import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_WhittakerBlock_isHaarMeasure_unipotentHaar3
import Theorems.Thm_WhittakerBlock_isMulRightInvariant_unipotentHaar3
import Theorems.Thm_LanglandsTunnell_CubicInduction_whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_mul_lintegral_quotientMeasure
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

section

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

namespace TorusSliceBounds

private theorem setLIntegral_lintegral_mul_eq_lintegral_mul_fibre
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    {α : Type*} [MeasurableSpace α] (m : Measure α) [SFinite m]
    {B : Set G} (hB : MeasurableSet B) {F : G → ℝ≥0∞} (hF : Measurable F)
    {t : α → G} (ht : AEMeasurable t m) {w : α → ℝ≥0∞} (hw : AEMeasurable w m) :
    ∫⁻ k in B, ∫⁻ a, F (t a * k) * w a ∂m ∂μ =
      ∫⁻ g, F g * ∫⁻ a, B.indicator (fun _ => (1 : ℝ≥0∞)) ((t a)⁻¹ * g) * w a ∂m ∂μ := by
  have h1 : AEMeasurable (Function.uncurry fun (k : G) (a : α) => F (t a * k) * w a)
      ((μ.restrict B).prod m) :=
    (hF.comp_aemeasurable (ht.comp_snd.mul measurable_fst.aemeasurable)).mul hw.comp_snd
  have h2 : AEMeasurable (Function.uncurry fun (g : G) (a : α) =>
      B.indicator (fun _ => (1 : ℝ≥0∞)) ((t a)⁻¹ * g) * F g * w a) (μ.prod m) :=
    (((measurable_const.indicator hB).comp_aemeasurable
        (ht.comp_snd.inv.mul measurable_fst.aemeasurable)).mul
      (hF.comp_aemeasurable measurable_fst.aemeasurable)).mul hw.comp_snd
  calc ∫⁻ k in B, ∫⁻ a, F (t a * k) * w a ∂m ∂μ
      = ∫⁻ a, ∫⁻ k in B, F (t a * k) * w a ∂μ ∂m := lintegral_lintegral_swap h1
    _ = ∫⁻ a, ∫⁻ g, B.indicator (fun _ => (1 : ℝ≥0∞)) ((t a)⁻¹ * g) * F g * w a ∂μ ∂m := by
        refine lintegral_congr fun a => ?_
        rw [← lintegral_indicator hB (fun k => F (t a * k) * w a),
          ← lintegral_mul_left_eq_self
            (fun g => B.indicator (fun _ => (1 : ℝ≥0∞)) ((t a)⁻¹ * g) * F g * w a) (t a)]
        refine lintegral_congr fun k => ?_
        simp only [inv_mul_cancel_left]
        by_cases hk : k ∈ B <;> simp [Set.indicator, hk]
    _ = ∫⁻ g, ∫⁻ a, B.indicator (fun _ => (1 : ℝ≥0∞)) ((t a)⁻¹ * g) * F g * w a ∂m ∂μ :=
        (lintegral_lintegral_swap h2).symm
    _ = ∫⁻ g, F g * ∫⁻ a, B.indicator (fun _ => (1 : ℝ≥0∞)) ((t a)⁻¹ * g) * w a ∂m ∂μ := by
        refine lintegral_congr fun g => ?_
        have hm : AEMeasurable (fun a : α => B.indicator (fun _ => (1 : ℝ≥0∞)) ((t a)⁻¹ * g) * w a) m :=
          ((measurable_const.indicator hB).comp_aemeasurable (ht.inv.mul_const g)).mul hw
        rw [← lintegral_const_mul'' (F g) hm]
        exact lintegral_congr fun a => by ring

private theorem setLIntegral_setLIntegral_le_mul_lintegral_mul_fibre
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    {α : Type*} [MeasurableSpace α] (m : Measure α) [SFinite m] {s : Set α} (hs : MeasurableSet s)
    {B : Set G} (hB : MeasurableSet B) {F : G → ℝ≥0∞} (hF : Measurable F)
    {t : α → G} (ht : AEMeasurable t (m.restrict s)) {w : α → ℝ≥0∞} (hw : AEMeasurable w (m.restrict s))
    {φ : α → G → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hdom : ∀ a ∈ s, ∀ k ∈ B, φ a k ≤ M * (F (t a * k) * w a)) :
    ∫⁻ k in B, ∫⁻ a in s, φ a k ∂m ∂μ ≤
      M * ∫⁻ g, F g * ∫⁻ a in s, B.indicator (fun _ => (1 : ℝ≥0∞)) ((t a)⁻¹ * g) * w a ∂m ∂μ := by
  rw [← setLIntegral_lintegral_mul_eq_lintegral_mul_fibre μ (m.restrict s) hB hF ht hw,
    ← lintegral_const_mul' M _ hM]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem hB] with k hk
  rw [← lintegral_const_mul' M _ hM]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem hs] with a ha
  exact hdom a ha k hk

private theorem le_mul_lintegral_out_of_fibre_bound
    {G Q X : Type*} [Mul G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace Q]
    [MeasurableSpace X] (μ : Measure G) (qb : Measure Q) (ν : Measure X) (out : Q → G) {ι : X → G}
    (hι : Measurable ι)
    (hunfold : ∀ h : G → ℝ≥0∞, Measurable h → ∫⁻ g, h g ∂μ = ∫⁻ q, ∫⁻ x, h (ι x * out q) ∂ν ∂qb)
    {f wB : G → ℝ≥0∞} (hf : Measurable f) (hwB : Measurable wB) (hinv : ∀ x g, f (ι x * g) = f g)
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ⊤) (hbound : ∀ g, ∫⁻ x, wB (ι x * g) ∂ν ≤ C₀)
    {L M : ℝ≥0∞} (hL : L ≤ M * ∫⁻ g, f g * wB g ∂μ) :
    L ≤ M * C₀ * ∫⁻ q, f (out q) ∂qb := by
  have hstep : ∫⁻ g, f g * wB g ∂μ ≤ C₀ * ∫⁻ q, f (out q) ∂qb := by
    rw [hunfold _ (hf.fun_mul hwB)]
    calc ∫⁻ q, ∫⁻ x, f (ι x * out q) * wB (ι x * out q) ∂ν ∂qb
        = ∫⁻ q, f (out q) * ∫⁻ x, wB (ι x * out q) ∂ν ∂qb := by
          refine lintegral_congr fun q => ?_
          simp_rw [hinv]
          have hm : Measurable fun x : X => wB (ι x * out q) := hwB.comp (hι.mul_const _)
          exact lintegral_const_mul (f (out q)) hm
      _ ≤ ∫⁻ q, f (out q) * C₀ ∂qb := lintegral_mono fun q => mul_le_mul_right (hbound _) _
      _ = C₀ * ∫⁻ q, f (out q) ∂qb := by rw [lintegral_mul_const' _ _ hC₀, mul_comm]
  calc L ≤ M * ∫⁻ g, f g * wB g ∂μ := hL
    _ ≤ M * (C₀ * ∫⁻ q, f (out q) ∂qb) := mul_le_mul_right hstep _
    _ = M * C₀ * ∫⁻ q, f (out q) ∂qb := (mul_assoc _ _ _).symm

private theorem one_le_rpow_mul_max_sq {m d σ : ℝ} (hm : 0 < m) (hmd : m ≤ d)
    (hσ : σ ∈ Set.Icc (1 : ℝ) 2) : 1 ≤ d ^ σ * max 1 m⁻¹ ^ 2 := by
  have hd : 0 < d := hm.trans_le hmd
  rcases le_or_gt 1 d with h1 | h1
  · have hdσ : 1 ≤ d ^ σ := Real.one_le_rpow h1 (zero_le_one.trans hσ.1)
    have hmax : (1 : ℝ) ≤ max 1 m⁻¹ ^ 2 := by nlinarith [le_max_left (1 : ℝ) m⁻¹]
    exact one_le_mul_of_one_le_of_one_le hdσ hmax
  · have hm0 : m ≠ 0 := hm.ne'
    have h2 : d ^ (2 : ℝ) ≤ d ^ σ := Real.rpow_le_rpow_of_exponent_ge hd h1.le hσ.2
    rw [Real.rpow_two] at h2
    have h3 : m ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hm.le hmd 2
    have h4 : m⁻¹ ^ 2 ≤ max 1 m⁻¹ ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hm.le) (le_max_right _ _) 2
    calc (1 : ℝ) = m ^ 2 * m⁻¹ ^ 2 := by rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hm0)]
      _ ≤ d ^ σ * max 1 m⁻¹ ^ 2 := mul_le_mul (h3.trans h2) h4 (by positivity) (by positivity)

private theorem torus_weight_eq {a : Fin 3 → ℝ} (ha : a ∈ Set.pi Set.univ fun _ : Fin 3 => Set.Ioi (0 : ℝ))
    (σ : ℝ) :
    a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1) =
      (a 0 * a 1 * a 2) ^ σ * (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2) := by
  have h0 : 0 < a 0 := ha 0 (Set.mem_univ _)
  have h1 : 0 < a 1 := ha 1 (Set.mem_univ _)
  have h2 : 0 < a 2 := ha 2 (Set.mem_univ _)
  rw [Real.mul_rpow (by positivity) h2.le, Real.mul_rpow h0.le h1.le,
    show σ - 3 = σ + (-3) by ring, show σ - 1 = σ + (-1) by ring,
    Real.rpow_add h0, Real.rpow_add h1, Real.rpow_add h2, Real.rpow_one]
  ring

private theorem slice_integrand_le {x : ℝ≥0∞} {a : Fin 3 → ℝ}
    (ha : a ∈ Set.pi Set.univ fun _ : Fin 3 => Set.Ioi (0 : ℝ)) {m dk σ : ℝ} (hm : 0 < m)
    (hdk : m ≤ dk) (hσ : σ ∈ Set.Icc (1 : ℝ) 2) :
    x * ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) ≤
      ENNReal.ofReal (max 1 m⁻¹ ^ 2) *
        (x * ENNReal.ofReal ((a 0 * a 1 * a 2 * dk) ^ σ) *
          ENNReal.ofReal (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2)) := by
  have h0 : 0 < a 0 := ha 0 (Set.mem_univ _)
  have h1 : 0 < a 1 := ha 1 (Set.mem_univ _)
  have h2 : 0 < a 2 := ha 2 (Set.mem_univ _)
  have hdk0 : 0 < dk := hm.trans_le hdk
  have hkey : a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1) ≤
      max 1 m⁻¹ ^ 2 * ((a 0 * a 1 * a 2 * dk) ^ σ * (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2)) := by
    rw [torus_weight_eq ha σ, Real.mul_rpow (by positivity) hdk0.le]
    have h := one_le_rpow_mul_max_sq hm hdk hσ
    calc (a 0 * a 1 * a 2) ^ σ * (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2)
        = (a 0 * a 1 * a 2) ^ σ * (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2) * 1 := (mul_one _).symm
      _ ≤ (a 0 * a 1 * a 2) ^ σ * (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2) *
            (dk ^ σ * max 1 m⁻¹ ^ 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = max 1 m⁻¹ ^ 2 *
            ((a 0 * a 1 * a 2) ^ σ * dk ^ σ * (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2)) := by ring
  have hE := ENNReal.ofReal_le_ofReal hkey
  rw [ENNReal.ofReal_mul (p := max 1 m⁻¹ ^ 2) (by positivity),
    ENNReal.ofReal_mul (p := (a 0 * a 1 * a 2 * dk) ^ σ) (by positivity)] at hE
  calc x * ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1))
      ≤ x * (ENNReal.ofReal (max 1 m⁻¹ ^ 2) * (ENNReal.ofReal ((a 0 * a 1 * a 2 * dk) ^ σ) *
          ENNReal.ofReal (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2))) := mul_le_mul_right hE x
    _ = ENNReal.ofReal (max 1 m⁻¹ ^ 2) * (x * ENNReal.ofReal ((a 0 * a 1 * a 2 * dk) ^ σ) *
          ENNReal.ofReal (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2)) := by ring

end TorusSliceBounds

namespace TorusSliceBoundsGL3

private theorem measurableSet_octant : MeasurableSet (Set.pi Set.univ fun _ : Fin 3 => Set.Ioi (0 : ℝ)) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

private theorem exists_pos_forall_le_ideleNorm_det {B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hB : IsCompact B)
    (hcont : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) :
    ∃ m : ℝ, 0 < m ∧ ∀ k ∈ B, m ≤ NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det k) := by
  rcases B.eq_empty_or_nonempty with hBe | hne
  · exact ⟨1, one_pos, fun k hk => by simp [hBe] at hk⟩
  · obtain ⟨k₀, -, hmin⟩ := hB.exists_isMinOn hne hcont.continuousOn
    exact ⟨_, NumberField.TateGlobal.ideleNorm_pos _, fun k hk => (isMinOn_iff.mp hmin) k hk⟩

private theorem measurable_weight :
    Measurable fun a : Fin 3 → ℝ => ENNReal.ofReal (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2) :=
  ((((measurable_pi_apply (0 : Fin 3)).pow_const (-3 : ℝ)).mul
    ((measurable_pi_apply (1 : Fin 3)).pow_const (-1 : ℝ))).mul (measurable_pi_apply (2 : Fin 3))).ennreal_ofReal

private theorem aemeasurable_torusLift
    (hS8 : ContinuousOn (fun a : Fin 3 → ℝ => WhittakerBlock.archRealLift3 fun i j => if i = j then a i else 0)
      (Set.pi Set.univ fun _ : Fin 3 => Set.Ioi (0 : ℝ))) :
    AEMeasurable (fun a : Fin 3 → ℝ => WhittakerBlock.archRealLift3 fun i j => if i = j then a i else 0)
      (volume.restrict (Set.pi Set.univ fun _ : Fin 3 => Set.Ioi (0 : ℝ))) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  exact hS8.aemeasurable measurableSet_octant

private theorem measurableMul₂_adelicGL3 [SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ)] :
    MeasurableMul₂ (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  infer_instance

private theorem measurableInv_adelicGL3 : MeasurableInv (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  infer_instance

private theorem sfinite_adelicGLHaar : SFinite (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  infer_instance

private theorem isMulLeftInvariant_adelicGLHaar :
    (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).IsMulLeftInvariant := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  infer_instance

private theorem left_le_mul_lintegral_mul_fibre [SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ)]
    (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hBm : MeasurableSet B)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ) (hσ : σ ∈ Set.Icc (1 : ℝ) 2)
    (hf : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F g‖₊ : ℝ≥0∞) ^ 2 *
        (‖Φ fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ))
    (hS8 : ContinuousOn (fun a : Fin 3 → ℝ => WhittakerBlock.archRealLift3 fun i j => if i = j then a i else 0)
      (Set.pi Set.univ fun _ : Fin 3 => Set.Ioi (0 : ℝ)))
    (hdet : ∀ a ∈ Set.pi Set.univ fun _ : Fin 3 => Set.Ioi (0 : ℝ),
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
        (WhittakerBlock.archRealLift3 fun i j => if i = j then a i else 0)) = a 0 * a 1 * a 2)
    {m : ℝ} (hm : 0 < m)
    (hmB : ∀ k ∈ B, m ≤ NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det k)) :
    ∫⁻ k in B, (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
        (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ F
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖₊ : ℝ≥0∞) ^ 2 *
          (‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
              AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
          ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) ∂volume)
      ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤
      ENNReal.ofReal (max 1 m⁻¹ ^ 2) *
        ∫⁻ g, ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ F g‖₊ : ℝ≥0∞) ^ 2 *
            (‖Φ fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ)) *
          ∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
            B.indicator (fun _ => (1 : ℝ≥0∞))
                ((WhittakerBlock.archRealLift3 fun i j => if i = j then a i else 0)⁻¹ * g) *
              ENNReal.ofReal (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2) ∂volume
          ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI := measurableMul₂_adelicGL3
  haveI := measurableInv_adelicGL3
  haveI := sfinite_adelicGLHaar
  haveI := isMulLeftInvariant_adelicGLHaar
  refine TorusSliceBounds.setLIntegral_setLIntegral_le_mul_lintegral_mul_fibre
    (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) volume measurableSet_octant hBm hf
    (aemeasurable_torusLift hS8) measurable_weight.aemeasurable (M := ENNReal.ofReal (max 1 m⁻¹ ^ 2))
    ENNReal.ofReal_ne_top ?_
  intro a ha k hk
  beta_reduce
  rw [map_mul Matrix.GeneralLinearGroup.det, NumberField.TateGlobal.ideleNorm_mul, hdet a ha]
  exact TorusSliceBounds.slice_integrand_le ha hm (hmB k hk) hσ

end TorusSliceBoundsGL3

end

section

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction
open scoped ENNReal

namespace WhittakerMeasurability

section

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

private theorem continuous_upperUnipotent3 :
    Continuous fun t : A × A × A => upperUnipotent3 t.1 t.2.1 t.2.2 := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent3] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [upperUnipotent3] <;> fun_prop

variable {G : Type*} [TopologicalSpace G] [Group G] [ContinuousMul G] [MeasurableSpace G] [BorelSpace G]
variable {R : Type*} [TopologicalSpace R] [AddCommGroup R] [IsTopologicalAddGroup R] [MeasurableSpace R]
  [BorelSpace R] [SecondCountableTopology R]

private theorem measurable_integral_integral_integral_of_continuous (ν : Measure R) [SFinite ν]
    (n : R × R × R → G) (hn : Continuous n) (F : G → ℂ) (hF : Continuous F) (ψ : R → ℂ) (hψ : Continuous ψ) :
    Measurable fun g : G => ∫ x, ∫ y, ∫ z, F (n (x, y, z) * g) * ψ (-(x + y)) ∂ν ∂ν ∂ν := by
  have h0 : StronglyMeasurable fun p : ((G × R) × R) × R =>
      F (n (p.1.1.2, p.1.2, p.2) * p.1.1.1) * ψ (-(p.1.1.2 + p.1.2)) := by
    refine Continuous.stronglyMeasurable ?_
    fun_prop
  have h1 : StronglyMeasurable fun p : (G × R) × R => ∫ z, F (n (p.1.2, p.2, z) * p.1.1) * ψ (-(p.1.2 + p.2)) ∂ν :=
    h0.integral_prod_right'
  have h2 : StronglyMeasurable fun p : G × R => ∫ y, ∫ z, F (n (p.2, y, z) * p.1) * ψ (-(p.2 + y)) ∂ν ∂ν :=
    h1.integral_prod_right'
  have h3 : StronglyMeasurable fun g : G => ∫ x, ∫ y, ∫ z, F (n (x, y, z) * g) * ψ (-(x + y)) ∂ν ∂ν ∂ν :=
    h2.integral_prod_right'
  exact h3.measurable

end

section

private theorem secondCountableTopology_adelicGL3 : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI := NumberField.AdeleRing.secondCountableTopology ℚ
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private theorem measurable_whittaker3_production (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : Continuous F) :
    @Measurable _ _ (NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ) _
      (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) psiQ F) := by
  letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdeleRing.secondCountableTopology ℚ
  haveI : IsProbabilityMeasure
      (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
        (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)) :=
    AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ
  exact measurable_integral_integral_integral_of_continuous
    (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
      (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ))
    (fun t => upperUnipotent3 t.1 t.2.1 t.2.2) continuous_upperUnipotent3 F hF (fun r => psiQ r) continuous_psiQ

end

section

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

private theorem lintegral_adelicGLHaar_eq_lintegral_lintegral_mul_out
    (h : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ g, h g ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) =
      ∫⁻ q, (∫⁻ x : WhittakerBlock.unipotentSubgroup3, h ((x : AdelicGL 3 (𝓞 ℚ) ℚ) * q.out)
        ∂WhittakerBlock.unipotentHaar3) ∂WhittakerBlock.quotientMeasure := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI := secondCountableTopology_adelicGL3
  haveI := WhittakerBlock.isHaarMeasure_unipotentHaar3
  haveI := WhittakerBlock.isMulRightInvariant_unipotentHaar3
  exact HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out _ _ WhittakerBlock.isClosed_unipotentSubgroup3 _ h hh

private theorem det_upperUnipotent3 (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    Matrix.GeneralLinearGroup.det (upperUnipotent3 x y z) = 1 := by
  ext
  simp [Matrix.det_fin_three]

private theorem coe_upperUnipotent3_mul_apply_two (x y z : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (j : Fin 3) :
    ((upperUnipotent3 x y z * g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j =
      (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j := by
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem right_integrand_unipotent_mul (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g)
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (σ : ℝ) (x : WhittakerBlock.unipotentSubgroup3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F ((x : AdelicGL 3 (𝓞 ℚ) ℚ) * g)‖₊ : ℝ≥0∞) ^ 2 *
      (‖Φ fun j : Fin 3 => (((x : AdelicGL 3 (𝓞 ℚ) ℚ) * g : AdelicGL 3 (𝓞 ℚ) ℚ) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ
        (Matrix.GeneralLinearGroup.det ((x : AdelicGL 3 (𝓞 ℚ) ℚ) * g)) ^ σ) =
    (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F g‖₊ : ℝ≥0∞) ^ 2 *
      (‖Φ fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) := by
  obtain ⟨hequiv, hnorm⟩ :=
    whittaker3_upperUnipotent3_mul_and_norm_whittaker3_unipotentSubgroup3_mul F haut
  have hW : (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
      NumberField.StandardAddChar.psiQ F ((x : AdelicGL 3 (𝓞 ℚ) ℚ) * g)‖₊ : ℝ≥0∞) =
      (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
        NumberField.StandardAddChar.psiQ F g‖₊ : ℝ≥0∞) := by
    congr 1
    exact NNReal.eq (hnorm (x : AdelicGL 3 (𝓞 ℚ) ℚ) x.2 g)
  obtain ⟨a, b, c, hx⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff (x : AdelicGL 3 (𝓞 ℚ) ℚ)).mp x.2
  have hrow : (fun j : Fin 3 => (((x : AdelicGL 3 (𝓞 ℚ) ℚ) * g : AdelicGL 3 (𝓞 ℚ) ℚ) :
      Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j) =
      fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j := by
    funext j
    rw [hx]
    exact coe_upperUnipotent3_mul_apply_two a b c g j
  have hdet : Matrix.GeneralLinearGroup.det ((x : AdelicGL 3 (𝓞 ℚ) ℚ) * g) = Matrix.GeneralLinearGroup.det g := by
    rw [map_mul, hx, det_upperUnipotent3, one_mul]
  rw [hW, hrow, hdet]

end

section

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

private theorem continuous_det_adelicGL3 :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => Matrix.GeneralLinearGroup.det g := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
        ((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).det) := Units.continuous_val.matrix_det
    exact h.congr fun g => (Matrix.GeneralLinearGroup.val_det_apply g).symm
  · have h : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
        (((g⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).det) :=
      (Units.continuous_val.comp continuous_inv).matrix_det
    refine h.congr fun g => ?_
    rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]

private theorem measurable_right_integrand (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : Continuous F)
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (hΦ : Measurable Φ) (σ : ℝ) :
    Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
          NumberField.StandardAddChar.psiQ F g‖₊ : ℝ≥0∞) ^ 2 *
        (‖Φ fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) := by
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdeleRing.secondCountableTopology ℚ
  have h1 := measurable_whittaker3_production F hF
  have h2 : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      fun j : Fin 3 => (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j :=
    (continuous_pi fun j => Units.continuous_val.matrix_elem 2 j).measurable
  have h3 : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) :=
    ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp continuous_det_adelicGL3).measurable
  exact ((h1.nnnorm.coe_nnreal_ennreal.pow_const 2).mul (hΦ.comp h2).nnnorm.coe_nnreal_ennreal).mul
    (ENNReal.measurable_ofReal.comp (h3.pow_const σ))

end

end WhittakerMeasurability

end

section

open Matrix IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.CubicInduction
open scoped ENNReal NNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

noncomputable section

namespace TorusConjugation

section

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A]
  [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular]

private theorem map_constSMul_eq_inv_distribHaarChar_smul (g : G) :
    μ.map (fun x : A => g • x) = ((distribHaarChar A g)⁻¹ : ℝ≥0∞) • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_smul g) hs, Measure.smul_apply, smul_eq_mul,
    Set.preimage_smul, ← distribHaarChar_mul μ g⁻¹ s, map_inv, ENNReal.coe_inv]
  exact (distribHaarChar_pos (g := g)).ne'

variable [SFinite μ]

private theorem map_prod₃_constSMul (g₁ g₂ g₃ : G) :
    (μ.prod (μ.prod μ)).map (fun p : A × A × A => (g₁ • p.1, g₂ • p.2.1, g₃ • p.2.2)) =
      ((distribHaarChar A g₁ : ℝ≥0∞)⁻¹ * ((distribHaarChar A g₂ : ℝ≥0∞)⁻¹ *
        (distribHaarChar A g₃ : ℝ≥0∞)⁻¹)) • (μ.prod (μ.prod μ)) := by
  have h23 : (μ.prod μ).map (fun p : A × A => (g₂ • p.1, g₃ • p.2)) =
      ((distribHaarChar A g₂ : ℝ≥0∞)⁻¹ * (distribHaarChar A g₃ : ℝ≥0∞)⁻¹) • (μ.prod μ) := by
    have := Measure.map_prod_map μ μ (measurable_const_smul g₂) (measurable_const_smul g₃)
    rw [map_constSMul_eq_inv_distribHaarChar_smul, map_constSMul_eq_inv_distribHaarChar_smul,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at this
    convert this.symm using 2 <;> try (funext p; rfl)
  have := Measure.map_prod_map μ (μ.prod μ) (measurable_const_smul g₁)
    ((measurable_const_smul g₂).prodMap (measurable_const_smul g₃))
  rw [map_constSMul_eq_inv_distribHaarChar_smul, Measure.prod_smul_left] at this
  have h23' : (μ.prod μ).map (Prod.map (fun x : A => g₂ • x) (fun x : A => g₃ • x)) =
      ((distribHaarChar A g₂ : ℝ≥0∞)⁻¹ * (distribHaarChar A g₃ : ℝ≥0∞)⁻¹) • (μ.prod μ) := by
    convert h23 using 2 <;> try (funext p; rfl)
  rw [h23', Measure.prod_smul_right, smul_smul] at this
  convert this.symm using 2 <;> try (funext p; rfl)

end

open AutomorphicForm.StandardKernel (ofReal)

private theorem _root_.TorusConjugation.ofReal_mul (r s : ℝ) : ofReal (r * s) = ofReal r * ofReal s :=
  funext fun _ => map_mul _ r s

p2m_export "TorusConjugation" "ofReal_mul"
private theorem _root_.TorusConjugation.ofReal_one : ofReal 1 = 1 :=
  funext fun _ => map_one _

p2m_export "TorusConjugation" "ofReal_one"
private theorem ofReal_zero : ofReal 0 = 0 :=
  funext fun _ => map_zero _

private def archScalarIdele (r : ℝ) (hr : r ≠ 0) : (AdeleRing (𝓞 ℚ) ℚ)ˣ where
  val := (⟨ofReal r, 1⟩ : AdeleRing (𝓞 ℚ) ℚ)
  inv := (⟨ofReal r⁻¹, 1⟩ : AdeleRing (𝓞 ℚ) ℚ)
  val_inv := by
    apply Prod.ext
    · show ofReal r * ofReal r⁻¹ = 1
      rw [← ofReal_mul, mul_inv_cancel₀ hr, ofReal_one]
    · show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * 1 = 1
      exact mul_one 1
  inv_val := by
    apply Prod.ext
    · show ofReal r⁻¹ * ofReal r = 1
      rw [← ofReal_mul, inv_mul_cancel₀ hr, ofReal_one]
    · show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * 1 = 1
      exact mul_one 1

private theorem archScalarIdele_fst (r : ℝ) (hr : r ≠ 0) :
    ((archScalarIdele r hr : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = ofReal r := rfl

private theorem archScalarIdele_snd (r : ℝ) (hr : r ≠ 0) :
    ((archScalarIdele r hr : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 = 1 := rfl

private theorem archScalarIdele_mul (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    archScalarIdele (r * s) (mul_ne_zero hr hs) = archScalarIdele r hr * archScalarIdele s hs := by
  ext : 1
  apply Prod.ext
  · show ofReal (r * s) = ofReal r * ofReal s
    exact ofReal_mul r s
  · show (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 * 1
    exact (mul_one 1).symm

private theorem archScalarIdele_inv (r : ℝ) (hr : r ≠ 0) :
    (archScalarIdele r hr)⁻¹ = archScalarIdele r⁻¹ (inv_ne_zero hr) := by
  ext : 1
  rfl

private theorem ideleNorm_archScalarIdele (r : ℝ) (hr : r ≠ 0) :
    NumberField.TateGlobal.ideleNorm ℚ (archScalarIdele r hr) = |r| := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one ℚ _
      (archScalarIdele_snd r hr), Fintype.prod_subsingleton _ Rat.infinitePlace, archScalarIdele_fst]
  have hmult : (Rat.infinitePlace).mult = 1 := by
    simp [InfinitePlace.mult, Rat.isReal_infinitePlace]
  rw [hmult, pow_one]
  change ‖(InfinitePlace.Completion.ringEquivRealOfIsReal _).symm r‖ = |r|
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal (K := ℚ) Rat.infinitePlace)
  have h0 : ‖(InfinitePlace.Completion.ringEquivRealOfIsReal
      (IsTotallyReal.isReal (K := ℚ) Rat.infinitePlace)).symm r‖ =
      dist ((InfinitePlace.Completion.ringEquivRealOfIsReal
        (IsTotallyReal.isReal (K := ℚ) Rat.infinitePlace)).symm r) 0 := (dist_zero_right _).symm
  rw [h0, ← hiso.dist_eq, map_zero, ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    RingEquiv.apply_symm_apply, Real.dist_eq, sub_zero]

private theorem archRealMat3_diagonal (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    WhittakerBlock.archRealMat3 (fun i j => if i = j then a i else 0) =
      Matrix.diagonal fun i => ((archScalarIdele (a i) (ha i) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) := by
  ext i j
  unfold WhittakerBlock.archRealMat3 AutomorphicForm.archMatrixInclN
  by_cases h : i = j
  · subst h
    simp only [Matrix.of_apply, if_true, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    rfl
  · simp only [Matrix.of_apply, if_neg h, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h, ofReal_zero]
    rfl

private theorem isUnit_archRealMat3_diagonal (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 (fun i j => if i = j then a i else 0)) := by
  rw [archRealMat3_diagonal a ha, Matrix.isUnit_diagonal]
  exact isUnit_iff_exists_inv.mpr ⟨fun i => ((archScalarIdele (a i) (ha i))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ),
    funext fun i => (archScalarIdele (a i) (ha i)).mul_inv⟩

private theorem coe_archRealLift3_diagonal (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      Matrix.diagonal fun i => ((archScalarIdele (a i) (ha i) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos (isUnit_archRealMat3_diagonal a ha), IsUnit.unit_spec, archRealMat3_diagonal a ha]

private theorem archRealLift3_diagonal_eq (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) =
      ⟨Matrix.diagonal fun i => ((archScalarIdele (a i) (ha i) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ),
        Matrix.diagonal fun i => (((archScalarIdele (a i) (ha i))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ),
        by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact Units.mul_inv _,
        by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact Units.inv_mul _⟩ :=
  Units.ext (coe_archRealLift3_diagonal a ha)

private theorem coe_inv_archRealLift3_diagonal (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    (((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0))⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
        Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      Matrix.diagonal fun i => (((archScalarIdele (a i) (ha i))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) := by
  rw [archRealLift3_diagonal_eq a ha]; rfl

private theorem det_archRealLift3_diagonal (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) :
    Matrix.GeneralLinearGroup.det (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0)) =
      archScalarIdele (a 0) (ha 0) * archScalarIdele (a 1) (ha 1) * archScalarIdele (a 2) (ha 2) := by
  ext : 1
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_archRealLift3_diagonal a ha, Matrix.det_diagonal,
    Fin.prod_univ_three, Units.val_mul, Units.val_mul]

private theorem archRealLift3_diagonal_mul (a b : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then (a i * b i) else 0) =
      WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) *
        WhittakerBlock.archRealLift3 (fun i j => if i = j then b i else 0) := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_archRealLift3_diagonal a ha, coe_archRealLift3_diagonal b hb,
    coe_archRealLift3_diagonal (fun i => a i * b i) (fun i => mul_ne_zero (ha i) (hb i)), Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [archScalarIdele_mul, Units.val_mul]

private theorem diagonal_mul_upperUnipotent3_mul_diagonal_inv {A : Type*} [CommRing A] (d : Fin 3 → Aˣ) (x y z : A) :
    Matrix.diagonal (fun i => (d i : A)) * (upperUnipotent3 x y z : Matrix (Fin 3) (Fin 3) A) *
        Matrix.diagonal (fun i => (((d i)⁻¹ : Aˣ) : A)) =
      (upperUnipotent3 ((d 0 : A) * (((d 1)⁻¹ : Aˣ) : A) * x) ((d 1 : A) * (((d 2)⁻¹ : Aˣ) : A) * y)
          ((d 0 : A) * (((d 2)⁻¹ : Aˣ) : A) * z) : Matrix (Fin 3) (Fin 3) A) := by
  rw [upperUnipotent3_coe, upperUnipotent3_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal, Units.mul_inv] <;> ring

private theorem archRealLift3_mul_upperUnipotent3_mul_inv (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0)
    (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * upperUnipotent3 x y z *
        (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0))⁻¹ =
      upperUnipotent3
        ((archScalarIdele (a 0) (ha 0) * (archScalarIdele (a 1) (ha 1))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) • x)
        ((archScalarIdele (a 1) (ha 1) * (archScalarIdele (a 2) (ha 2))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) • y)
        ((archScalarIdele (a 0) (ha 0) * (archScalarIdele (a 2) (ha 2))⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) • z) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_archRealLift3_diagonal a ha, coe_inv_archRealLift3_diagonal a ha,
    diagonal_mul_upperUnipotent3_mul_diagonal_inv]
  rfl

section

open WhittakerBlock

private theorem archRealMat3_diagonal_eq (a : Fin 3 → ℝ) :
    archRealMat3 (fun i j => if i = j then a i else 0) =
      Matrix.diagonal fun i => (⟨ofReal (a i), 1⟩ : AdeleRing (𝓞 ℚ) ℚ) := by
  ext i j
  unfold WhittakerBlock.archRealMat3 AutomorphicForm.archMatrixInclN
  by_cases h : i = j
  · subst h
    simp only [Matrix.of_apply, if_true, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
  · simp only [Matrix.of_apply, if_neg h, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h, ofReal_zero]
    rfl

private theorem archRealLift3_diagonal_eq_one {a : Fin 3 → ℝ} {i : Fin 3} (hi : a i = 0) :
    archRealLift3 (fun i j => if i = j then a i else 0) = 1 := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_neg]
  rw [archRealMat3_diagonal_eq]
  intro h

  have h' : IsUnit (Matrix.diagonal fun i => (⟨ofReal (a i), 1⟩ : AdeleRing (𝓞 ℚ) ℚ)) := h
  have h2 : IsUnit (fun i => (⟨ofReal (a i), 1⟩ : AdeleRing (𝓞 ℚ) ℚ)) := Matrix.isUnit_diagonal.mp h'
  have h3 : IsUnit ((⟨ofReal (a i), 1⟩ : AdeleRing (𝓞 ℚ) ℚ)) :=
    h2.map (Pi.evalMonoidHom (fun _ : Fin 3 => AdeleRing (𝓞 ℚ) ℚ) i)
  have h1 : IsUnit (ofReal (a i)) := h3.map (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ))
  rw [hi, ofReal_zero] at h1
  exact not_isUnit_zero h1

private theorem continuousOn_archRealLift3_diagonal :
    ContinuousOn (fun a : Fin 3 → ℝ => archRealLift3 (fun i j => if i = j then a i else 0)) {a | ∀ i, a i ≠ 0} := by
  rw [Units.isEmbedding_embedProduct.isInducing.continuousOn_iff]
  have hval : Continuous fun d : Fin 3 → ℝ =>
      Matrix.diagonal fun i => (⟨ofReal (d i), 1⟩ : AdeleRing (𝓞 ℚ) ℚ) :=
    (continuous_pi fun i =>
      ((AutomorphicForm.StandardKernel.continuous_ofReal.comp (continuous_apply i)).prodMk
        continuous_const)).matrix_diagonal
  have hinv : ContinuousOn (fun a : Fin 3 → ℝ => fun i => (a i)⁻¹) {a | ∀ i, a i ≠ 0} :=
    continuousOn_pi.mpr fun i => ((continuous_apply i).continuousOn).inv₀ fun a ha => ha i
  refine ContinuousOn.congr (f := fun a : Fin 3 → ℝ =>
      ((Matrix.diagonal fun i => (⟨ofReal (a i), 1⟩ : AdeleRing (𝓞 ℚ) ℚ)),
        MulOpposite.op (Matrix.diagonal fun i => (⟨ofReal (a i)⁻¹, 1⟩ : AdeleRing (𝓞 ℚ) ℚ))))
    (hval.continuousOn.prodMk (MulOpposite.continuous_op.comp_continuousOn (hval.comp_continuousOn hinv))) ?_
  intro a ha
  exact Prod.ext (coe_archRealLift3_diagonal a ha) (congrArg MulOpposite.op (coe_inv_archRealLift3_diagonal a ha))

private theorem measurable_archRealLift3_diagonal :
    Measurable fun a : Fin 3 → ℝ => archRealLift3 (fun i j => if i = j then a i else 0) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  classical
  have hU : IsOpen {a : Fin 3 → ℝ | ∀ i, a i ≠ 0} := by
    rw [show {a : Fin 3 → ℝ | ∀ i, a i ≠ 0} = ⋂ i, {a | a i ≠ 0} by ext; simp]
    exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const
  have h := ContinuousOn.measurable_piecewise (s := {a : Fin 3 → ℝ | ∀ i, a i ≠ 0})
    continuousOn_archRealLift3_diagonal
    ((continuousOn_const (c := (1 : AdelicGL 3 (𝓞 ℚ) ℚ))).congr fun a ha => by
      obtain ⟨i, hi⟩ := not_forall.mp ha
      exact archRealLift3_diagonal_eq_one (not_not.mp hi))
    hU.measurableSet
  rwa [Set.piecewise_same] at h

end

section

open NumberField.AdelicHaar WhittakerBlock

private theorem mul_mul_inv_mem_unipotentSubgroup3 (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) {x : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hx : x ∈ unipotentSubgroup3) :
    archRealLift3 (fun i j => if i = j then a i else 0) * x * (archRealLift3 (fun i j => if i = j then a i else 0))⁻¹ ∈
      unipotentSubgroup3 := by
  obtain ⟨x, y, z, rfl⟩ := (mem_unipotentSubgroup3_iff _).mp hx
  rw [archRealLift3_mul_upperUnipotent3_mul_inv a ha]
  exact (mem_unipotentSubgroup3_iff _).mpr ⟨_, _, _, rfl⟩

private def torusConj (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) : unipotentSubgroup3 → unipotentSubgroup3 :=
  fun x => ⟨archRealLift3 (fun i j => if i = j then a i else 0) * x *
      (archRealLift3 (fun i j => if i = j then a i else 0))⁻¹, mul_mul_inv_mem_unipotentSubgroup3 a ha x.2⟩

private theorem coe_torusConj (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) (x : unipotentSubgroup3) :
    (torusConj a ha x : AdelicGL 3 (𝓞 ℚ) ℚ) =
      archRealLift3 (fun i j => if i = j then a i else 0) * x *
        (archRealLift3 (fun i j => if i = j then a i else 0))⁻¹ :=
  rfl

private theorem measurable_torusConj (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) : Measurable (torusConj a ha) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  exact ((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk

private theorem map_torusConj_unipotentHaar3 (a : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0)
    (hι : Measurable fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (⟨upperUnipotent3 t.1 t.2.1 t.2.2, Subgroup.subset_closure ⟨t, rfl⟩⟩ : unipotentSubgroup3)) :
    Measure.map (torusConj a ha) unipotentHaar3 =
      ((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)
            (archScalarIdele (a 0) (ha 0) * (archScalarIdele (a 1) (ha 1))⁻¹) : ℝ≥0∞)⁻¹ *
        ((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)
            (archScalarIdele (a 1) (ha 1) * (archScalarIdele (a 2) (ha 2))⁻¹) : ℝ≥0∞)⁻¹ *
          (distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)
            (archScalarIdele (a 0) (ha 0) * (archScalarIdele (a 2) (ha 2))⁻¹) : ℝ≥0∞)⁻¹)) • unipotentHaar3 := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ
  haveI : (adelicAddHaar (𝓞 ℚ) ℚ).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  set ρ₀₁ : (AdeleRing (𝓞 ℚ) ℚ)ˣ := archScalarIdele (a 0) (ha 0) * (archScalarIdele (a 1) (ha 1))⁻¹ with hρ₀₁
  set ρ₁₂ : (AdeleRing (𝓞 ℚ) ℚ)ˣ := archScalarIdele (a 1) (ha 1) * (archScalarIdele (a 2) (ha 2))⁻¹ with hρ₁₂
  set ρ₀₂ : (AdeleRing (𝓞 ℚ) ℚ)ˣ := archScalarIdele (a 0) (ha 0) * (archScalarIdele (a 2) (ha 2))⁻¹ with hρ₀₂

  set S : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ →
      AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ :=
    fun p => (ρ₀₁ • p.1, ρ₁₂ • p.2.1, ρ₀₂ • p.2.2) with hS
  have hSm : Measurable S :=
    ((measurable_const_smul ρ₀₁).comp measurable_fst).prodMk
      ((((measurable_const_smul ρ₁₂).comp (measurable_fst.comp measurable_snd))).prodMk
        ((measurable_const_smul ρ₀₂).comp (measurable_snd.comp measurable_snd)))

  have hinter : (torusConj a ha ∘ fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        (⟨upperUnipotent3 t.1 t.2.1 t.2.2, Subgroup.subset_closure ⟨t, rfl⟩⟩ : unipotentSubgroup3)) =
      (fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        (⟨upperUnipotent3 t.1 t.2.1 t.2.2, Subgroup.subset_closure ⟨t, rfl⟩⟩ : unipotentSubgroup3)) ∘ S := by
    funext t
    apply Subtype.ext
    simp only [Function.comp_apply, coe_torusConj, Subtype.coe_mk, hS]
    exact archRealLift3_mul_upperUnipotent3_mul_inv a ha t.1 t.2.1 t.2.2
  unfold WhittakerBlock.unipotentHaar3
  rw [Measure.map_map (measurable_torusConj a ha) hι, hinter, ← Measure.map_map hι hSm, hS,
    map_prod₃_constSMul (adelicAddHaar (𝓞 ℚ) ℚ) ρ₀₁ ρ₁₂ ρ₀₂, Measure.map_smul]

private theorem distribHaarChar_ratio (r s : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) :
    (distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (archScalarIdele r hr * (archScalarIdele s hs)⁻¹) : ℝ≥0∞) =
      ENNReal.ofReal (|r| / |s|) := by
  have h : ((distribHaarChar (AdeleRing (𝓞 ℚ) ℚ) (archScalarIdele r hr * (archScalarIdele s hs)⁻¹) : ℝ≥0) : ℝ) =
      |r| / |s| := by
    rw [archScalarIdele_inv, ← archScalarIdele_mul]
    change NumberField.TateGlobal.ideleNorm ℚ _ = _
    rw [ideleNorm_archScalarIdele, abs_mul, abs_inv, div_eq_mul_inv]
  rw [← h, ENNReal.ofReal_coe_nnreal]

end

end TorusConjugation

end

namespace TorusInputs

private theorem ideleNorm_det_archRealLift3_diagonal_of_mem_octant (a : Fin 3 → ℝ)
    (ha : a ∈ Set.pi Set.univ fun _ : Fin 3 => Set.Ioi (0 : ℝ)) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det
      (WhittakerBlock.archRealLift3 fun i j => if i = j then a i else 0)) = a 0 * a 1 * a 2 := by
  have h : ∀ i, a i ≠ 0 := fun i => (ha i (Set.mem_univ _)).ne'
  rw [TorusConjugation.det_archRealLift3_diagonal a h, NumberField.TateGlobal.ideleNorm_mul,
    NumberField.TateGlobal.ideleNorm_mul, TorusConjugation.ideleNorm_archScalarIdele,
    TorusConjugation.ideleNorm_archScalarIdele, TorusConjugation.ideleNorm_archScalarIdele,
    abs_of_pos (ha 0 (Set.mem_univ _)), abs_of_pos (ha 1 (Set.mem_univ _)), abs_of_pos (ha 2 (Set.mem_univ _))]

private theorem continuousOn_torusLift_octant :
    ContinuousOn (fun a : Fin 3 → ℝ => WhittakerBlock.archRealLift3 fun i j => if i = j then a i else 0)
      (Set.pi Set.univ fun _ : Fin 3 => Set.Ioi (0 : ℝ)) :=
  TorusConjugation.continuousOn_archRealLift3_diagonal.mono fun _ ha i => (ha i (Set.mem_univ _)).ne'

end TorusInputs

end

section

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace FibreConstant

private def octant : Set (Fin 3 → ℝ) := Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)

private theorem mem_octant {a : Fin 3 → ℝ} : a ∈ octant ↔ ∀ i, 0 < a i := by
  simp [octant, Set.mem_pi]

private theorem measurableSet_octant : MeasurableSet octant :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

private def scaleEquiv (c : Fin 3 → ℝ) (hc : c ∈ octant) : (Fin 3 → ℝ) ≃ᵐ (Fin 3 → ℝ) where
  toFun a := c * a
  invFun a := fun i => (c i)⁻¹ * a i
  left_inv a := funext fun i => by simp [(mem_octant.mp hc i).ne']
  right_inv a := funext fun i => by simp [(mem_octant.mp hc i).ne']
  measurable_toFun := measurable_const_mul c
  measurable_invFun := measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul _

private theorem coe_scaleEquiv (c : Fin 3 → ℝ) (hc : c ∈ octant) : ⇑(scaleEquiv c hc) = fun a => c * a := rfl

private theorem map_scaleEquiv_volume (c : Fin 3 → ℝ) (hc : c ∈ octant) :
    Measure.map (scaleEquiv c hc) volume = ENNReal.ofReal (∏ i, c i)⁻¹ • volume := by
  have hdet : LinearMap.det (Matrix.toLin' (Matrix.diagonal c)) = ∏ i, c i := by
    rw [LinearMap.det_toLin', Matrix.det_diagonal]
  have hne : LinearMap.det (Matrix.toLin' (Matrix.diagonal c)) ≠ 0 := by
    rw [hdet]; exact (Finset.prod_pos fun i _ => mem_octant.mp hc i).ne'
  have hfun : ⇑(scaleEquiv c hc) = ⇑(Matrix.toLin' (Matrix.diagonal c)) := by
    funext a
    rw [Matrix.toLin'_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  rw [hfun, Real.map_linearMap_volume_pi_eq_smul_volume_pi hne, hdet, abs_of_pos]
  exact inv_pos.mpr (Finset.prod_pos fun i _ => mem_octant.mp hc i)

private theorem setLIntegral_octant_eq_mul_setLIntegral_comp_mul (c : Fin 3 → ℝ) (hc : c ∈ octant)
    (F : (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ a in octant, F a = ENNReal.ofReal (∏ i, c i) * ∫⁻ a in octant, F (c * a) := by
  have hprod : 0 < ∏ i, c i := Finset.prod_pos fun i _ => mem_octant.mp hc i
  set e := scaleEquiv c hc with he
  have hpre : e ⁻¹' octant = octant := by
    ext a
    simp only [Set.mem_preimage, he, coe_scaleEquiv, mem_octant, Pi.mul_apply]
    exact ⟨fun h i => pos_of_mul_pos_right (h i) (mem_octant.mp hc i).le,
      fun h i => mul_pos (mem_octant.mp hc i) (h i)⟩
  have hκ : ENNReal.ofReal (∏ i, c i)⁻¹ ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; exact inv_pos.mpr hprod
  have hvol : (volume : Measure (Fin 3 → ℝ)) = ENNReal.ofReal (∏ i, c i) • Measure.map e volume := by
    rw [he, map_scaleEquiv_volume, smul_smul, ← ENNReal.ofReal_mul hprod.le, mul_inv_cancel₀ hprod.ne',
      ENNReal.ofReal_one, one_smul]
  calc ∫⁻ a in octant, F a
      = ∫⁻ a in octant, F a ∂(ENNReal.ofReal (∏ i, c i) • Measure.map e volume) := by rw [← hvol]
    _ = ENNReal.ofReal (∏ i, c i) * ∫⁻ a in octant, F a ∂(Measure.map e volume) := by
        rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    _ = ENNReal.ofReal (∏ i, c i) * ∫⁻ a in octant, F (c * a) := by
        congr 1
        rw [MeasurableEquiv.restrict_map, hpre, lintegral_map_equiv]
        rfl

section

variable {G : Type*} [Group G] [MeasurableSpace G]
variable (N : Subgroup G) (ν : Measure N)
variable (t : (Fin 3 → ℝ) → G) (w : (Fin 3 → ℝ) → ℝ≥0∞)

private def fibreWeight (E : Set G) (g : G) : ℝ≥0∞ :=
  ∫⁻ a in octant, E.indicator (fun _ => (1 : ℝ≥0∞)) ((t a)⁻¹ * g) * w a

private def fibreConst (E : Set G) (g : G) : ℝ≥0∞ :=
  ∫⁻ x : N, fibreWeight t w E ((x : G) * g) ∂ν

variable {N ν t w}

private theorem measurable_fibreWeight [MeasurableMul₂ G] [MeasurableInv G] (ht : Measurable t) (hw : Measurable w)
    {E : Set G} (hE : MeasurableSet E) : Measurable (fibreWeight t w E) := by
  unfold fibreWeight
  have h : Measurable fun p : G × (Fin 3 → ℝ) => E.indicator (fun _ => (1 : ℝ≥0∞)) ((t p.2)⁻¹ * p.1) * w p.2 :=
    ((measurable_const.indicator hE).comp ((ht.comp measurable_snd).inv.mul measurable_fst)).mul
      (hw.comp measurable_snd)
  exact h.lintegral_prod_right'

private theorem fibreConst_mul_of_mem [MeasurableMul N] [ν.IsMulRightInvariant] (E : Set G) {n : G} (hn : n ∈ N)
    (g : G) : fibreConst N ν t w E (n * g) = fibreConst N ν t w E g := by
  unfold fibreConst
  calc ∫⁻ x : N, fibreWeight t w E ((x : G) * (n * g)) ∂ν
      = ∫⁻ x : N, (fun y : N => fibreWeight t w E ((y : G) * g)) (x * ⟨n, hn⟩) ∂ν := by
        congr 1; funext x; simp only [Subgroup.coe_mul, mul_assoc]
    _ = ∫⁻ x : N, fibreWeight t w E ((x : G) * g) ∂ν :=
        lintegral_mul_right_eq_self (μ := ν) (fun y : N => fibreWeight t w E ((y : G) * g)) _

private theorem fibreConst_le_of_mem {B : Set G} {b : G} (hb : b ∈ B) :
    fibreConst N ν t w B b ≤ fibreConst N ν t w (B * B⁻¹) 1 := by
  unfold fibreConst fibreWeight
  refine lintegral_mono fun x => lintegral_mono fun a => mul_le_mul_left ?_ _
  by_cases h : (t a)⁻¹ * ((x : G) * b) ∈ B
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
    rw [mul_one]
    refine ⟨(t a)⁻¹ * ((x : G) * b), h, b⁻¹, Set.inv_mem_inv.mpr hb, ?_⟩
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  · rw [Set.indicator_of_notMem h]; exact zero_le

end

section

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable {N : Subgroup G} {ν : Measure N}
variable {t : (Fin 3 → ℝ) → G} {w : (Fin 3 → ℝ) → ℝ≥0∞}

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in

private theorem fibreWeight_torus_mul (ht_mul : ∀ a ∈ octant, ∀ b ∈ octant, t (a * b) = t a * t b)
    (hw_mul : ∀ a ∈ octant, ∀ b ∈ octant, w (a * b) = w a * w b) (hw_top : ∀ a, w a ≠ ⊤)
    (E : Set G) {c : Fin 3 → ℝ} (hc : c ∈ octant) (h : G) :
    fibreWeight t w E (t c * h) = ENNReal.ofReal (∏ i, c i) * w c * fibreWeight t w E h := by
  unfold fibreWeight
  rw [setLIntegral_octant_eq_mul_setLIntegral_comp_mul c hc, mul_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ (hw_top c)]
  refine setLIntegral_congr_fun measurableSet_octant fun a ha => ?_
  rw [ht_mul c hc a ha, hw_mul c hc a ha, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left, ← mul_assoc]
  ring

private theorem fibreConst_torus_mul (ht : Measurable t) (hw : Measurable w)
    (ht_mul : ∀ a ∈ octant, ∀ b ∈ octant, t (a * b) = t a * t b)
    (hw_mul : ∀ a ∈ octant, ∀ b ∈ octant, w (a * b) = w a * w b) (hw_top : ∀ a, w a ≠ ⊤)
    (κ : (Fin 3 → ℝ) → N → N) (hκm : ∀ a, Measurable (κ a))
    (hκ : ∀ a ∈ octant, ∀ x : N, ((κ a x : N) : G) = t a * x * (t a)⁻¹)
    (cmod : (Fin 3 → ℝ) → ℝ≥0∞) (hmap : ∀ a ∈ octant, Measure.map (κ a) ν = cmod a • ν)
    (hcancel : ∀ a ∈ octant, cmod a = ENNReal.ofReal (∏ i, a i) * w a)
    (hc0 : ∀ a ∈ octant, cmod a ≠ 0) (hctop : ∀ a ∈ octant, cmod a ≠ ⊤)
    {E : Set G} (hE : MeasurableSet E) {c : Fin 3 → ℝ} (hc : c ∈ octant) (g : G) :
    fibreConst N ν t w E (t c * g) = fibreConst N ν t w E g := by
  have hF : Measurable fun x : N => fibreWeight t w E ((x : G) * (t c * g)) :=
    (measurable_fibreWeight ht hw hE).comp (measurable_subtype_coe.mul_const _)
  have key : cmod c * fibreConst N ν t w E (t c * g) = cmod c * fibreConst N ν t w E g := by
    unfold fibreConst
    calc cmod c * ∫⁻ x : N, fibreWeight t w E ((x : G) * (t c * g)) ∂ν
        = ∫⁻ x : N, fibreWeight t w E ((x : G) * (t c * g)) ∂(cmod c • ν) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ = ∫⁻ x : N, fibreWeight t w E ((x : G) * (t c * g)) ∂(Measure.map (κ c) ν) := by rw [hmap c hc]
      _ = ∫⁻ x : N, fibreWeight t w E (((κ c x : N) : G) * (t c * g)) ∂ν := lintegral_map hF (hκm c)
      _ = ∫⁻ x : N, ENNReal.ofReal (∏ i, c i) * w c * fibreWeight t w E ((x : G) * g) ∂ν := by
          congr 1
          funext x
          rw [hκ c hc, ← fibreWeight_torus_mul ht_mul hw_mul hw_top E hc]
          congr 1
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = ENNReal.ofReal (∏ i, c i) * w c * ∫⁻ x : N, fibreWeight t w E ((x : G) * g) ∂ν :=
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hw_top c))
      _ = cmod c * ∫⁻ x : N, fibreWeight t w E ((x : G) * g) ∂ν := by rw [hcancel c hc]
  exact (ENNReal.mul_right_inj (hc0 c hc) (hctop c hc)).mp key

private theorem fibreConst_le [MeasurableMul N] [ν.IsMulRightInvariant] (ht : Measurable t) (hw : Measurable w)
    (ht_mul : ∀ a ∈ octant, ∀ b ∈ octant, t (a * b) = t a * t b)
    (hw_mul : ∀ a ∈ octant, ∀ b ∈ octant, w (a * b) = w a * w b) (hw_top : ∀ a, w a ≠ ⊤)
    (κ : (Fin 3 → ℝ) → N → N) (hκm : ∀ a, Measurable (κ a))
    (hκ : ∀ a ∈ octant, ∀ x : N, ((κ a x : N) : G) = t a * x * (t a)⁻¹)
    (cmod : (Fin 3 → ℝ) → ℝ≥0∞) (hmap : ∀ a ∈ octant, Measure.map (κ a) ν = cmod a • ν)
    (hcancel : ∀ a ∈ octant, cmod a = ENNReal.ofReal (∏ i, a i) * w a)
    (hc0 : ∀ a ∈ octant, cmod a ≠ 0) (hctop : ∀ a ∈ octant, cmod a ≠ ⊤)
    {B : Set G} (hB : MeasurableSet B) (g : G) :
    fibreConst N ν t w B g ≤ fibreConst N ν t w (B * B⁻¹) 1 := by
  by_cases hex : ∃ x : N, ∃ a ∈ octant, (t a)⁻¹ * ((x : G) * g) ∈ B
  · obtain ⟨x₀, a₀, ha₀, hb₀⟩ := hex
    have hg : g = ((x₀⁻¹ : N) : G) * (t a₀ * ((t a₀)⁻¹ * ((x₀ : G) * g))) := by
      simp only [Subgroup.coe_inv, mul_inv_cancel_left, inv_mul_cancel_left]
    rw [hg, fibreConst_mul_of_mem (t := t) (w := w) B (x₀⁻¹).2,
      fibreConst_torus_mul ht hw ht_mul hw_mul hw_top κ hκm hκ cmod hmap hcancel hc0 hctop hB ha₀]
    exact fibreConst_le_of_mem hb₀
  · have h0 : fibreConst N ν t w B g = 0 := by
      unfold fibreConst
      have hzero : ∀ x : N, fibreWeight t w B ((x : G) * g) = 0 := fun x => by
        unfold fibreWeight
        rw [← lintegral_zero (μ := volume.restrict octant)]
        refine setLIntegral_congr_fun measurableSet_octant fun a ha => ?_
        rw [Set.indicator_of_notMem (fun hmem => hex ⟨x, a, ha, hmem⟩), zero_mul]
      simp only [hzero, lintegral_zero]
    rw [h0]
    exact zero_le

end

section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G]
variable {N : Subgroup G} {ν : Measure N}
variable {t : (Fin 3 → ℝ) → G} {w : (Fin 3 → ℝ) → ℝ≥0∞}

private theorem fibreConst_one_lt_top [IsFiniteMeasureOnCompacts ν] (hN : IsClosed (N : Set G))
    (ht_cont : ContinuousOn t octant)
    (hw_bdd : ∀ K ⊆ octant, IsCompact K → ∃ W : ℝ≥0∞, W ≠ ⊤ ∧ ∀ a ∈ K, w a ≤ W)
    {E : Set G} (hE : IsCompact E)
    (hbox : ∃ K ⊆ octant, IsCompact K ∧ ∀ a ∈ octant, ∀ x : N, (t a)⁻¹ * (x : G) ∈ E → a ∈ K) :
    fibreConst N ν t w E 1 < ⊤ := by
  obtain ⟨K, hKsub, hK, hKbox⟩ := hbox
  obtain ⟨W, hWtop, hW⟩ := hw_bdd K hKsub hK
  have hKG : IsCompact ((t '' K) * E) := (hK.image_of_continuousOn (ht_cont.mono hKsub)).mul hE
  set KN : Set N := ((↑) : N → G) ⁻¹' ((t '' K) * E) with hKN
  have hKNc : IsCompact KN := hN.isClosedEmbedding_subtypeVal.isCompact_preimage hKG
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKNm : MeasurableSet KN := hKNc.isClosed.measurableSet

  have hpt : ∀ x : N, ∀ a ∈ octant,
      E.indicator (fun _ => (1 : ℝ≥0∞)) ((t a)⁻¹ * ((x : G) * 1)) * w a ≤
        KN.indicator (fun _ => (1 : ℝ≥0∞)) x * K.indicator (fun _ => W) a := by
    intro x a ha
    by_cases hmem : (t a)⁻¹ * ((x : G) * 1) ∈ E
    · have haK : a ∈ K := hKbox a ha x (by simpa only [mul_one] using hmem)
      have hxK : x ∈ KN := by
        rw [hKN, Set.mem_preimage]
        refine ⟨t a, Set.mem_image_of_mem t haK, (t a)⁻¹ * ((x : G) * 1), hmem, ?_⟩
        simp only [mul_one, mul_inv_cancel_left]
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hxK, Set.indicator_of_mem haK, one_mul, one_mul]
      exact hW a haK
    · rw [Set.indicator_of_notMem hmem, zero_mul]
      exact zero_le
  calc fibreConst N ν t w E 1
      ≤ ∫⁻ x : N, (∫⁻ a in octant, KN.indicator (fun _ => (1 : ℝ≥0∞)) x * K.indicator (fun _ => W) a) ∂ν := by
        unfold fibreConst fibreWeight
        exact lintegral_mono fun x => setLIntegral_mono' measurableSet_octant fun a ha => hpt x a ha
    _ = ∫⁻ x : N, KN.indicator (fun _ => (1 : ℝ≥0∞)) x * (∫⁻ a in octant, K.indicator (fun _ => W) a) ∂ν := by
        congr 1
        funext x
        have h1 : KN.indicator (fun _ => (1 : ℝ≥0∞)) x ≤ 1 :=
          Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)
        rw [lintegral_const_mul' _ _ (h1.trans_lt ENNReal.one_lt_top).ne]
    _ ≤ ∫⁻ x : N, KN.indicator (fun _ => (1 : ℝ≥0∞)) x * (W * volume K) ∂ν := by
        refine lintegral_mono fun x => mul_le_mul_right ?_ _
        calc ∫⁻ a in octant, K.indicator (fun _ => W) a
            ≤ ∫⁻ a, K.indicator (fun _ => W) a := setLIntegral_le_lintegral _ _
          _ = W * volume K := lintegral_indicator_const hKm W
    _ = W * volume K * ν KN := by
        rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top hWtop hK.measure_lt_top.ne), lintegral_indicator_const hKNm,
          one_mul, mul_comm]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hWtop.lt_top hK.measure_lt_top) hKNc.measure_lt_top

end

section

private def torusWeight (a : Fin 3 → ℝ) : ℝ≥0∞ := ENNReal.ofReal (a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2)

private theorem torusWeight_mul {a b : Fin 3 → ℝ} (ha : a ∈ octant) (hb : b ∈ octant) :
    torusWeight (a * b) = torusWeight a * torusWeight b := by
  have ha' := mem_octant.mp ha
  have hb' := mem_octant.mp hb
  unfold torusWeight
  rw [← ENNReal.ofReal_mul (by
    have := ha' 0; have := ha' 1; have := ha' 2; positivity)]
  congr 1
  simp only [Pi.mul_apply]
  rw [Real.mul_rpow (ha' 0).le (hb' 0).le, Real.mul_rpow (ha' 1).le (hb' 1).le]
  ring

private theorem torusWeight_ne_top (a : Fin 3 → ℝ) : torusWeight a ≠ ⊤ := ENNReal.ofReal_ne_top

private theorem torusWeight_ne_zero {a : Fin 3 → ℝ} (ha : a ∈ octant) : torusWeight a ≠ 0 := by
  have ha' := mem_octant.mp ha
  unfold torusWeight
  rw [ENNReal.ofReal_ne_zero_iff]
  have := ha' 0; have := ha' 1; have := ha' 2
  positivity

private theorem measurable_torusWeight : Measurable torusWeight := by
  unfold torusWeight
  refine ENNReal.measurable_ofReal.comp ?_
  exact (((measurable_pi_apply 0).pow_const _).mul ((measurable_pi_apply 1).pow_const _)).mul (measurable_pi_apply 2)

private theorem continuousOn_torusWeight_toReal :
    ContinuousOn (fun a : Fin 3 → ℝ => a 0 ^ (-3 : ℝ) * a 1 ^ (-1 : ℝ) * a 2) octant := by
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) (continuous_apply 2).continuousOn
  · exact (continuous_apply 0).continuousOn.rpow_const fun a ha => Or.inl (mem_octant.mp ha 0).ne'
  · exact (continuous_apply 1).continuousOn.rpow_const fun a ha => Or.inl (mem_octant.mp ha 1).ne'

private theorem exists_forall_torusWeight_le {K : Set (Fin 3 → ℝ)} (hK : K ⊆ octant) (hKc : IsCompact K) :
    ∃ W : ℝ≥0∞, W ≠ ⊤ ∧ ∀ a ∈ K, torusWeight a ≤ W := by
  obtain ⟨M, hM⟩ := (hKc.image_of_continuousOn (continuousOn_torusWeight_toReal.mono hK)).isBounded.bddAbove
  refine ⟨ENNReal.ofReal M, ENNReal.ofReal_ne_top, fun a ha => ?_⟩
  exact ENNReal.ofReal_le_ofReal (hM (Set.mem_image_of_mem _ ha))

private theorem modulus_eq_prod_mul_torusWeight {a : Fin 3 → ℝ} (ha : a ∈ octant) :
    (ENNReal.ofReal (|a 0| / |a 1|))⁻¹ * ((ENNReal.ofReal (|a 1| / |a 2|))⁻¹ * (ENNReal.ofReal (|a 0| / |a 2|))⁻¹) =
      ENNReal.ofReal (∏ i, a i) * torusWeight a := by
  have ha' := mem_octant.mp ha
  have h0 := ha' 0; have h1 := ha' 1; have h2 := ha' 2
  rw [abs_of_pos h0, abs_of_pos h1, abs_of_pos h2]
  rw [← ENNReal.ofReal_inv_of_pos (div_pos h0 h1), ← ENNReal.ofReal_inv_of_pos (div_pos h1 h2),
    ← ENNReal.ofReal_inv_of_pos (div_pos h0 h2), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  unfold torusWeight
  rw [← ENNReal.ofReal_mul (Finset.prod_pos fun i _ => ha' i).le, Fin.prod_univ_three]
  congr 1
  rw [Real.rpow_neg h0.le, Real.rpow_neg_one, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

end

end FibreConstant

end

end

section

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction
open scoped ENNReal

namespace ArchBox

private noncomputable def archCoord : AdeleRing (𝓞 ℚ) ℚ →+* ℝ :=
  StandardKernel.realCoord.comp (NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ)

private theorem archCoord_apply (x : AdeleRing (𝓞 ℚ) ℚ) : archCoord x = StandardKernel.realCoord x.1 := rfl

private theorem continuous_realCoord : Continuous StandardKernel.realCoord := by
  have h : (StandardKernel.realCoord : InfiniteAdeleRing ℚ → ℝ) = fun x =>
      InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (x Rat.infinitePlace) :=
    funext StandardKernel.realCoord_apply
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply _)

private theorem continuous_archCoord : Continuous archCoord :=
  continuous_realCoord.comp (NumberField.AdelicLevel.continuous_adeleArch (𝓞 ℚ) ℚ)

private theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r := by
  rw [StandardKernel.realCoord_apply]
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private noncomputable def archMat (g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)).map archCoord

private theorem archMat_mul (g h : AdelicGL 3 (𝓞 ℚ) ℚ) : archMat (g * h) = archMat g * archMat h := by
  simp only [archMat, Units.val_mul]
  exact Matrix.map_mul

private theorem continuous_archMat : Continuous archMat :=
  Units.continuous_val.matrix_map continuous_archCoord

private theorem archMat_upperUnipotent3_apply_self (x y z : AdeleRing (𝓞 ℚ) ℚ) (i : Fin 3) :
    archMat (upperUnipotent3 x y z) i i = 1 := by
  fin_cases i <;> simp [archMat]

private theorem archMat_upperUnipotent3_det (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    (archMat (upperUnipotent3 x y z)).det = 1 := by
  simp [archMat, Matrix.det_fin_three]

private theorem archMat_one : archMat 1 = 1 := by
  simp only [archMat, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

private theorem archMat_det_ne_zero (g : AdelicGL 3 (𝓞 ℚ) ℚ) : (archMat g).det ≠ 0 := by
  intro h0
  have h1 : (archMat g).det * (archMat g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← archMat_mul, mul_inv_cancel, archMat_one, Matrix.det_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

private theorem archMat_eq_diagonal {t : (Fin 3 → ℝ) → AdelicGL 3 (𝓞 ℚ) ℚ} {a : Fin 3 → ℝ}
    (ht : ∀ i j, StandardKernel.realCoord
      (((t a : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 = if i = j then a i else 0) :
    archMat (t a) = Matrix.diagonal a := by
  ext i j
  rw [archMat, Matrix.map_apply, archCoord_apply, ht i j, Matrix.diagonal_apply]

private theorem mem_Icc_of_diag_det {a m : Fin 3 → ℝ} {D R₁ d₀ : ℝ} (hapos : ∀ i, 0 < a i)
    (hdiag : ∀ i, a i * m i = 1) (hdet : (∏ i, a i) * D = 1) (hm : ∀ i, |m i| ≤ R₁) (hD : d₀ ≤ |D|)
    (hR₁ : 0 < R₁) (hd₀ : 0 < d₀) (i : Fin 3) : a i ∈ Set.Icc R₁⁻¹ (R₁ ^ 2 / d₀) := by

  have hlow : ∀ j, R₁⁻¹ ≤ a j := by
    intro j
    have hmj : m j ≤ R₁ := (abs_le.mp (hm j)).2
    rw [inv_eq_one_div, div_le_iff₀ hR₁]
    calc (1 : ℝ) = a j * m j := (hdiag j).symm
      _ ≤ a j * R₁ := by gcongr; exact (hapos j).le

  have hprod : a 0 * a 1 * a 2 * |D| = 1 := by
    have h1 : |(∏ i, a i) * D| = 1 := by rw [hdet, abs_one]
    have h0 := hapos 0; have h1' := hapos 1; have h2 := hapos 2
    rw [abs_mul, Fin.prod_univ_three, abs_of_pos (by positivity)] at h1
    exact h1
  have hDpos : 0 < |D| := lt_of_lt_of_le hd₀ hD
  refine ⟨hlow i, ?_⟩
  rw [le_div_iff₀ hd₀]

  have key : a i * d₀ * (R₁⁻¹ * R₁⁻¹) ≤ 1 := by
    have h0 := hapos 0; have h1 := hapos 1; have h2 := hapos 2
    have hl0 := hlow 0; have hl1 := hlow 1; have hl2 := hlow 2
    have hinv : 0 < R₁⁻¹ := inv_pos.mpr hR₁
    fin_cases i
    · calc a 0 * d₀ * (R₁⁻¹ * R₁⁻¹) ≤ a 0 * |D| * (a 1 * a 2) := by gcongr
        _ = 1 := by rw [← hprod]; ring
    · calc a 1 * d₀ * (R₁⁻¹ * R₁⁻¹) ≤ a 1 * |D| * (a 0 * a 2) := by gcongr
        _ = 1 := by rw [← hprod]; ring
    · calc a 2 * d₀ * (R₁⁻¹ * R₁⁻¹) ≤ a 2 * |D| * (a 0 * a 1) := by gcongr
        _ = 1 := by rw [← hprod]; ring
  calc a i * d₀ = a i * d₀ * (R₁⁻¹ * R₁⁻¹) * R₁ ^ 2 := by field_simp
    _ ≤ 1 * R₁ ^ 2 := by gcongr
    _ = R₁ ^ 2 := one_mul _

private theorem exists_forall_mem_Icc_of_mem_compact (E : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hE : IsCompact E)
    (t : (Fin 3 → ℝ) → AdelicGL 3 (𝓞 ℚ) ℚ)
    (ht : ∀ a ∈ Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)), ∀ i j, StandardKernel.realCoord
      (((t a : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 = if i = j then a i else 0) :
    ∃ r R : ℝ, 0 < r ∧ ∀ a ∈ Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
      ∀ x : WhittakerBlock.unipotentSubgroup3, (t a)⁻¹ * (x : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ E →
        ∀ i, a i ∈ Set.Icc r R := by
  rcases E.eq_empty_or_nonempty with hEe | hEne
  · exact ⟨1, 1, one_pos, fun a _ x hx => by simp [hEe] at hx⟩
  have hent : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => fun i j : Fin 3 => archMat g i j :=
    continuous_pi fun i => continuous_pi fun j => continuous_archMat.matrix_elem i j
  obtain ⟨R₀, hR₀⟩ := hE.exists_bound_of_continuousOn hent.continuousOn
  obtain ⟨g₀, -, hg₀⟩ := hE.exists_isMinOn hEne (continuous_archMat.matrix_det.abs).continuousOn
  have hd₀ : 0 < |(archMat g₀).det| := abs_pos.mpr (archMat_det_ne_zero g₀)
  have hR₁ : (0 : ℝ) < max R₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max R₀ 1)⁻¹, max R₀ 1 ^ 2 / |(archMat g₀).det|, inv_pos.mpr hR₁, ?_⟩
  intro a ha x hx
  obtain ⟨u, v, w, hxu⟩ := (WhittakerBlock.mem_unipotentSubgroup3_iff (x : AdelicGL 3 (𝓞 ℚ) ℚ)).mp x.2
  set g : AdelicGL 3 (𝓞 ℚ) ℚ := (t a)⁻¹ * (x : AdelicGL 3 (𝓞 ℚ) ℚ) with hg
  have hxg : (x : AdelicGL 3 (𝓞 ℚ) ℚ) = t a * g := by rw [hg, mul_inv_cancel_left]
  have hmat : archMat (upperUnipotent3 u v w) = Matrix.diagonal a * archMat g := by
    rw [← hxu, hxg, archMat_mul, archMat_eq_diagonal (ht a ha)]
  have hdiag : ∀ i, a i * archMat g i i = 1 := by
    intro i
    have h1 := congrFun (congrFun hmat i) i
    rw [archMat_upperUnipotent3_apply_self, Matrix.diagonal_mul] at h1
    exact h1.symm
  have hdet : (∏ i, a i) * (archMat g).det = 1 := by
    have h1 := congrArg Matrix.det hmat
    rw [archMat_upperUnipotent3_det, Matrix.det_mul, Matrix.det_diagonal] at h1
    exact h1.symm
  have hm : ∀ i, |archMat g i i| ≤ max R₀ 1 := by
    intro i
    have h1 := hR₀ g hx
    have h2 := norm_le_pi_norm (fun i j : Fin 3 => archMat g i j) i
    have h3 := norm_le_pi_norm (fun j : Fin 3 => archMat g i j) i
    rw [Real.norm_eq_abs] at h3
    exact (h3.trans (h2.trans h1)).trans (le_max_left _ _)
  exact mem_Icc_of_diag_det (fun i => ha i (Set.mem_univ i)) hdiag hdet hm (hg₀ hx) hR₁ hd₀

end ArchBox

end

section

noncomputable section

namespace TorusInstance

open Matrix IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.CubicInduction
open WhittakerBlock NumberField.AdelicHaar TorusConjugation FibreConstant
open scoped ENNReal NNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

private def torusLift (a : Fin 3 → ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ := archRealLift3 (fun i j => if i = j then a i else 0)

private theorem ne_zero_of_mem_octant {a : Fin 3 → ℝ} (ha : a ∈ octant) (i : Fin 3) : a i ≠ 0 :=
  (mem_octant.mp ha i).ne'

private theorem torusLift_mul {a b : Fin 3 → ℝ} (ha : a ∈ octant) (hb : b ∈ octant) :
    torusLift (a * b) = torusLift a * torusLift b :=
  archRealLift3_diagonal_mul a b (ne_zero_of_mem_octant ha) (ne_zero_of_mem_octant hb)

private def torusConj' (a : Fin 3 → ℝ) : ↥unipotentSubgroup3 → ↥unipotentSubgroup3 :=
  if h : ∀ i, a i ≠ 0 then torusConj a h else id

private theorem coe_torusConj' {a : Fin 3 → ℝ} (ha : a ∈ octant) (x : ↥unipotentSubgroup3) :
    ((torusConj' a x : ↥unipotentSubgroup3) : AdelicGL 3 (𝓞 ℚ) ℚ) = torusLift a * x * (torusLift a)⁻¹ := by
  unfold torusConj'
  rw [dif_pos (ne_zero_of_mem_octant ha)]
  rfl

private theorem measurable_torusConj' (a : Fin 3 → ℝ) : Measurable (torusConj' a) := by
  unfold torusConj'
  split
  · exact measurable_torusConj a _
  · exact measurable_id

private theorem map_torusConj'_unipotentHaar3
    (hι : Measurable fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (⟨upperUnipotent3 t.1 t.2.1 t.2.2, Subgroup.subset_closure ⟨t, rfl⟩⟩ : unipotentSubgroup3))
    {a : Fin 3 → ℝ} (ha : a ∈ octant) :
    Measure.map (torusConj' a) unipotentHaar3 = (ENNReal.ofReal (∏ i, a i) * torusWeight a) • unipotentHaar3 := by
  have ha' := ne_zero_of_mem_octant ha
  unfold torusConj'
  rw [dif_pos ha', map_torusConj_unipotentHaar3 a ha' hι, distribHaarChar_ratio, distribHaarChar_ratio,
    distribHaarChar_ratio, modulus_eq_prod_mul_torusWeight ha]

private theorem realCoord_torusLift_apply {a : Fin 3 → ℝ} (ha : a ∈ Set.pi Set.univ fun _ : Fin 3 => Set.Ioi (0 : ℝ))
    (i j : Fin 3) :
    AutomorphicForm.StandardKernel.realCoord
        (((torusLift a : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 =
      if i = j then a i else 0 := by
  have ha' : ∀ i, a i ≠ 0 := ne_zero_of_mem_octant ha
  unfold torusLift
  rw [coe_archRealLift3_diagonal a ha']
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, if_pos rfl, archScalarIdele_fst]
    exact ArchBox.realCoord_ofReal (a i)
  · rw [Matrix.diagonal_apply_ne _ h, if_neg h]
    exact map_zero _

private theorem exists_forall_fibreConst_le [SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ)]
    (hι : Measurable fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (⟨upperUnipotent3 t.1 t.2.1 t.2.2, Subgroup.subset_closure ⟨t, rfl⟩⟩ : unipotentSubgroup3))
    {B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hB : IsCompact B) :
    ∃ C₀ : ℝ≥0∞, C₀ ≠ ⊤ ∧ ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ∫⁻ x : ↥unipotentSubgroup3, fibreWeight torusLift torusWeight B ((x : AdelicGL 3 (𝓞 ℚ) ℚ) * g)
        ∂unipotentHaar3 ≤ C₀ := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : MeasurableMul₂ (AdelicGL 3 (𝓞 ℚ) ℚ) := TorusSliceBoundsGL3.measurableMul₂_adelicGL3
  haveI : MeasurableInv (AdelicGL 3 (𝓞 ℚ) ℚ) := TorusSliceBoundsGL3.measurableInv_adelicGL3
  haveI : BorelSpace ↥unipotentSubgroup3 := Subtype.borelSpace _
  haveI : MeasurableMul ↥unipotentSubgroup3 := inferInstance
  haveI : unipotentHaar3.IsMulRightInvariant := isMulRightInvariant_unipotentHaar3
  haveI : unipotentHaar3.IsHaarMeasure := isHaarMeasure_unipotentHaar3
  have hBm : MeasurableSet B := hB.isClosed.measurableSet
  have hE : IsCompact (B * B⁻¹) := hB.mul hB.inv
  have ht : Measurable torusLift := measurable_archRealLift3_diagonal
  have hw : Measurable torusWeight := measurable_torusWeight
  have ht_mul : ∀ a ∈ octant, ∀ b ∈ octant, torusLift (a * b) = torusLift a * torusLift b :=
    fun a ha b hb => torusLift_mul ha hb
  have hw_mul : ∀ a ∈ octant, ∀ b ∈ octant, torusWeight (a * b) = torusWeight a * torusWeight b :=
    fun a ha b hb => torusWeight_mul ha hb
  have hκ : ∀ a ∈ octant, ∀ x : ↥unipotentSubgroup3,
      ((torusConj' a x : ↥unipotentSubgroup3) : AdelicGL 3 (𝓞 ℚ) ℚ) = torusLift a * x * (torusLift a)⁻¹ :=
    fun a ha x => coe_torusConj' ha x
  have hmap : ∀ a ∈ octant,
      Measure.map (torusConj' a) unipotentHaar3 = (ENNReal.ofReal (∏ i, a i) * torusWeight a) • unipotentHaar3 :=
    fun a ha => map_torusConj'_unipotentHaar3 hι ha
  have hc0 : ∀ a ∈ octant, ENNReal.ofReal (∏ i, a i) * torusWeight a ≠ 0 := fun a ha =>
    mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (Finset.prod_pos fun i _ => mem_octant.mp ha i))
      (torusWeight_ne_zero ha)
  have hctop : ∀ a ∈ octant, ENNReal.ofReal (∏ i, a i) * torusWeight a ≠ ⊤ := fun a _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (torusWeight_ne_top a)
  have ht_cont : ContinuousOn torusLift octant :=
    continuousOn_archRealLift3_diagonal.mono fun a ha => ne_zero_of_mem_octant ha
  obtain ⟨r, R, hr, hrR⟩ :=
    ArchBox.exists_forall_mem_Icc_of_mem_compact (B * B⁻¹) hE torusLift fun a ha => realCoord_torusLift_apply ha
  have hbox : ∃ K ⊆ octant, IsCompact K ∧ ∀ a ∈ octant, ∀ x : ↥unipotentSubgroup3,
      (torusLift a)⁻¹ * (x : AdelicGL 3 (𝓞 ℚ) ℚ) ∈ B * B⁻¹ → a ∈ K :=
    ⟨Set.pi Set.univ fun _ => Set.Icc r R,
      fun a ha => mem_octant.mpr fun i => hr.trans_le (Set.mem_univ_pi.mp ha i).1,
      isCompact_univ_pi fun _ => isCompact_Icc,
      fun a ha x hx => Set.mem_univ_pi.mpr (hrR a ha x hx)⟩
  refine ⟨fibreConst unipotentSubgroup3 unipotentHaar3 torusLift torusWeight (B * B⁻¹) 1,
    (fibreConst_one_lt_top isClosed_unipotentSubgroup3 ht_cont (fun K hK hKc => exists_forall_torusWeight_le hK hKc)
      hE hbox).ne,
    fun g => ?_⟩
  exact fibreConst_le ht hw ht_mul hw_mul torusWeight_ne_top torusConj' measurable_torusConj' hκ
    (fun a => ENNReal.ofReal (∏ i, a i) * torusWeight a) hmap (fun a _ => rfl) hc0 hctop hBm g

private theorem measurable_fibreWeight_torusLift [SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ)]
    {B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (hB : IsCompact B) : Measurable (fibreWeight torusLift torusWeight B) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : MeasurableMul₂ (AdelicGL 3 (𝓞 ℚ) ℚ) := TorusSliceBoundsGL3.measurableMul₂_adelicGL3
  haveI : MeasurableInv (AdelicGL 3 (𝓞 ℚ) ℚ) := TorusSliceBoundsGL3.measurableInv_adelicGL3
  exact measurable_fibreWeight measurable_archRealLift3_diagonal measurable_torusWeight hB.isClosed.measurableSet

private theorem measurable_upperUnipotent3_mk [SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ)] :
    Measurable fun t : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (⟨upperUnipotent3 t.1 t.2.1 t.2.2, Subgroup.subset_closure ⟨t, rfl⟩⟩ : unipotentSubgroup3) := by
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ
  exact (WhittakerMeasurability.continuous_upperUnipotent3 (A := AdeleRing (𝓞 ℚ) ℚ)).measurable.subtype_mk

end TorusInstance

end

section

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem solution
    (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hB : IsCompact B) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, Continuous F →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = F g) →
      ∀ Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ, Measurable Φ →
        ∀ σ : ℝ, σ ∈ Set.Icc (1 : ℝ) 2 →
        (letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
          ∫⁻ k in B, (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
              (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                    NumberField.StandardAddChar.psiQ F
                    (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖₊ : ℝ≥0∞) ^ 2 *
                (‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                    AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
                ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) ∂volume)
            ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤
          C * ∫⁻ q,
            ((‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                    NumberField.StandardAddChar.psiQ F q.out‖₊ : ℝ≥0∞) ^ 2 *
              (‖Φ fun j : Fin 3 => (q.out : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det q.out) ^ σ))
            ∂WhittakerBlock.quotientMeasure) := by
  haveI : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := WhittakerMeasurability.secondCountableTopology_adelicGL3
  haveI : BorelSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI : MeasurableMul₂ (AdelicGL 3 (𝓞 ℚ) ℚ) := TorusSliceBoundsGL3.measurableMul₂_adelicGL3
  obtain ⟨m, hm, hmB⟩ := TorusSliceBoundsGL3.exists_pos_forall_le_ideleNorm_det hB
    ((NumberField.TateGlobal.continuous_ideleNorm ℚ).comp WhittakerMeasurability.continuous_det_adelicGL3)
  obtain ⟨C₀, hC₀, hbound⟩ :=
    TorusInstance.exists_forall_fibreConst_le TorusInstance.measurable_upperUnipotent3_mk hB
  refine ⟨ENNReal.ofReal (max 1 m⁻¹ ^ 2) * C₀, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC₀, ?_⟩
  intro F hF haut Φ hΦ σ hσ
  exact TorusSliceBounds.le_mul_lintegral_out_of_fibre_bound
    (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) WhittakerBlock.quotientMeasure WhittakerBlock.unipotentHaar3
    Quotient.out measurable_subtype_coe WhittakerMeasurability.lintegral_adelicGLHaar_eq_lintegral_lintegral_mul_out
    (WhittakerMeasurability.measurable_right_integrand F hF Φ hΦ σ) (TorusInstance.measurable_fibreWeight_torusLift hB)
    (WhittakerMeasurability.right_integrand_unipotent_mul F haut Φ σ) hC₀ hbound
    (TorusSliceBoundsGL3.left_le_mul_lintegral_mul_fibre B hB.isClosed.measurableSet F Φ σ hσ
      (WhittakerMeasurability.measurable_right_integrand F hF Φ hΦ σ) TorusInputs.continuousOn_torusLift_octant
      TorusInputs.ideleNorm_det_archRealLift3_diagonal_of_mem_octant hm hmB)

end

end

#print axioms solution

end S_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_mul_lintegral_quotientMeasure
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_mul_lintegral_quotientMeasure (solution)
