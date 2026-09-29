-- Prove2me | solution 1 for NumberField.TateGlobal.measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2010a55c-1ad5-52b2-8cd0-3a0b7b6db53b

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_NumberField_IdeleProductMeasure
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Theorems.Thm_NumberField_Idele_exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity
import Theorems.Thm_NumberField_mixedEmbedding_fundamentalCone_setLIntegral_inv_norm_eq_volume_normLeOne_mul_log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.NumberField IsDedekindDomain NumberField.mixedEmbedding NumberField.InfinitePlace"
open scoped Classical ENNReal Pointwise

noncomputable section

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mixedEmbedding.norm_apply InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp Units.regulator_pos place Units.torsionOrder InfinitePlace.nrComplexPlaces mixedEmbedding InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace mixedEmbedding.continuous_norm Units.torsion AdeleRing Units.regulator mixedEmbedding.norm TateGlobal.ideleNorm TateGlobal.ideleNorm_pos TateGlobal.ideleNorm_mul AdeleRing.unitIdelesOutside AdeleRing.mem_unitIdelesOutside_iff Idele.partAt Idele.partAt_fst Idele.ideleBorel Idele.borelSpace_ideleBorel Idele.idelicHaar Idele.isHaarMeasure_idelicHaar Idele.isOpen_unitIdelesOutside Idele.measurable_partAt Idele.sPartMeasure AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm AdeleRing.distribHaarChar_algebraMap TateGlobal.continuous_ideleNorm AdeleRing.secondCountableTopology InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace Idele.exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "ideleNorm ideleNorm_pos ideleNorm_mul continuous_ideleNorm"
namespace UnitRegulatorVolume
p2m_open "NumberField.TateGlobal NumberField"

section ShellMass

variable (K : Type) [Field K] [NumberField K]

def shellV : Set (mixedSpace K) :=
  {x | (∀ w, ‖x.1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)) ∧ ∀ w, ‖x.2 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)}

def invN (x : mixedSpace K) : ℝ≥0∞ := ENNReal.ofReal (mixedEmbedding.norm x)⁻¹

theorem one_lt_exp_one : (1 : ℝ) < Real.exp 1 := by
  have h := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
  linarith

def fR (r : ℝ) : ℝ := if ‖r‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1) then ‖r‖⁻¹ else 0

def fC (z : ℂ) : ℝ := if ‖z‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1) then (‖z‖ ^ 2)⁻¹ else 0

theorem fR_nonneg (r : ℝ) : 0 ≤ fR r := by
  unfold fR; split_ifs <;> positivity

theorem fC_nonneg (z : ℂ) : 0 ≤ fC z := by
  unfold fC; split_ifs <;> positivity

theorem measurableSet_norm_mem_Icc (E : Type) [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] :
    MeasurableSet {x : E | ‖x‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} :=
  measurable_norm measurableSet_Icc

theorem isCompact_norm_mem_Icc (E : Type) [NormedAddCommGroup E] [ProperSpace E] :
    IsCompact {x : E | ‖x‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} :=
  (isCompact_closedBall (0 : E) (Real.exp 1)).of_isClosed_subset
    (isClosed_Icc.preimage continuous_norm) fun x hx => mem_closedBall_zero_iff.mpr hx.2

theorem fR_eq_indicator :
    fR = {x : ℝ | ‖x‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)}.indicator fun r => ‖r‖⁻¹ := by
  funext r
  simp only [fR, Set.indicator_apply, Set.mem_setOf_eq]

theorem fC_eq_indicator :
    fC = {x : ℂ | ‖x‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)}.indicator fun z => (‖z‖ ^ 2)⁻¹ := by
  funext z
  simp only [fC, Set.indicator_apply, Set.mem_setOf_eq]

theorem measurable_fR : Measurable fR := by
  rw [fR_eq_indicator]
  exact measurable_norm.inv.indicator (measurableSet_norm_mem_Icc ℝ)

theorem measurable_fC : Measurable fC := by
  rw [fC_eq_indicator]
  exact (measurable_norm.pow_const 2).inv.indicator (measurableSet_norm_mem_Icc ℂ)

theorem integrableOn_inv_norm (s : Set ℝ) (hs : ∀ r ∈ s, r ≠ 0) (hc : IsCompact s) :
    IntegrableOn (fun r : ℝ => ‖r‖⁻¹) s :=
  ContinuousOn.integrableOn_compact hc
    ((continuous_norm.continuousOn).inv₀ fun r hr => norm_ne_zero_iff.mpr (hs r hr))

theorem integrable_fR : Integrable fR := by
  rw [fR_eq_indicator, integrable_indicator_iff (measurableSet_norm_mem_Icc ℝ)]
  refine integrableOn_inv_norm _ (fun r hr h0 => ?_) (isCompact_norm_mem_Icc ℝ)
  have h1 : (1 : ℝ) ≤ ‖r‖ := hr.1
  rw [h0, norm_zero] at h1
  linarith

theorem integrable_fC : Integrable fC := by
  rw [fC_eq_indicator, integrable_indicator_iff (measurableSet_norm_mem_Icc ℂ)]
  refine ContinuousOn.integrableOn_compact (isCompact_norm_mem_Icc ℂ) ?_
  refine ((continuous_norm.pow 2).continuousOn).inv₀ fun z hz => pow_ne_zero _ ?_
  intro h0
  beta_reduce at h0
  have h1 : (1 : ℝ) ≤ ‖z‖ := hz.1
  rw [h0] at h1
  linarith

theorem integral_fR : ∫ r, fR r = 2 := by
  have e1 := one_lt_exp_one
  have hS : {x : ℝ | ‖x‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} =
      Set.Icc (-Real.exp 1) (-1) ∪ Set.Icc 1 (Real.exp 1) := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_Icc, Set.mem_union, Real.norm_eq_abs]
    constructor
    · intro hr
      rcases le_or_gt 0 r with h0 | h0
      · rw [abs_of_nonneg h0] at hr
        exact Or.inr hr
      · rw [abs_of_neg h0] at hr
        exact Or.inl ⟨by linarith [hr.2], by linarith [hr.1]⟩
    · rintro (hr | hr)
      · rw [abs_of_neg (by linarith [hr.2])]
        exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
      · rw [abs_of_pos (by linarith [hr.1])]
        exact hr
  have hpos : ∫ r in Set.Icc 1 (Real.exp 1), ‖r‖⁻¹ = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le e1.le,
      intervalIntegral.integral_congr (g := fun r => r⁻¹) ?_,
      integral_inv_of_pos one_pos (by positivity), div_one, Real.log_exp]
    intro r hr
    rw [Set.uIcc_of_le e1.le] at hr
    simp only [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le one_pos hr.1)]
  have hneg : ∫ r in Set.Icc (-Real.exp 1) (-1), ‖r‖⁻¹ = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have h := intervalIntegral.integral_comp_neg (a := -Real.exp 1) (b := -1) (fun r : ℝ => ‖r‖⁻¹)
    simp only [norm_neg, neg_neg] at h
    rw [h, intervalIntegral.integral_of_le e1.le, ← integral_Icc_eq_integral_Ioc]
    exact hpos
  rw [fR_eq_indicator, integral_indicator (measurableSet_norm_mem_Icc ℝ), hS,
    setIntegral_union ?_ measurableSet_Icc ?_ ?_, hneg, hpos]
  · norm_num
  · exact Set.disjoint_left.mpr fun r h1 h2 => by linarith [h1.2, h2.1]
  · exact integrableOn_inv_norm _ (fun r hr h0 => by rw [h0] at hr; linarith [hr.2]) isCompact_Icc
  · exact integrableOn_inv_norm _ (fun r hr h0 => by rw [h0] at hr; linarith [hr.1]) isCompact_Icc

theorem integral_fC : ∫ z, fC z = 2 * Real.pi := by
  have e1 := one_lt_exp_one
  rw [← Complex.integral_comp_polarCoord_symm, _root_.polarCoord_target]
  set g : ℝ → ℝ := fun r => if r ∈ Set.Icc (1 : ℝ) (Real.exp 1) then r⁻¹ else 0 with hg
  have hcongr : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      p.1 • fC (Complex.polarCoord.symm p) = g p.1 * (fun _ : ℝ => (1 : ℝ)) p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    simp only [Set.mem_Ioi] at hr
    simp only [fC, Complex.norm_polarCoord_symm, abs_of_pos hr, smul_eq_mul, mul_one, hg]
    split_ifs
    · field_simp
    · rw [mul_zero]
  rw [setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) hcongr,
    Measure.volume_eq_prod, setIntegral_prod_mul g fun _ : ℝ => (1 : ℝ)]
  have h1 : ∫ r in Set.Ioi (0 : ℝ), g r = 1 := by
    have hg' : g = (Set.Icc (1 : ℝ) (Real.exp 1)).indicator fun r => r⁻¹ := by
      funext r
      simp only [hg, Set.indicator_apply]
    have hsub : Set.Icc (1 : ℝ) (Real.exp 1) ⊆ Set.Ioi 0 := fun r hr => lt_of_lt_of_le one_pos hr.1
    rw [hg', setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsub,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le e1.le,
      integral_inv_of_pos one_pos (by positivity), div_one, Real.log_exp]
  have h2 : ∫ θ in Set.Ioo (-Real.pi) Real.pi, (fun _ : ℝ => (1 : ℝ)) θ = 2 * Real.pi := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  rw [h1, h2, one_mul]

theorem integral_pi_fR :
    ∫ y : ({w : InfinitePlace K // IsReal w} → ℝ), ∏ w, fR (y w) = 2 ^ nrRealPlaces K := by
  rw [volume_pi, integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (fun _ : {w : InfinitePlace K // IsReal w} => fR)]
  simp only [integral_fR, Finset.prod_const, Finset.card_univ, nrRealPlaces]

theorem integral_pi_fC :
    ∫ y : ({w : InfinitePlace K // IsComplex w} → ℂ), ∏ w, fC (y w) =
      (2 * Real.pi) ^ nrComplexPlaces K := by
  rw [volume_pi, integral_fintype_prod_eq_prod (𝕜 := ℝ)
    (fun _ : {w : InfinitePlace K // IsComplex w} => fC)]
  simp only [integral_fC, Finset.prod_const, Finset.card_univ, nrComplexPlaces]

theorem integrable_pi_fR :
    Integrable (fun y : ({w : InfinitePlace K // IsReal w} → ℝ) => ∏ w, fR (y w)) := by
  have h := Integrable.fintype_prod (f := fun _ : {w : InfinitePlace K // IsReal w} => fR)
    (μ := fun _ => volume) (fun _ => integrable_fR)
  rw [← volume_pi] at h
  exact h

theorem integrable_pi_fC :
    Integrable (fun y : ({w : InfinitePlace K // IsComplex w} → ℂ) => ∏ w, fC (y w)) := by
  have h := Integrable.fintype_prod (f := fun _ : {w : InfinitePlace K // IsComplex w} => fC)
    (μ := fun _ => volume) (fun _ => integrable_fC)
  rw [← volume_pi] at h
  exact h

theorem norm_eq_prod_mul_prod (x : mixedSpace K) :
    mixedEmbedding.norm x = (∏ w, ‖x.1 w‖) * ∏ w, ‖x.2 w‖ ^ 2 := by
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [normAtPlace_apply_of_isReal w.2, mult_isReal, pow_one]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [normAtPlace_apply_of_isComplex w.2, mult_isComplex]

theorem indicator_shellV_invN (x : mixedSpace K) :
    (shellV K).indicator (invN K) x =
      ENNReal.ofReal (∏ w, fR (x.1 w)) * ENNReal.ofReal (∏ w, fC (x.2 w)) := by
  by_cases hx : x ∈ shellV K
  · rw [Set.indicator_of_mem hx, invN, norm_eq_prod_mul_prod, mul_inv,
      ENNReal.ofReal_mul (inv_nonneg.mpr (Finset.prod_nonneg fun w _ => norm_nonneg _))]
    congr 2
    · rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [fR, if_pos (hx.1 w)]
    · rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [fC, if_pos (hx.2 w)]
  · rw [Set.indicator_of_notMem hx]
    simp only [shellV, Set.mem_setOf_eq, not_and_or, not_forall] at hx
    rcases hx with ⟨w, hw⟩ | ⟨w, hw⟩
    · rw [Finset.prod_eq_zero (Finset.mem_univ w) (by rw [fR, if_neg hw]), ENNReal.ofReal_zero,
        zero_mul]
    · rw [Finset.prod_eq_zero (Finset.mem_univ w) (by rw [fC, if_neg hw]), ENNReal.ofReal_zero,
        mul_zero]

theorem isCompact_shellV : IsCompact (shellV K) := by
  have h : shellV K = (Set.univ.pi fun _ => {r : ℝ | ‖r‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)}) ×ˢ
      (Set.univ.pi fun _ => {z : ℂ | ‖z‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)}) := by
    ext x
    simp only [shellV, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ_pi]
  rw [h]
  exact (isCompact_univ_pi fun _ => isCompact_norm_mem_Icc ℝ).prod
    (isCompact_univ_pi fun _ => isCompact_norm_mem_Icc ℂ)

theorem measurableSet_shellV : MeasurableSet (shellV K) :=
  (isCompact_shellV K).isClosed.measurableSet

theorem lintegral_shellV_invN :
    ∫⁻ x in shellV K, invN K x = 2 ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K := by
  rw [← lintegral_indicator (measurableSet_shellV K)]
  simp_rw [indicator_shellV_invN]
  have hmR : Measurable fun y : ({w : InfinitePlace K // IsReal w} → ℝ) =>
      ENNReal.ofReal (∏ w, fR (y w)) :=
    ENNReal.measurable_ofReal.comp
      (Finset.measurable_prod _ fun w _ => measurable_fR.comp (measurable_pi_apply w))
  have hmC : Measurable fun y : ({w : InfinitePlace K // IsComplex w} → ℂ) =>
      ENNReal.ofReal (∏ w, fC (y w)) :=
    ENNReal.measurable_ofReal.comp
      (Finset.measurable_prod _ fun w _ => measurable_fC.comp (measurable_pi_apply w))
  rw [Measure.volume_eq_prod, lintegral_prod_mul hmR.aemeasurable hmC.aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_pi_fR K)
      (ae_of_all _ fun y => Finset.prod_nonneg fun w _ => fR_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_pi_fC K)
      (ae_of_all _ fun y => Finset.prod_nonneg fun w _ => fC_nonneg _),
    integral_pi_fR, integral_pi_fC, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat,
    ENNReal.ofReal_pow (by positivity)]

theorem lintegral_shellV_inv_ofReal :
    ∫⁻ x in shellV K, (ENNReal.ofReal (mixedEmbedding.norm x))⁻¹ =
      2 ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K := by
  rw [← lintegral_shellV_invN]
  refine setLIntegral_congr_fun (measurableSet_shellV K) fun x hx => ?_
  have hpos : 0 < mixedEmbedding.norm x := by
    rw [norm_eq_prod_mul_prod]
    refine mul_pos (Finset.prod_pos fun w _ => lt_of_lt_of_le one_pos (hx.1 w).1)
      (Finset.prod_pos fun w _ => pow_pos (lt_of_lt_of_le one_pos (hx.2 w).1) _)
  rw [invN, ENNReal.ofReal_inv_of_pos hpos]

end ShellMass

section Idelic

variable (K : Type) [Field K] [NumberField K]

def U0 : Set (AdeleRing (𝓞 K) K)ˣ :=
  {u | ∀ v : HeightOneSpectrum (𝓞 K),
    ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
    (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
      v.adicCompletionIntegers K}

abbrev Ugrp : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K)))

abbrev Kx : Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range

abbrev Egrp : Subgroup (AdeleRing (𝓞 K) K)ˣ := Kx K ⊓ Ugrp K

def Sh : Set (AdeleRing (𝓞 K) K)ˣ :=
  {u | (∀ v : HeightOneSpectrum (𝓞 K),
      ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
      (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
        v.adicCompletionIntegers K) ∧
    ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)}

def band (a b : ℝ) : Set (AdeleRing (𝓞 K) K)ˣ := {x | NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b}

theorem mem_Ugrp_iff (u : (AdeleRing (𝓞 K) K)ˣ) : u ∈ Ugrp K ↔ u ∈ U0 K := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, forall_const]
  rfl

theorem coe_Ugrp : ((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) = U0 K :=
  Set.ext (mem_Ugrp_iff K)

def phi : (AdeleRing (𝓞 K) K)ˣ →* mixedSpace K where
  toFun u := InfiniteAdeleRing.ringEquiv_mixedSpace K ((u : AdeleRing (𝓞 K) K).1)
  map_one' := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace K (1 : InfiniteAdeleRing K) = 1
    exact map_one _
  map_mul' u v := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace K
        ((u : AdeleRing (𝓞 K) K).1 * (v : AdeleRing (𝓞 K) K).1) = _
    exact map_mul _ _ _

theorem phi_apply (u : (AdeleRing (𝓞 K) K)ˣ) :
    phi K u = InfiniteAdeleRing.ringEquiv_mixedSpace K ((u : AdeleRing (𝓞 K) K).1) := rfl

theorem continuous_phi : Continuous (phi K) :=
  (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K).continuous.comp
    (continuous_fst.comp Units.continuous_val)

theorem norm_phi_fst (u : (AdeleRing (𝓞 K) K)ˣ) (w : {w : InfinitePlace K // IsReal w}) :
    ‖(phi K u).1 w‖ = ‖(u : AdeleRing (𝓞 K) K).1 w.1‖ := by
  show ‖Completion.extensionEmbeddingOfIsReal w.2 ((u : AdeleRing (𝓞 K) K).1 w.1)‖ = _
  exact (Completion.isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _) _

theorem norm_phi_snd (u : (AdeleRing (𝓞 K) K)ˣ) (w : {w : InfinitePlace K // IsComplex w}) :
    ‖(phi K u).2 w‖ = ‖(u : AdeleRing (𝓞 K) K).1 w.1‖ := by
  show ‖Completion.extensionEmbedding w.1 ((u : AdeleRing (𝓞 K) K).1 w.1)‖ = _
  exact (Completion.isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) _

theorem norm_phi (u : (AdeleRing (𝓞 K) K)ˣ) :
    mixedEmbedding.norm (phi K u) = ∏ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult := by
  rw [mixedEmbedding.norm_apply]
  refine Finset.prod_congr rfl fun w _ => ?_
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw]
    exact congrArg (· ^ _) (norm_phi_fst K u ⟨w, hw⟩)
  · rw [normAtPlace_apply_of_isComplex hw]
    exact congrArg (· ^ _) (norm_phi_snd K u ⟨w, hw⟩)

theorem norm_snd_eq_one_of_mem_U0 {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ U0 K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ‖((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
  obtain ⟨h1, h2⟩ := hu v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  have h1' : ‖((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr h1
  have h2' : ‖(((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr h2
  have hmul : ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v *
      (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := by
    have h : (((u * u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v = 1 := by
      rw [mul_inv_cancel]; rfl
    exact h
  have hn := congrArg norm hmul
  rw [norm_mul, norm_one] at hn
  refine le_antisymm h1' ?_
  have hb : 0 ≤ ‖((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ := norm_nonneg _
  nlinarith

theorem ideleNorm_eq_norm_phi {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ U0 K) :
    NumberField.TateGlobal.ideleNorm K u = mixedEmbedding.norm (phi K u) := by
  rw [norm_phi]
  have h := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm K u
  rw [finprod_eq_one_of_forall_eq_one (fun v => norm_snd_eq_one_of_mem_U0 K hu v), mul_one] at h
  exact h

theorem norm_phi_pos_of_mem_U0 {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ U0 K) :
    0 < mixedEmbedding.norm (phi K u) := by
  rw [← ideleNorm_eq_norm_phi K hu]
  exact NumberField.TateGlobal.ideleNorm_pos u

def coneI : Set (AdeleRing (𝓞 K) K)ˣ := U0 K ∩ phi K ⁻¹' fundamentalCone K

theorem Sh_eq : Sh K = U0 K ∩ phi K ⁻¹' shellV K := by
  ext u
  simp only [Sh, shellV, U0, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, norm_phi_fst,
    norm_phi_snd]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun w => h2 w.1, fun w => h2 w.1⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun w => ?_⟩
    obtain hw | hw := isReal_or_isComplex w
    exacts [h2 ⟨w, hw⟩, h3 ⟨w, hw⟩]

theorem coneI_inter_band (a b : ℝ) :
    coneI K ∩ band K a b =
      U0 K ∩ phi K ⁻¹' (fundamentalCone K ∩ {x | mixedEmbedding.norm x ∈ Set.Icc a b}) := by
  ext u
  simp only [coneI, band, Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hU, hc⟩, hb⟩
    exact ⟨hU, hc, by rwa [← ideleNorm_eq_norm_phi K hU]⟩
  · rintro ⟨hU, hc, hb⟩
    exact ⟨⟨hU, hc⟩, by rwa [ideleNorm_eq_norm_phi K hU]⟩

def iota : (𝓞 K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).comp
    (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K))

theorem iota_mem_Kx (η : (𝓞 K)ˣ) : iota K η ∈ Kx K :=
  ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) η, rfl⟩

theorem coe_snd_algebraMap (k : K) (v : HeightOneSpectrum (𝓞 K)) :
    ((algebraMap K (AdeleRing (𝓞 K) K) k).2 : FiniteAdeleRing (𝓞 K) K) v = (k : v.adicCompletion K) := rfl

theorem mem_integers_iff (k : K) (v : HeightOneSpectrum (𝓞 K)) :
    ((algebraMap K (AdeleRing (𝓞 K) K) k).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ↔
      v.valuation K k ≤ 1 := by
  rw [coe_snd_algebraMap, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem iota_mem_U0 (η : (𝓞 K)ˣ) : iota K η ∈ U0 K := by
  intro v
  constructor
  · show ((algebraMap K (AdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K η)).2 : FiniteAdeleRing (𝓞 K) K) v ∈ _
    rw [mem_integers_iff]
    exact HeightOneSpectrum.valuation_le_one v _
  · show ((algebraMap K (AdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K ↑η⁻¹)).2 : FiniteAdeleRing (𝓞 K) K) v ∈ _
    rw [mem_integers_iff]
    exact HeightOneSpectrum.valuation_le_one v _

theorem iota_mem_E (η : (𝓞 K)ˣ) : iota K η ∈ Egrp K :=
  ⟨iota_mem_Kx K η, (mem_Ugrp_iff K _).mpr (iota_mem_U0 K η)⟩

scoped instance nontrivial_adeleRing : Nontrivial (AdeleRing (𝓞 K) K) :=
  inferInstanceAs (Nontrivial (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

theorem iota_injective : Function.Injective (iota K) := by
  intro a b h
  have h' : (algebraMap K (AdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K a) : AdeleRing (𝓞 K) K) =
      algebraMap K (AdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K b) := congrArg Units.val h
  exact Units.ext (IsFractionRing.injective (𝓞 K) K ((algebraMap K (AdeleRing (𝓞 K) K)).injective h'))

theorem exists_iota_eq_of_mem_E {g : (AdeleRing (𝓞 K) K)ˣ} (hg : g ∈ Egrp K) : ∃ η, iota K η = g := by
  obtain ⟨⟨k, rfl⟩, hU'⟩ := hg
  have hU : Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k ∈ U0 K :=
    (mem_Ugrp_iff K _).mp hU'
  have hk : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (k : K) ≤ 1 := fun v =>
    (mem_integers_iff K (k : K) v).mp (hU v).1
  have hk' : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((k⁻¹ : Kˣ) : K) ≤ 1 := fun v =>
    (mem_integers_iff K ((k⁻¹ : Kˣ) : K) v).mp (hU v).2
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (k : K) hk
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((k⁻¹ : Kˣ) : K) hk'
  have hxy : x * y = 1 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [map_mul, map_one]
    change (algebraMap (𝓞 K) K) x * (algebraMap (𝓞 K) K) y = 1
    rw [hx, hy]
    exact k.mul_inv
  have hyx : y * x = 1 := by rw [mul_comm]; exact hxy
  refine ⟨⟨x, y, hxy, hyx⟩, Units.ext ?_⟩
  show (algebraMap K (AdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K x) : AdeleRing (𝓞 K) K) =
    algebraMap K (AdeleRing (𝓞 K) K) k
  rw [hx]

theorem phi_iota (η : (𝓞 K)ˣ) : phi K (iota K η) = mixedEmbedding K (algebraMap (𝓞 K) K η) := by
  rw [phi_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem phi_iota_mul (η : (𝓞 K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ) :
    phi K (iota K η * u) = η • phi K u := by
  rw [map_mul, phi_iota, unitSMul_smul]

theorem inv_iota_mul_mem_coneI_iff {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ U0 K) {η₀ : (𝓞 K)ˣ}
    (hη₀ : η₀ • phi K u ∈ fundamentalCone K) (η : (𝓞 K)ˣ) :
    (iota K η)⁻¹ * u ∈ coneI K ↔ η₀ * η ∈ Units.torsion K := by
  have hU : (iota K η)⁻¹ * u ∈ U0 K := by
    rw [← mem_Ugrp_iff] at hu ⊢
    exact mul_mem (inv_mem ((iota_mem_E K η).2)) hu
  have hη : η⁻¹ = η⁻¹ * η₀⁻¹ * η₀ := by rw [inv_mul_cancel_right]
  have hphi : phi K ((iota K η)⁻¹ * u) = (η⁻¹ * η₀⁻¹) • (η₀ • phi K u) := by
    rw [← map_inv, phi_iota_mul]
    conv_lhs => rw [hη]
    rw [unitSMul_smul, unitSMul_smul, unitSMul_smul, Units.val_mul, map_mul, map_mul, mul_assoc]
  simp only [coneI, Set.mem_inter_iff, Set.mem_preimage, hU, true_and, hphi]
  rw [fundamentalCone.unit_smul_mem_iff_mem_torsion hη₀, ← mul_inv_rev, inv_mem_iff]

theorem tsum_indicator_coneI {u : (AdeleRing (𝓞 K) K)ˣ} (hu : u ∈ U0 K) :
    ∑' g : Egrp K, (coneI K).indicator (fun _ => (1 : ℝ≥0∞)) ((g⁻¹ : Egrp K) • u) =
      (Units.torsionOrder K : ℝ≥0∞) := by
  haveI := Fintype.ofFinite (NumberField.Units.torsion K)
  obtain ⟨η₀, hη₀⟩ := fundamentalCone.exists_unit_smul_mem (norm_phi_pos_of_mem_U0 K hu).ne'

  let emb : Units.torsion K → Egrp K := fun ζ => ⟨iota K (η₀⁻¹ * ζ), iota_mem_E K _⟩
  have hemb : Function.Injective emb := by
    intro ζ₁ ζ₂ h
    have h1 : iota K (η₀⁻¹ * ζ₁) = iota K (η₀⁻¹ * ζ₂) := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (iota_injective K h1))
  let S : Finset (Egrp K) := Finset.univ.image emb
  have hS : ∀ g : Egrp K, (g⁻¹ : Egrp K) • u ∈ coneI K ↔ g ∈ S := by
    intro g
    obtain ⟨η, hη⟩ := exists_iota_eq_of_mem_E K g.2
    have hg : ((g⁻¹ : Egrp K) • u : (AdeleRing (𝓞 K) K)ˣ) = (iota K η)⁻¹ * u := by
      rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv, hη]
    rw [hg, inv_iota_mul_mem_coneI_iff K hu hη₀ η]
    constructor
    · intro hmem
      refine Finset.mem_image.mpr ⟨⟨η₀ * η, hmem⟩, Finset.mem_univ _, Subtype.ext ?_⟩
      show iota K (η₀⁻¹ * (η₀ * η)) = g
      rw [inv_mul_cancel_left, hη]
    · intro hmem
      obtain ⟨ζ, -, hζ⟩ := Finset.mem_image.mp hmem
      have h1 : iota K (η₀⁻¹ * ζ) = iota K η := (congrArg Subtype.val hζ).trans hη.symm
      have h2 : η₀⁻¹ * ζ = η := iota_injective K h1
      rw [← h2, mul_inv_cancel_left]
      exact ζ.2
  rw [tsum_eq_sum (s := S) (fun g hg => by rw [Set.indicator_of_notMem ((hS g).not.mpr hg)]),
    Finset.sum_congr rfl (fun g hg => by rw [Set.indicator_of_mem ((hS g).mpr hg)]),
    Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_image_of_injective _ hemb, Finset.card_univ,
    Units.torsionOrder, Nat.card_eq_fintype_card]

end Idelic

section Measures

variable (K : Type) [Field K] [NumberField K]

section Reference

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem exists_idelicHaar_U0_inter_preimage :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ s : Set (mixedSpace K), MeasurableSet s →
      NumberField.Idele.idelicHaar K (U0 K ∩ phi K ⁻¹' s) =
        C * ∫⁻ x in s, (ENNReal.ofReal (mixedEmbedding.norm x))⁻¹ := by
  obtain ⟨C, hC0, hCtop, hC⟩ :=
    NumberField.Idele.exists_map_ringEquiv_mixedSpace_sPartMeasure_empty_eq_smul_withDensity K
  refine ⟨C, hC0, hCtop, fun s hs => ?_⟩
  have hφ : Measurable fun a : (AdeleRing (𝓞 K) K)ˣ =>
      InfiniteAdeleRing.ringEquiv_mixedSpace K ((a : AdeleRing (𝓞 K) K)).1 :=
    (continuous_phi K).measurable
  have h := congrArg (fun m : Measure (mixedSpace K) => m s) hC
  beta_reduce at h
  rw [Measure.map_apply hφ hs, NumberField.Idele.sPartMeasure,
    Measure.map_apply (NumberField.Idele.measurable_partAt K ∅) (hs.preimage hφ),
    Measure.restrict_apply ((hs.preimage hφ).preimage (NumberField.Idele.measurable_partAt K ∅)),
    Finset.coe_empty, coe_Ugrp, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul] at h
  have hset : U0 K ∩ phi K ⁻¹' s =
      NumberField.Idele.partAt K ∅ ⁻¹'
        ((fun a : (AdeleRing (𝓞 K) K)ˣ => InfiniteAdeleRing.ringEquiv_mixedSpace K
          ((a : AdeleRing (𝓞 K) K)).1) ⁻¹' s) ∩ U0 K := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, phi_apply, NumberField.Idele.partAt_fst]
    exact and_comm
  rw [hset, h]
  congr 1
  refine setLIntegral_congr_fun hs fun x hx => ?_
  rw [norm_eq_prod_mul_prod]
  rfl

end Reference

variable [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]

theorem isOpen_U0 : IsOpen (U0 K) := by
  rw [← coe_Ugrp]
  exact NumberField.Idele.isOpen_unitIdelesOutside K _

theorem measurableSet_U0 : MeasurableSet (U0 K) := (isOpen_U0 K).measurableSet

theorem measurable_phi : Measurable (phi K) := (continuous_phi K).measurable

theorem measurableSet_band (a b : ℝ) : MeasurableSet (band K a b) :=
  (NumberField.TateGlobal.continuous_ideleNorm K).measurable measurableSet_Icc

theorem measurableSet_coneI : MeasurableSet (coneI K) :=
  (measurableSet_U0 K).inter ((measurableSet_fundamentalCone K).preimage (measurable_phi K))

theorem exists_eq_mul_idelicHaar (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ s : Set (AdeleRing (𝓞 K) K)ˣ, ν s = c * @NumberField.Idele.idelicHaar K _ _ s := by
  borelize (AdeleRing (𝓞 K) K)ˣ
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
    haveI := NumberField.AdeleRing.secondCountableTopology K
    haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
    exact Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := hν
  haveI := NumberField.Idele.isHaarMeasure_idelicHaar K
  have h := Measure.isMulLeftInvariant_eq_smul ν (NumberField.Idele.idelicHaar K)
  refine ⟨ν.haarScalarFactor (NumberField.Idele.idelicHaar K), ?_, ENNReal.coe_ne_top, fun s => ?_⟩
  · exact ENNReal.coe_ne_zero.mpr (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  · conv_lhs => rw [h]
    rfl

theorem exists_measure_U0_inter_preimage (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    ∃ W : ℝ≥0∞, W ≠ 0 ∧ W ≠ ⊤ ∧ ∀ s : Set (mixedSpace K), MeasurableSet s →
      ν (U0 K ∩ phi K ⁻¹' s) = W * ∫⁻ x in s, (ENNReal.ofReal (mixedEmbedding.norm x))⁻¹ := by
  obtain ⟨c, hc0, hctop, hc⟩ := exists_eq_mul_idelicHaar K ν hν
  obtain ⟨C, hC0, hCtop, hC⟩ := exists_idelicHaar_U0_inter_preimage K
  exact ⟨c * C, mul_ne_zero hc0 hC0, ENNReal.mul_ne_top hctop hCtop, fun s hs => by
    rw [hc, hC s hs, mul_assoc]⟩

theorem countable_field : Countable K := by
  let b := Module.finBasis ℚ K
  exact Function.Injective.countable b.equivFun.injective

scoped instance countable_E : Countable (Egrp K) := by
  haveI := countable_field K
  haveI : Countable Kˣ := Function.Injective.countable (Units.val_injective (α := K))
  have h : ((Kx K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact (h.mono fun x hx => hx.1).to_subtype

scoped instance measurableConstSMul_E : MeasurableConstSMul (Egrp K) (AdeleRing (𝓞 K) K)ˣ :=
  ⟨fun c => by
    show Measurable fun x : (AdeleRing (𝓞 K) K)ˣ => (c : (AdeleRing (𝓞 K) K)ˣ) * x
    exact measurable_const_mul _⟩

theorem smulInvariant_E_restrict (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsMulLeftInvariant] :
    SMulInvariantMeasure (Egrp K) (AdeleRing (𝓞 K) K)ˣ
      (ν.restrict ((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)) := by
  refine ⟨fun c s hs => ?_⟩
  have hU : MeasurableSet ((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) := by
    rw [coe_Ugrp]; exact measurableSet_U0 K
  have hpre : (fun x : (AdeleRing (𝓞 K) K)ˣ => c • x) ⁻¹' s =
      (fun x : (AdeleRing (𝓞 K) K)ˣ => (c : (AdeleRing (𝓞 K) K)ˣ) * x) ⁻¹' s := rfl
  have hUinv : (fun x : (AdeleRing (𝓞 K) K)ˣ => (c : (AdeleRing (𝓞 K) K)ˣ) * x) ⁻¹'
      ((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) =
      ((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_left _ c.2.2
  rw [hpre, Measure.restrict_apply (hs.preimage (measurable_const_mul _)),
    Measure.restrict_apply hs]
  conv_lhs => rw [← hUinv, ← Set.preimage_inter]
  exact measure_preimage_mul ν _ _

theorem ideleNorm_E (g : Egrp K) : NumberField.TateGlobal.ideleNorm K (g : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
  obtain ⟨_, ⟨a, rfl⟩, _⟩ := g
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
  have h : distribHaarChar (AdeleRing (𝓞 K) K)
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) = 1 :=
    NumberField.AdeleRing.distribHaarChar_algebraMap K a
  simp only [NumberField.TateGlobal.ideleNorm, h, NNReal.coe_one]

theorem E_smul_band (g : Egrp K) (a b : ℝ) : g • band K a b = band K a b := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
  simp only [band, Set.mem_setOf_eq, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_E, one_mul]

theorem measure_coneI_inter (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsMulLeftInvariant]
    (F : Set (AdeleRing (𝓞 K) K)ˣ)
    (hF : IsFundamentalDomain (Egrp K) F
      (ν.restrict ((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ)))
    {A : Set (AdeleRing (𝓞 K) K)ˣ} (hA : MeasurableSet A) (hAinv : ∀ g : Egrp K, g • A = A) :
    ν (coneI K ∩ A) =
      (Units.torsionOrder K : ℝ≥0∞) *
        ν (((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) ∩ F ∩ A) := by
  haveI := smulInvariant_E_restrict K ν
  set μ := ν.restrict ((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) with hμ
  have hU : MeasurableSet ((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) := by
    rw [coe_Ugrp]; exact measurableSet_U0 K
  have hC := measurableSet_coneI K

  have h1 : μ (coneI K ∩ A) = ∫⁻ x in A, (coneI K).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
    rw [lintegral_indicator hC, setLIntegral_const, one_mul, Measure.restrict_apply hC]

  have h2 := hF.setLIntegral_eq_tsum' ((coneI K).indicator fun _ => (1 : ℝ≥0∞)) A
  simp_rw [hAinv] at h2
  have hmeas : ∀ g : Egrp K, Measurable fun x : (AdeleRing (𝓞 K) K)ˣ =>
      (coneI K).indicator (fun _ => (1 : ℝ≥0∞)) ((g⁻¹ : Egrp K) • x) := fun g =>
    (measurable_const.indicator hC).comp (measurable_const_smul _)
  have h3 : ∑' g : Egrp K, ∫⁻ x in A ∩ F, (coneI K).indicator (fun _ => (1 : ℝ≥0∞))
      ((g⁻¹ : Egrp K) • x) ∂μ =
      ∫⁻ x in A ∩ F, ∑' g : Egrp K, (coneI K).indicator (fun _ => (1 : ℝ≥0∞))
        ((g⁻¹ : Egrp K) • x) ∂μ :=
    (lintegral_tsum fun g => (hmeas g).aemeasurable).symm
  have h4 : ∫⁻ x in A ∩ F, ∑' g : Egrp K, (coneI K).indicator (fun _ => (1 : ℝ≥0∞))
        ((g⁻¹ : Egrp K) • x) ∂μ = ∫⁻ x in A ∩ F, (Units.torsionOrder K : ℝ≥0∞) ∂μ := by
    refine lintegral_congr_ae ?_
    have hae : ∀ᵐ x ∂μ, x ∈ ((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) :=
      ae_restrict_mem hU
    filter_upwards [ae_restrict_of_ae hae] with x hx
    rw [coe_Ugrp] at hx
    exact tsum_indicator_coneI K hx
  have h5 : ∫⁻ x in A ∩ F, (Units.torsionOrder K : ℝ≥0∞) ∂μ =
      (Units.torsionOrder K : ℝ≥0∞) * μ (A ∩ F) := setLIntegral_const _ _
  have hCU : coneI K ∩ A ∩ ((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) =
      coneI K ∩ A := by
    rw [coe_Ugrp]
    exact Set.inter_eq_left.mpr fun x hx => hx.1.1
  have hL : ν (coneI K ∩ A) = μ (coneI K ∩ A) := by
    rw [hμ, Measure.restrict_apply' hU, hCU]
  have hR : μ (A ∩ F) =
      ν (((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) ∩ F ∩ A) := by
    rw [hμ, Measure.restrict_apply' hU]
    congr 1
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  rw [hL, h1, h2, h3, h4, h5, hR]

theorem constants_identity :
    ((Units.torsionOrder K : ℝ≥0∞))⁻¹ * volume (fundamentalCone.normLeOne K) =
      (2 ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K) *
        ENNReal.ofReal (Units.regulator K /
          (2 ^ nrComplexPlaces K * (Units.torsionOrder K : ℝ))) := by
  have hw : (0 : ℝ) < Units.torsionOrder K := by
    have : 0 < Units.torsionOrder K := Units.torsionOrder_pos K
    exact_mod_cast this
  have hR : 0 ≤ Units.regulator K := (Units.regulator_pos K).le
  rw [fundamentalCone.volume_normLeOne]
  have e2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := (ENNReal.ofReal_ofNat 2).symm
  have epi : ((NNReal.pi : NNReal) : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [ENNReal.ofReal_eq_coe_nnreal Real.pi_pos.le]
    rfl
  have ew : ((Units.torsionOrder K : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((Units.torsionOrder K : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hw, ENNReal.ofReal_natCast]
  rw [e2, epi, ew, ← ENNReal.ofReal_pow zero_le_two, ← ENNReal.ofReal_pow Real.pi_pos.le,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow]
  field_simp

end Measures

end NumberField.TateGlobal.UnitRegulatorVolume
p2m_reactivate "P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.NumberField P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.NumberField.TateGlobal.UnitRegulatorVolume"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.NumberField P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.NumberField P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div.NumberField.TateGlobal.UnitRegulatorVolume"

open NumberField.TateGlobal.UnitRegulatorVolume in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) (hν : ν.IsHaarMeasure) :
    ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} ≠ 0 ∧
    ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} ≠ ⊤ ∧
    ∀ F : Set (AdeleRing (𝓞 K) K)ˣ,
      IsFundamentalDomain
        ↥((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ⊓
          NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K)))) F
        (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))))) →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        ν ((NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (∅ : Set (HeightOneSpectrum (𝓞 K))) :
              Set (AdeleRing (𝓞 K) K)ˣ) ∩ F ∩
            {x | NumberField.TateGlobal.ideleNorm K x ∈ Set.Icc a b}) =
          ν {u | (∀ v : HeightOneSpectrum (𝓞 K),
            ((u : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
            (((u⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
              v.adicCompletionIntegers K) ∧
          ∀ w : InfinitePlace K, ‖(u : AdeleRing (𝓞 K) K).1 w‖ ∈ Set.Icc (1 : ℝ) (Real.exp 1)} *
            ENNReal.ofReal (NumberField.Units.regulator K /
              (2 ^ NumberField.InfinitePlace.nrComplexPlaces K * (NumberField.Units.torsionOrder K : ℝ))) *
            ENNReal.ofReal (Real.log (b / a)) := by
  haveI := hν

  obtain ⟨W, hW0, hWtop, hW⟩ := exists_measure_U0_inter_preimage K ν hν

  have hD0 : (2 : ℝ≥0∞) ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ two_ne_zero)
      (pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by positivity)).ne')
  have hDtop : (2 : ℝ≥0∞) ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hSh : ν (Sh K) = W * (2 ^ nrRealPlaces K * ENNReal.ofReal (2 * Real.pi) ^ nrComplexPlaces K) := by
    rw [Sh_eq, hW _ (measurableSet_shellV K), lintegral_shellV_inv_ofReal]
  refine ⟨?_, ?_, fun F hF a b ha hab => ?_⟩
  · show ν (Sh K) ≠ 0
    rw [hSh]
    exact mul_ne_zero hW0 hD0
  · show ν (Sh K) ≠ ⊤
    rw [hSh]
    exact ENNReal.mul_ne_top hWtop hDtop
  · show ν (((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) ∩ F ∩ band K a b) =
      ν (Sh K) * _ * _

    have hslab_meas : MeasurableSet (fundamentalCone K ∩ {x | mixedEmbedding.norm x ∈ Set.Icc a b}) :=
      (measurableSet_fundamentalCone K).inter
        (measurableSet_Icc.preimage (mixedEmbedding.continuous_norm K).measurable)
    have hcone : ν (coneI K ∩ band K a b) =
        W * (volume (fundamentalCone.normLeOne K) * ENNReal.ofReal (Real.log (b / a))) := by
      rw [coneI_inter_band, hW _ hslab_meas,
        ← fundamentalCone.setLIntegral_inv_norm_eq_volume_normLeOne_mul_log K a b ha hab]
      congr 1
      refine setLIntegral_congr_fun hslab_meas fun x hx => ?_
      rw [ENNReal.ofReal_inv_of_pos (lt_of_lt_of_le ha hx.2.1)]

    have hcount := measure_coneI_inter K ν F hF (measurableSet_band K a b) (fun g => E_smul_band K g a b)
    have hw0 : (Units.torsionOrder K : ℝ≥0∞) ≠ 0 := by
      have : 0 < Units.torsionOrder K := Units.torsionOrder_pos K
      exact_mod_cast this.ne'
    have hwtop : (Units.torsionOrder K : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hsolve : ν (((Ugrp K : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) ∩ F ∩ band K a b) =
        ((Units.torsionOrder K : ℝ≥0∞))⁻¹ * ν (coneI K ∩ band K a b) := by
      rw [hcount, ← mul_assoc, ENNReal.inv_mul_cancel hw0 hwtop, one_mul]
    rw [hsolve, hcone, hSh]
    calc ((Units.torsionOrder K : ℝ≥0∞))⁻¹ *
          (W * (volume (fundamentalCone.normLeOne K) * ENNReal.ofReal (Real.log (b / a))))
        = W * ((((Units.torsionOrder K : ℝ≥0∞))⁻¹ * volume (fundamentalCone.normLeOne K)) *
            ENNReal.ofReal (Real.log (b / a))) := by ring
      _ = _ := by rw [constants_identity K]; ring

end S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div
end P2MW
export P2MW.S_NumberField_TateGlobal_measure_unitIdeles_inter_fundamentalDomain_inter_ideleNorm_Icc_eq_measure_unitShell_mul_regulator_div (solution)
