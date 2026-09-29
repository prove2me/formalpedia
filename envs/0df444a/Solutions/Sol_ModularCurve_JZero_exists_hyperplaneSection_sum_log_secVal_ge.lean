-- Prove2me | solution 1 for ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/85c38980-f05f-5c49-b685-4810c8f1ba9d

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import Theorems.Thm_AlgebraicCurve_Place_evalAt_map_eq_of_comap_eq
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_AlgebraicCurve_Place_exists_place_laurentBaseChange_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Theorems.Thm_AlgebraicCurve_exists_D_ne_zero
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AnalyticOnNhd_integrableOn_log_norm_ball
import Theorems.Thm_AnalyticOnNhd_log_norm_sub_mul_le_setAverage_ball
import Theorems.Thm_Complex_exists_analyticOnNhd_comp_pow_of_forall_mul_eq
import Theorems.Thm_Complex_exists_grid_reProdIm
import Theorems.Thm_Complex_exists_lipschitzWith_divided_minor
import Theorems.Thm_Complex_exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero
import Theorems.Thm_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le
import Theorems.Thm_Complex_volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume
import Theorems.Thm_Complex_volume_ball_inter_norm_sum_mul_le
import Theorems.Thm_MeasureTheory_exists_mem_le_of_setAverage_chain
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_analyticAt_eventuallyEq_realize
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_pt_eq_of_mem
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_pt_eq_pt_iff
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer
import Theorems.Thm_ModularCurve_CuspSpace_conj_T_zpow_mem_Gamma0_iff
import Theorems.Thm_ModularCurve_CuspSpace_sum_cuspWidth_eq_dedekindPsi
import Theorems.Thm_ModularCurve_JZero_chordVec_ne_zero_of_ne
import Theorems.Thm_ModularCurve_JZero_sum_toNat_hyperplaneSection_eq_embDegree
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_algHom_slot_mul_qExpansion_slash_eq
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionary
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_exists_modularForm_realize_eventuallyEq_div
import Theorems.Thm_ModularCurve_exists_ord_add_embDivisor_eq_zero
import Theorems.Thm_ModularCurve_exists_slot_of_isCusp
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasSum_jq_qParam
import Theorems.Thm_ModularCurve_hasSum_qParam_mul_laurent
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_realize_eq_div
import Theorems.Thm_ModularCurve_sum_neg_ord_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularGroup_exists_finset_box_or_cusp
import Theorems.Thm_RingHom_exists_mem_forall_mem_range_of_isOpen
import Theorems.Thm_UpperHalfPlane_cayley_smul_eq_mul_cayley
import Theorems.Thm_UpperHalfPlane_periodic_comp_smul_of_conj_T_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 4000000

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit false

open UpperHalfPlane Filter AlgebraicCurve ModularCurve
open scoped Topology MatrixGroups ModularForm Pointwise

noncomputable section

namespace CUSPATLAS

section Generic
variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem eq_pow_smul_iterate_dslope {p : FormalMultilinearSeries ℂ ℂ ℂ} {f : ℂ → ℂ} {z₀ : ℂ}
    {n : ℕ} (hp : HasFPowerSeriesAt f p z₀) (hn : ∀ k < n, p.coeff k = 0) :
    ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • (Function.swap dslope z₀)^[n] f z := by
  have hq := hasFPowerSeriesAt_iff'.mp (hp.has_fpower_series_iterate_dslope_fslope n)
  filter_upwards [hq, hasFPowerSeriesAt_iff'.mp hp] with x hx1 hx2
  obtain ⟨s, hs1, hs2⟩ := HasSum.exists_hasSum_smul_of_apply_eq_zero hx2 hn
  convert hs1.symm
  simp only [FormalMultilinearSeries.coeff_iterate_fslope] at hx1
  exact hx1.unique hs2

theorem hasFPowerSeriesAt_cuspFunction_width (F : ModularForm Γ k) {w : ℝ} (hw : 0 < w)
    (hΓ : w ∈ Γ.strictPeriods) :
    HasFPowerSeriesAt (cuspFunction w (F : ℍ → ℂ)) (qExpansionFormalMultilinearSeries w F) 0 := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods hw hΓ⟩
  exact (UpperHalfPlane.hasFPowerSeries_cuspFunction F
    (c := fun m => PowerSeries.coeff m (qExpansion w (F : ℍ → ℂ))) hw
    (ModularFormClass.analyticAt_cuspFunction_zero F hw hΓ) fun τ =>
      UpperHalfPlane.hasSum_qExpansion hw (SlashInvariantFormClass.periodic_comp_ofComplex F hΓ)
        (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ).hasFPowerSeriesAt

theorem cuspFunction_factor_width (F : ModularForm Γ k) {w : ℝ} (hw : 0 < w)
    (hΓ : w ∈ Γ.strictPeriods) (n : ℕ)
    (hn : ∀ j < n, PowerSeries.coeff j (qExpansion w (F : ℍ → ℂ)) = 0) :
    HasFPowerSeriesAt ((Function.swap dslope (0 : ℂ))^[n] (cuspFunction w (F : ℍ → ℂ)))
        (FormalMultilinearSeries.fslope^[n] (qExpansionFormalMultilinearSeries w F)) 0 ∧
      (Function.swap dslope (0 : ℂ))^[n] (cuspFunction w (F : ℍ → ℂ)) 0 =
        PowerSeries.coeff n (qExpansion w (F : ℍ → ℂ)) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), cuspFunction w (F : ℍ → ℂ) z =
        (z - 0) ^ n • (Function.swap dslope (0 : ℂ))^[n] (cuspFunction w (F : ℍ → ℂ)) z := by
  have hP := hasFPowerSeriesAt_cuspFunction_width F hw hΓ
  have hD := hP.has_fpower_series_iterate_dslope_fslope n
  refine ⟨hD, ?_, eq_pow_smul_iterate_dslope hP fun j hj => by
    rw [UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff]; exact hn j hj⟩
  rw [← hD.coeff_zero 1]
  change (FormalMultilinearSeries.fslope^[n] (qExpansionFormalMultilinearSeries w F)).coeff 0 = _
  rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add,
    UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff]

theorem qExpansionFormalMultilinearSeries_ne_zero (F : ModularForm Γ k) {w : ℝ} (hw : 0 < w)
    (hΓ : w ∈ Γ.strictPeriods) (hF : F ≠ 0) : qExpansionFormalMultilinearSeries w F ≠ 0 := by
  intro h0
  apply hF
  have hP := hasFPowerSeriesAt_cuspFunction_width F hw hΓ
  rw [h0] at hP

  have hz : ∀ᶠ q in 𝓝 (0 : ℂ), cuspFunction w (F : ℍ → ℂ) q = 0 := by
    simpa using hP.eventually_eq_zero
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hz

  have hhigh : ∀ τ : ℍ, -w * Real.log ε / (2 * Real.pi) + 1 ≤ τ.im → (F : ℍ → ℂ) τ = 0 := by
    intro τ hτ
    rw [← SlashInvariantFormClass.eq_cuspFunction F τ hΓ hw.ne']
    apply hball
    rw [dist_zero_right, Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
    have hπ := Real.pi_pos
    calc Real.exp (-2 * Real.pi * τ.im / w)
        ≤ Real.exp (-2 * Real.pi * (-w * Real.log ε / (2 * Real.pi) + 1) / w) := by
          apply Real.exp_le_exp.mpr
          apply div_le_div_of_nonneg_right _ hw.le
          exact mul_le_mul_of_nonpos_left hτ (by linarith)
      _ = ε * Real.exp (-2 * Real.pi / w) := by
          rw [show -2 * Real.pi * (-w * Real.log ε / (2 * Real.pi) + 1) / w =
            Real.log ε + -2 * Real.pi / w by field_simp; ring, Real.exp_add, Real.exp_log hε]
      _ < ε := by
          rw [mul_lt_iff_lt_one_right hε]
          exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hw)

  set f : ℂ → ℂ := (F : ℍ → ℂ) ∘ ofComplex with hf
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hdiff : DifferentiableOn ℂ f {z : ℂ | 0 < z.im} := fun z hz =>
    (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo F ⟨z, hz⟩)).differentiableWithinAt
  have hana : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im} := hdiff.analyticOnNhd hU
  set A : ℝ := max (-w * Real.log ε / (2 * Real.pi) + 1) 1 with hA
  have hz₀ : (⟨(2 * A : ℝ) * Complex.I, by simp; positivity⟩ : ℍ).im = 2 * A := by
    show ((2 * A : ℝ) * Complex.I).im = 2 * A
    simp
  set z₀ : ℂ := ((2 * A : ℝ) : ℂ) * Complex.I with hz₀def
  have hz₀im : z₀.im = 2 * A := by simp [hz₀def]
  have hApos : 0 < A := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hz₀U : z₀ ∈ {z : ℂ | 0 < z.im} := by show 0 < z₀.im; rw [hz₀im]; positivity
  have hfz₀ : f =ᶠ[𝓝 z₀] 0 := by
    have hopen : IsOpen {z : ℂ | A < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds (show A < z₀.im by rw [hz₀im]; linarith)] with z hz
    have hzpos : 0 < z.im := hApos.trans hz
    simp only [hf, Function.comp_apply, Pi.zero_apply]
    rw [ofComplex_apply_of_im_pos hzpos]
    exact hhigh ⟨z, hzpos⟩ ((le_max_left _ _).trans hz.le)
  have hEq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_im_gt 0).isPreconnected hz₀U hfz₀
  apply DFunLike.ext
  intro τ'
  have := hEq τ'.im_pos
  simp only [hf, Function.comp_apply, ofComplex_apply, Pi.zero_apply] at this
  simpa using this

theorem exists_forall_ne_zero_of_le_im_width (F : ModularForm Γ k) {w : ℝ} (hw : 0 < w)
    (hΓ : w ∈ Γ.strictPeriods) (hF : F ≠ 0) :
    ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → (F : ℍ → ℂ) τ ≠ 0 := by
  have hP := hasFPowerSeriesAt_cuspFunction_width F hw hΓ
  have hloc := hP.locally_ne_zero (qExpansionFormalMultilinearSeries_ne_zero F hw hΓ hF)
  obtain ⟨ε, hε, hεne⟩ : ∃ ε > 0, ∀ q : ℂ, q ≠ 0 → ‖q‖ < ε → cuspFunction w (F : ℍ → ℂ) q ≠ 0 := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hloc
    obtain ⟨ε, hε, hh⟩ := hloc
    exact ⟨ε, hε, fun q hq0 hq => hh (by simpa using hq) hq0⟩
  refine ⟨-w * Real.log ε / (2 * Real.pi) + 1, fun τ hτ => ?_⟩
  rw [← SlashInvariantFormClass.eq_cuspFunction F τ hΓ hw.ne']
  refine hεne _ (by first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]) ?_
  rw [Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
  have hπ := Real.pi_pos
  calc Real.exp (-2 * Real.pi * τ.im / w)
      ≤ Real.exp (-2 * Real.pi * (-w * Real.log ε / (2 * Real.pi) + 1) / w) := by
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ hw.le
        exact mul_le_mul_of_nonpos_left hτ (by linarith)
    _ = ε * Real.exp (-2 * Real.pi / w) := by
        rw [show -2 * Real.pi * (-w * Real.log ε / (2 * Real.pi) + 1) / w =
          Real.log ε + -2 * Real.pi / w by field_simp; ring, Real.exp_add, Real.exp_log hε]
    _ < ε := by
        rw [mul_lt_iff_lt_one_right hε]
        exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hw)

theorem order_coe_eq {φ : PowerSeries ℂ} {n : ℕ} (hn : PowerSeries.coeff n φ ≠ 0)
    (hlt : ∀ i < n, PowerSeries.coeff i φ = 0) :
    (φ : LaurentSeries ℂ).order = n := by
  have key : ∀ j : ℤ, j < 0 → (φ : LaurentSeries ℂ).coeff j = 0 := fun j hj => by
    rw [HahnSeries.ofPowerSeries_apply]
    first
      | exact HahnSeries.embDomain_notin_range (by rintro ⟨m', hm'⟩; simp at hm'; omega)
      | exact HahnSeries.embDomain_notMem_range (by rintro ⟨m', hm'⟩; simp at hm'; omega)
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by rwa [HahnSeries.ofPowerSeries_apply_coeff])
  · have hφ : (φ : LaurentSeries ℂ) ≠ 0 := fun h0 => hn (by
      have := congrArg (fun y : LaurentSeries ℂ => y.coeff (n : ℤ)) h0
      simpa [HahnSeries.ofPowerSeries_apply_coeff] using this)
    have hc : (φ : LaurentSeries ℂ).coeff (φ : LaurentSeries ℂ).order ≠ 0 := by
      rw [← HahnSeries.leadingCoeff_eq]; exact HahnSeries.leadingCoeff_ne_zero.mpr hφ
    by_contra hle
    have hlt' : (φ : LaurentSeries ℂ).order < n := not_le.mp hle
    rcases le_or_gt 0 (φ : LaurentSeries ℂ).order with h0 | h0
    · obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le h0
      rw [hi, HahnSeries.ofPowerSeries_apply_coeff] at hc
      exact hc (hlt i (by omega))
    · exact hc (key _ h0)

theorem div_chart_width (G H : ModularForm Γ k) (hG : G ≠ 0) (hH : H ≠ 0) {w : ℝ} (hw : 0 < w)
    (hΓ : w ∈ Γ.strictPeriods) :
    (((qExpansion w (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
              ((qExpansion w (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) ≠ 0 ∧
    ∃ Φ : ℂ → ℂ, AnalyticAt ℂ Φ 0 ∧
      Φ 0 = (((qExpansion w (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
              ((qExpansion w (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)).coeff
            (((qExpansion w (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
              ((qExpansion w (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)).order ∧
      ∀ᶠ τ in atImInfty, (H : ℍ → ℂ) τ ≠ 0 ∧
        (G : ℍ → ℂ) τ / (H : ℍ → ℂ) τ =
          Function.Periodic.qParam w (τ : ℂ) ^
              (((qExpansion w (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
                ((qExpansion w (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)).order *
            Φ (Function.Periodic.qParam w (τ : ℂ)) := by

  set Gs : LaurentSeries ℂ := ((qExpansion w (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with hGs
  set Hs : LaurentSeries ℂ := ((qExpansion w (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with hHs
  set Q : LaurentSeries ℂ := Gs / Hs with hQ
  have hpG := qExpansionFormalMultilinearSeries_ne_zero G hw hΓ hG
  have hpH := qExpansionFormalMultilinearSeries_ne_zero H hw hΓ hH
  set n : ℕ := (qExpansionFormalMultilinearSeries w H).order with hn_def
  set m : ℕ := (qExpansionFormalMultilinearSeries w G).order with hm_def
  have hHlt : ∀ j < n, PowerSeries.coeff j (qExpansion w (H : ℍ → ℂ)) = 0 := fun j hj => by
    rw [← UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff, FormalMultilinearSeries.coeff_eq_zero]
    exact FormalMultilinearSeries.apply_eq_zero_of_lt_order hj
  have hGlt : ∀ j < m, PowerSeries.coeff j (qExpansion w (G : ℍ → ℂ)) = 0 := fun j hj => by
    rw [← UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff, FormalMultilinearSeries.coeff_eq_zero]
    exact FormalMultilinearSeries.apply_eq_zero_of_lt_order hj
  obtain ⟨hDh, hDh_val, hFh⟩ := cuspFunction_factor_width H hw hΓ n hHlt
  obtain ⟨hDg, hDg_val, hFg⟩ := cuspFunction_factor_width G hw hΓ m hGlt
  set Dh : ℂ → ℂ := (Function.swap dslope (0 : ℂ))^[n] (cuspFunction w (H : ℍ → ℂ)) with hDh_def
  set Dg : ℂ → ℂ := (Function.swap dslope (0 : ℂ))^[m] (cuspFunction w (G : ℍ → ℂ)) with hDg_def
  have hDh0 : Dh 0 ≠ 0 := (hasFPowerSeriesAt_cuspFunction_width H hw hΓ).iterate_dslope_fslope_ne_zero hpH
  have hDg0 : Dg 0 ≠ 0 := (hasFPowerSeriesAt_cuspFunction_width G hw hΓ).iterate_dslope_fslope_ne_zero hpG
  have hordH : Hs.order = n := order_coe_eq (by rw [← hDh_val]; exact hDh0) hHlt
  have hordG : Gs.order = m := order_coe_eq (by rw [← hDg_val]; exact hDg0) hGlt
  have hHs0 : Hs ≠ 0 := fun h0 => by
    have h1 : Hs.coeff (n : ℤ) ≠ 0 := by
      rw [hHs, HahnSeries.ofPowerSeries_apply_coeff, ← hDh_val]; exact hDh0
    rw [h0] at h1; simp at h1
  have hGs0 : Gs ≠ 0 := fun h0 => by
    have h1 : Gs.coeff (m : ℤ) ≠ 0 := by
      rw [hGs, HahnSeries.ofPowerSeries_apply_coeff, ← hDg_val]; exact hDg0
    rw [h0] at h1; simp at h1
  have hQH : Q * Hs = Gs := div_mul_cancel₀ Gs hHs0
  have hQ0 : Q ≠ 0 := div_ne_zero hGs0 hHs0
  have hord : Q.order = (m : ℤ) - n := by
    have := HahnSeries.order_mul hQ0 hHs0
    rw [hQH, hordG, hordH] at this
    omega
  have hlead : PowerSeries.coeff m (qExpansion w (G : ℍ → ℂ)) =
      Q.coeff Q.order * PowerSeries.coeff n (qExpansion w (H : ℍ → ℂ)) := by
    have := HahnSeries.leadingCoeff_mul Q Hs
    rw [hQH] at this
    simp only [HahnSeries.leadingCoeff_eq] at this
    rw [hordG, hordH, hGs, hHs, HahnSeries.ofPowerSeries_apply_coeff,
      HahnSeries.ofPowerSeries_apply_coeff] at this
    exact this
  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam w (τ : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty hw
  refine ⟨hQ0, fun z => Dg z / Dh z, hDg.analyticAt.div hDh.analyticAt hDh0, ?_, ?_⟩
  · show Dg 0 / Dh 0 = _
    rw [hDg_val, hlead, ← hDh_val, mul_div_cancel_right₀ _ hDh0]
  · have h3 : ∀ᶠ z in 𝓝 (0 : ℂ), Dh z ≠ 0 := hDh.continuousAt.eventually_ne hDh0
    filter_upwards [hq.eventually hFh, hq.eventually hFg, hq.eventually h3] with τ h1 h2 h3
    have hqne : Function.Periodic.qParam w (τ : ℂ) ≠ 0 := by
      first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]
    have hhτ : (H : ℍ → ℂ) τ =
        Function.Periodic.qParam w (τ : ℂ) ^ n * Dh (Function.Periodic.qParam w (τ : ℂ)) := by
      rw [← SlashInvariantFormClass.eq_cuspFunction H τ hΓ hw.ne', h1, sub_zero, smul_eq_mul]
    have hgτ : (G : ℍ → ℂ) τ =
        Function.Periodic.qParam w (τ : ℂ) ^ m * Dg (Function.Periodic.qParam w (τ : ℂ)) := by
      rw [← SlashInvariantFormClass.eq_cuspFunction G τ hΓ hw.ne', h2, sub_zero, smul_eq_mul]
    have hhne : (H : ℍ → ℂ) τ ≠ 0 := by
      rw [hhτ]; exact mul_ne_zero (pow_ne_zero _ hqne) h3
    refine ⟨hhne, ?_⟩
    rw [hgτ, hhτ, hord, zpow_natCast_sub_natCast₀ hqne, mul_div_mul_comm]

end Generic

abbrev FC (N : ℕ) : Type := ↥(laurentBaseChange ℂ (modularFunctionFieldFull N))

abbrev conjGamma0 (N : ℕ) (γ : SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • (CongruenceSubgroup.Gamma0 N).map
    (Matrix.SpecialLinearGroup.mapGL ℝ)

def slashQuot (N : ℕ) {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (γ : SL(2, ℤ))
    (w : ℝ) : LaurentSeries ℂ :=
  ((qExpansion w ((g : ℍ → ℂ) ∣[k] γ) : PowerSeries ℂ) : LaurentSeries ℂ) /
    ((qExpansion w ((h : ℍ → ℂ) ∣[k] γ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem coe_translate_SL (N : ℕ) {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (γ : SL(2, ℤ)) :
    ((ModularForm.translate f (γ : GL (Fin 2) ℝ) : ModularForm (conjGamma0 N γ) k) : ℍ → ℂ) =
      (f : ℍ → ℂ) ∣[k] γ := by
  rw [ModularForm.coe_translate, ModularForm.SL_slash]

theorem translate_ne_zero (N : ℕ) {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : f ≠ 0) (γ : SL(2, ℤ)) :
    (ModularForm.translate f (γ : GL (Fin 2) ℝ) : ModularForm (conjGamma0 N γ) k) ≠ 0 := by
  intro h0
  apply hf
  apply DFunLike.ext
  intro τ
  have h1 := congrArg (fun F : ModularForm (conjGamma0 N γ) k => (F : ℍ → ℂ) (γ⁻¹ • τ)) h0
  simp only [coe_translate_SL, ModularForm.SL_slash_apply, smul_inv_smul, ModularForm.zero_apply] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · simpa using h
  · exfalso
    exact (zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _)) h

theorem slash_chart (N : ℕ) [NeZero N] (x : FC N) (hx : x ≠ 0) {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh0 : h ≠ 0)
    (hxhg : (x : LaurentSeries ℂ) * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) :
    slashQuot N g h γ w ≠ 0 ∧
    ∃ Φ : ℂ → ℂ, AnalyticAt ℂ Φ 0 ∧
      Φ 0 = (slashQuot N g h γ w).coeff (slashQuot N g h γ w).order ∧
      ∀ᶠ τ in atImInfty, realize N (x : LaurentSeries ℂ) (γ • τ) =
        Function.Periodic.qParam w (τ : ℂ) ^ (slashQuot N g h γ w).order *
          Φ (Function.Periodic.qParam w (τ : ℂ)) := by
  have hΓ₁ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _

  have hH0 : ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := fun h0 =>
    hh0 ((ModularForm.qExpansion_eq_zero_iff one_pos hΓ₁ h).mp
      (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ) (by rwa [map_zero])))
  have hx' : (x : LaurentSeries ℂ) ≠ 0 := by rwa [Ne, ZeroMemClass.coe_eq_zero]
  have hg0 : g ≠ 0 := by
    intro hg
    apply hx'
    have hG0 : ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = 0 := by
      rw [(ModularForm.qExpansion_eq_zero_iff one_pos hΓ₁ g).mpr hg, map_zero]
    rw [hG0] at hxhg
    exact (mul_eq_zero.mp hxhg).resolve_right hH0

  set Fg : ModularForm (conjGamma0 N γ) k := ModularForm.translate g (γ : GL (Fin 2) ℝ) with hFg
  set Fh : ModularForm (conjGamma0 N γ) k := ModularForm.translate h (γ : GL (Fin 2) ℝ) with hFh
  have hFg0 : Fg ≠ 0 := translate_ne_zero N g hg0 γ
  have hFh0 : Fh ≠ 0 := translate_ne_zero N h hh0 γ
  have hcoeg : (Fg : ℍ → ℂ) = (g : ℍ → ℂ) ∣[k] γ := coe_translate_SL N g γ
  have hcoeh : (Fh : ℍ → ℂ) = (h : ℍ → ℂ) ∣[k] γ := coe_translate_SL N h γ
  have hQ : slashQuot N g h γ w =
      ((qExpansion w (Fg : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion w (Fh : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [slashQuot, hcoeg, hcoeh]
  obtain ⟨hQ0, Φ, hΦ, hΦ0, hev⟩ := div_chart_width Fg Fh hFg0 hFh0 hw hΓ
  rw [← hQ] at hQ0 hΦ0 hev
  refine ⟨hQ0, Φ, hΦ, hΦ0, ?_⟩
  · filter_upwards [hev] with τ ⟨hne, hdiv⟩
    rw [← hdiv]

    have hhγ : (h : ℍ → ℂ) (γ • τ) ≠ 0 := by
      intro h0
      apply hne
      rw [hcoeh, ModularForm.SL_slash_apply, h0, zero_mul]
    rw [ModularCurve.realize_eq_div N g h (x : LaurentSeries ℂ) hxhg (γ • τ) hhγ, hcoeg, hcoeh,
      ModularForm.SL_slash_apply, ModularForm.SL_slash_apply,
      mul_div_mul_right _ _ (zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _))]

end CUSPATLAS

end

namespace CUSPATLAS

section Width

theorem T_zpow_mem_Gamma (N : ℕ) : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem, ModularGroup.coe_T_zpow]
  simp

theorem conj_T_zpow_mem_Gamma0 (N : ℕ) (γ : SL(2, ℤ)) :
    γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  have h1 : γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma N :=
    (CongruenceSubgroup.Gamma_normal N).conj_mem _ (T_zpow_mem_Gamma N) γ
  rw [CongruenceSubgroup.Gamma0_mem]
  exact (CongruenceSubgroup.Gamma_mem.mp h1).2.2.1

theorem mapGL_T_zpow (N : ℕ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (N : ℤ)) : GL (Fin 2) ℝ) =
      Matrix.GeneralLinearGroup.upperRightHom (N : ℝ) := by
  have hT : ModularGroup.T ^ (N : ℤ) = ⟨!![1, (N : ℤ); 0, 1], by simp [Matrix.det_fin_two_of]⟩ :=
    Subtype.ext (ModularGroup.coe_T_zpow N)
  rw [hT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom_apply, Matrix.SpecialLinearGroup.mapGL,
      Matrix.SpecialLinearGroup.map_apply_coe]

theorem natCast_mem_strictPeriods_conjGamma0 (N : ℕ) (γ : SL(2, ℤ)) :
    (N : ℝ) ∈ (conjGamma0 N γ).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, ← mapGL_T_zpow]
  have hmem : (Matrix.SpecialLinearGroup.mapGL ℝ (γ * ModularGroup.T ^ (N : ℤ) * γ⁻¹) : GL (Fin 2) ℝ) ∈
      (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
    Subgroup.mem_map_of_mem _ (conj_T_zpow_mem_Gamma0 N γ)
  have h2 := Subgroup.smul_mem_pointwise_smul _ (ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹) _ hmem
  convert h2 using 1
  rw [ConjAct.toConjAct_smul, inv_inv, map_mul, map_mul, map_inv]

  show _ = ((γ : GL (Fin 2) ℝ))⁻¹ *
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ) * (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (N : ℤ))) *
      ((Matrix.SpecialLinearGroup.mapGL ℝ γ))⁻¹) * (γ : GL (Fin 2) ℝ)
  have hc : (γ : GL (Fin 2) ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := rfl
  rw [hc]
  group

theorem natCast_pos_of_neZero (N : ℕ) [NeZero N] : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

end Width

section SlotAlgebra
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isRational_and_evalAt_eq_coeff_zero_of_slot (v : Place K F) (ι : F →ₐ[K] LaurentSeries K)
    (hO : ∀ y : F, y ≠ 0 → (y ∈ v.toValuationSubring ↔ 0 ≤ (ι y).order))
    (hM : ∀ y : F, y ≠ 0 → y ∈ v.toValuationSubring → (0 < v.ord y ↔ 0 < (ι y).order)) :
    v.IsRational ∧ ∀ x : F, x ∈ v.toValuationSubring → v.evalAt x = (ι x).coeff 0 := by
  have hkey : ∀ (y : F) (hy : y ∈ v.toValuationSubring),
      (⟨y, hy⟩ : v.toValuationSubring) - algebraMap K v.toValuationSubring ((ι y).coeff 0) ∈
        IsLocalRing.maximalIdeal v.toValuationSubring := by
    intro y hy
    set c : K := (ι y).coeff 0 with hc
    set z : F := y - algebraMap K F c with hz
    have hzmem : z ∈ v.toValuationSubring := sub_mem hy (v.algebraMap_mem' c)
    have hcoe : ((⟨y, hy⟩ : v.toValuationSubring) - algebraMap K v.toValuationSubring c :
        v.toValuationSubring) = ⟨z, hzmem⟩ := by
      apply Subtype.ext
      show y - ((algebraMap K v.toValuationSubring c : v.toValuationSubring) : F) = z
      rw [Place.coe_algebraMap]
    rw [hcoe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    by_cases hz0 : z = 0
    · intro hu
      apply hu.ne_zero
      exact Subtype.ext hz0
    · have hιz : ι z = ι y - HahnSeries.single 0 c := by
        rw [hz, map_sub, AlgHom.commutes, algebraMap_laurentSeries_eq_single]
      have hz0' : (ι z).coeff 0 = 0 := by
        simp [hιz, hc]
      have hzord : 0 ≤ (ι z).order := (hO z hz0).mp hzmem
      have hzpos : 0 < (ι z).order := by
        rcases hzord.eq_or_lt with h | h
        · exfalso
          have hι0 : ι z ≠ 0 := fun h0 => hz0 ((map_eq_zero_iff ι ι.toRingHom.injective).mp h0)
          have h2 := HahnSeries.leadingCoeff_ne_zero.mpr hι0
          rw [HahnSeries.leadingCoeff_eq, ← h, hz0'] at h2
          exact h2 rfl
        · exact h
      have hvord : 0 < v.ord z := (hM z hz0 hzmem).mpr hzpos
      intro hu
      obtain ⟨u, hu'⟩ := hu
      have h3 := v.ord_coe_unit u
      have h4 : ((u : v.toValuationSubring) : F) = z := congrArg Subtype.val hu'
      rw [h4] at h3
      omega
  have hrat : v.IsRational := by
    intro r
    obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨(ι y).coeff 0, ?_⟩
    rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField]
    show IsLocalRing.residue v.toValuationSubring _ = IsLocalRing.residue v.toValuationSubring _
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hkey y hy
  refine ⟨hrat, fun x hx => ?_⟩
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hrat hx,
    IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField]
  show IsLocalRing.residue v.toValuationSubring _ = IsLocalRing.residue v.toValuationSubring _
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hkey x hx

theorem slot_detects (v : Place K F) (ι : F →ₐ[K] LaurentSeries K) (e : ℕ) (he : 0 < e)
    (hord : ∀ x : F, v.ord x * (e : ℤ) = (ι x).order) :
    (∀ y : F, y ≠ 0 → (y ∈ v.toValuationSubring ↔ 0 ≤ (ι y).order)) ∧
    (∀ y : F, y ≠ 0 → y ∈ v.toValuationSubring → (0 < v.ord y ↔ 0 < (ι y).order)) := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  refine ⟨fun y hy => ?_, fun y hy _ => ?_⟩
  · rw [AlgebraicCurve.Place.mem_iff_ord_nonneg _ hy, ← hord y]
    constructor
    · intro h; positivity
    · intro h; nlinarith
  · rw [← hord y]
    constructor
    · intro h; positivity
    · intro h; nlinarith

end SlotAlgebra

theorem tendsto_realize_smul_of_slot (N : ℕ) [NeZero N] (x : FC N) (hx : x ≠ 0)
    (ι : FC N →ₐ[ℂ] LaurentSeries ℂ) (σ : SL(2, ℤ))
    (hι : ∀ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (x : LaurentSeries ℂ) * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) →
      ι x * ((qExpansion N ((h : ℍ → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion N ((g : ℍ → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (hreg : 0 ≤ (ι x).order) :
    Tendsto (fun τ : ℍ => realize N (x : LaurentSeries ℂ) (σ • τ)) atImInfty
      (𝓝 ((ι x).coeff 0)) := by
  obtain ⟨k, g, h, hh0, hxhg⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N (x : LaurentSeries ℂ) x.2
  have hw : (0 : ℝ) < N := natCast_pos_of_neZero N
  obtain ⟨hQ0, Φ, hΦ, hΦ0, hev⟩ :=
    slash_chart N x hx g h hh0 hxhg σ hw (natCast_mem_strictPeriods_conjGamma0 N σ)

  have hιx : ι x = slashQuot N g h σ N := by
    have h1 := hι k g h hxhg
    have hH : ((qExpansion N ((h : ℍ → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
      intro h0
      apply hQ0
      rw [slashQuot, h0, div_zero]
    rw [slashQuot, eq_div_iff hH]
    exact_mod_cast h1
  rw [← hιx] at hΦ0 hev
  have hq : Tendsto (fun τ : ℍ => Function.Periodic.qParam N (τ : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty hw
  have hΦc : Tendsto (fun τ : ℍ => Φ (Function.Periodic.qParam N (τ : ℂ))) atImInfty (𝓝 (Φ 0)) :=
    hΦ.continuousAt.tendsto.comp hq
  rcases hreg.eq_or_lt with h0 | hpos
  ·
    have ht : (ι x).coeff 0 = Φ 0 := by rw [hΦ0, ← h0]
    have hlim : Tendsto (fun τ : ℍ => Function.Periodic.qParam N (τ : ℂ) ^ (ι x).order *
        Φ (Function.Periodic.qParam N (τ : ℂ))) atImInfty (𝓝 ((ι x).coeff 0)) := by
      rw [ht, ← h0]
      simpa using hΦc
    exact hlim.congr' (by filter_upwards [hev] with τ hτ; exact hτ.symm)
  ·
    have hc0 : (ι x).coeff 0 = 0 := HahnSeries.coeff_eq_zero_of_lt_order hpos
    obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le hreg
    have hepos : 0 < e := by
      have : (0 : ℤ) < e := by rw [← he]; exact hpos
      exact_mod_cast this
    have hlim : Tendsto (fun τ : ℍ => Function.Periodic.qParam N (τ : ℂ) ^ (ι x).order *
        Φ (Function.Periodic.qParam N (τ : ℂ))) atImInfty (𝓝 ((ι x).coeff 0)) := by
      rw [hc0, he]
      have h2 : Tendsto (fun τ : ℍ => Function.Periodic.qParam N (τ : ℂ) ^ e) atImInfty (𝓝 0) := by
        simpa [zero_pow hepos.ne'] using hq.pow e
      simpa [zpow_natCast] using h2.mul hΦc
    exact hlim.congr' (by filter_upwards [hev] with τ hτ; exact hτ.symm)

theorem cusp_value_bridge (N : ℕ) [NeZero N]
    (v : Place ℂ (FC N))
    (hc : IsCusp (⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_full N)⟩ : FC N) v) :
    ∃ (ι : FC N →ₐ[ℂ] LaurentSeries ℂ) (σ : SL(2, ℤ)),
      v.IsRational ∧
      (∀ x : FC N, x ∈ v.toValuationSubring → v.evalAt x = (ι x).coeff 0) ∧
      (∀ x : FC N, x ≠ 0 → (x ∈ v.toValuationSubring ↔ 0 ≤ (ι x).order)) ∧
      ∀ x : FC N, x ≠ 0 → x ∈ v.toValuationSubring →
        Tendsto (fun τ : ℍ => realize N (x : LaurentSeries ℂ) (σ • τ)) atImInfty (𝓝 (v.evalAt x)) := by

  set ζc : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hζc
  have hζprim : IsPrimitiveRoot ζc N := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hζ0 : ζc ≠ 0 := hζprim.ne_zero (NeZero.ne N)
  set ζ : ℂˣ := Units.mk0 ζc hζ0 with hζ
  obtain ⟨a, b, ha, hb, hab, hna, ι, hι₁, hι₂, hord⟩ :=
    ModularCurve.exists_slot_of_isCusp ℂ N ζ (by simpa [hζ] using hζprim) v hc
  haveI : NeZero a := hna
  obtain ⟨σ, hσ⟩ := ModularCurve.exists_algHom_slot_mul_qExpansion_slash_eq N ζ (by simp [hζ, hζc])
    a b ha hab ι hι₁ hι₂
  have he : 0 < a * Nat.gcd a (N / a) := by
    have ha0 : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
    exact Nat.mul_pos ha0 (Nat.gcd_pos_of_pos_left _ ha0)
  obtain ⟨hO, hM⟩ := slot_detects v ι _ he hord
  obtain ⟨hrat, hval⟩ := isRational_and_evalAt_eq_coeff_zero_of_slot v ι hO hM
  refine ⟨ι, σ, hrat, hval, hO, fun x hx0 hx => ?_⟩
  rw [hval x hx]
  exact tendsto_realize_smul_of_slot N x hx0 ι σ (fun k g h hp => hσ x k g h hp) ((hO x hx0).mp hx)

section CuspInfinity

noncomputable def phi (N : ℕ) (σ : AlgebraicClosure ℚ →+* ℂ) : ↥(modularFunctionFieldBar N) →+* FC N where
  toFun y := ⟨coeffMap σ (y : LaurentSeries (AlgebraicClosure ℚ)),
    coeffMap_mem_laurentBaseChange_of_ringHom σ (modularFunctionFieldFull N) y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

variable {N : ℕ} [NeZero N]

theorem realize_zero' (τ : ℍ) : realize N (0 : LaurentSeries ℂ) τ = 0 := by
  have h := ModularCurve.realize_eq_div N (0 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) 1 0
    (by simp [UpperHalfPlane.qExpansion_zero]) τ (by simp)
  simpa using h

end CuspInfinity

section Exports

variable {N : ℕ} [NeZero N]

theorem phi_ne_zero (σ : AlgebraicClosure ℚ →+* ℂ) {y : ↥(modularFunctionFieldBar N)} (hy : y ≠ 0) :
    phi N σ y ≠ 0 :=
  (map_ne_zero_iff _ (phi N σ).injective).mpr hy

theorem phi_algebraMap (σ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    phi N σ (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c) = algebraMap ℂ (FC N) (σ c) := by
  apply Subtype.ext
  show coeffMap σ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) =
    algebraMap ℂ (LaurentSeries ℂ) (σ c)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

noncomputable def jB (N : ℕ) [NeZero N] : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

noncomputable def jC (N : ℕ) [NeZero N] : FC N :=
  ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_full N)⟩

theorem phi_jB (σ : AlgebraicClosure ℚ →+* ℂ) : phi N σ (jB N) = jC N := by
  apply Subtype.ext
  show coeffMap σ (coeffEmb (AlgebraicClosure ℚ) jq) = coeffEmb ℂ jq
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) jq

theorem isRational_FB (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) : v.IsRational :=
  (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).mpr (ModularCurve.deg_eq_one_modularFunctionFieldBar N v)

theorem placePoint (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hj : jB N ∈ v.toValuationSubring) :
    ∃ τ : ℍ, (∀ y, (D.pt τ).ord (phi N σ y) = v.ord y) ∧
      v.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) := by
  obtain ⟨w₀, hw₀ord, -⟩ := AlgebraicCurve.Place.exists_place_laurentBaseChange_of_deg_eq_one.{0, 0, 0} σ
    (modularFunctionFieldFull N) v (ModularCurve.deg_eq_one_modularFunctionFieldBar N v)
  have hordφ : ∀ y : ↥(modularFunctionFieldBar N), w₀.ord (phi N σ y) = v.ord y :=
    fun y => hw₀ord y (phi N σ y) rfl
  have hcomap : v.toValuationSubring = w₀.toValuationSubring.comap (phi N σ) := by
    ext y
    rw [ValuationSubring.mem_comap]
    by_cases hy : y = 0
    · subst hy
      simp only [map_zero]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    · rw [AlgebraicCurve.Place.mem_iff_ord_nonneg _ hy,
        AlgebraicCurve.Place.mem_iff_ord_nonneg _ (phi_ne_zero σ hy), hordφ]
  have hjC : jC N ∈ w₀.toValuationSubring := by
    have h := hj
    rw [hcomap, ValuationSubring.mem_comap, phi_jB] at h
    exact h
  obtain ⟨τ, hτ⟩ := D.exists_pt_eq_of_mem w₀ hjC
  refine ⟨τ, ?_, ?_⟩
  · rw [hτ]; exact hordφ
  · rw [hτ]; exact hcomap

theorem evalAt_transport (σ : AlgebraicClosure ℚ →+* ℂ)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) (w : Place ℂ (FC N))
    (h : v.toValuationSubring = w.toValuationSubring.comap (phi N σ))
    {y : ↥(modularFunctionFieldBar N)} (hy : y ∈ v.toValuationSubring) :
    σ (v.evalAt y) = w.evalAt (phi N σ y) :=
  (AlgebraicCurve.Place.evalAt_map_eq_of_comap_eq σ (phi N σ) (phi_algebraMap σ) v w h.symm
    (isRational_FB v) hy).symm

end Exports

section LinIndep

variable {N : ℕ} [NeZero N]

theorem phi_coeffEmb (σ : AlgebraicClosure ℚ →+* ℂ) (y : LaurentSeries ℚ)
    (hy : y ∈ modularFunctionFieldFull N) :
    phi N σ ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩ =
      ⟨coeffEmb ℂ y, coeffEmb_mem_laurentBaseChange ℂ hy⟩ := by
  apply Subtype.ext
  show coeffMap σ (coeffEmb (AlgebraicClosure ℚ) y) = coeffEmb ℂ y
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) y

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem linearIndependent_phi {ι : Type*} (σ : AlgebraicClosure ℚ →+* ℂ)
    {s : ι → ↥(modularFunctionFieldBar N)} (hs : LinearIndependent (AlgebraicClosure ℚ) s) :
    LinearIndependent ℂ (fun i => phi N σ (s i)) := by
  letI : Algebra (AlgebraicClosure ℚ) ℂ := σ.toAlgebra
  letI : Algebra ↥(modularFunctionFieldBar N) (FC N) := (phi N σ).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (FC N) := ((algebraMap ℂ (FC N)).comp σ).toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ (FC N) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (FC N) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      show ((algebraMap ℂ (FC N)).comp σ) c = phi N σ (algebraMap (AlgebraicClosure ℚ) _ c)
      rw [phi_algebraMap]; rfl
  have hrange : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionFieldFull N),
      (⟨coeffEmb ℂ y, coeffEmb_mem_laurentBaseChange ℂ hy⟩ : FC N) ∈
        Set.range (algebraMap ↥(modularFunctionFieldBar N) (FC N)) := fun y hy =>
    ⟨⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩,
      phi_coeffEmb σ y hy⟩
  have hgen : IntermediateField.adjoin ℂ (Set.range (algebraMap ↥(modularFunctionFieldBar N) (FC N))) = ⊤ := by
    apply top_le_iff.mp
    rw [← ModularCurve.adjoin_jBar_jNBar_eq_top ℂ N]
    apply IntermediateField.adjoin.mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h <;> rw [h]
    · exact hrange jq (jq_mem_full N)
    · exact hrange (qExpand ℚ N jq) (jqd_mem_full N (dvd_refl N))
  have key := AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed
    (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) ℂ (FC N)
    (ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar N)
    ⟨_, ModularCurve.transcendental_coeffEmb_jq ℂ N, ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full ℂ N⟩
    hgen hs
  exact key

theorem linComb_phi_ne_zero' {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ)
    {s : Fin r → ↥(modularFunctionFieldBar N)} (hs : LinearIndependent (AlgebraicClosure ℚ) s)
    (a : Fin r → ℂ) (ha : a ≠ 0) :
    (∑ i, a i • phi N σ (s i) : FC N) ≠ 0 := by
  intro h0
  exact ha (funext fun i => Fintype.linearIndependent_iff.mp (linearIndependent_phi σ hs) a h0 i)

end LinIndep

section ZeroCount

variable {N : ℕ} [NeZero N]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_unique_place_over (σ : AlgebraicClosure ℚ →+* ℂ)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :
    ∃ w : Place ℂ (FC N),
      w.toValuationSubring.comap (phi N σ) = v.toValuationSubring ∧
      (∀ y, w.ord (phi N σ y) = v.ord y) ∧
      ∀ w' : Place ℂ (FC N), w'.toValuationSubring.comap (phi N σ) = v.toValuationSubring → w' = w := by
  letI : Algebra (AlgebraicClosure ℚ) ℂ := σ.toAlgebra
  letI : Algebra ↥(modularFunctionFieldBar N) (FC N) := (phi N σ).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (FC N) := ((algebraMap ℂ (FC N)).comp σ).toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ (FC N) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (FC N) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      show ((algebraMap ℂ (FC N)).comp σ) c = phi N σ (algebraMap (AlgebraicClosure ℚ) _ c)
      rw [phi_algebraMap]; rfl
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  have hrange : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionFieldFull N),
      (⟨coeffEmb ℂ y, coeffEmb_mem_laurentBaseChange ℂ hy⟩ : FC N) ∈
        Set.range (algebraMap ↥(modularFunctionFieldBar N) (FC N)) := fun y hy =>
    ⟨⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩,
      phi_coeffEmb σ y hy⟩
  have hgen : IntermediateField.adjoin ℂ (Set.range (algebraMap ↥(modularFunctionFieldBar N) (FC N))) = ⊤ := by
    apply top_le_iff.mp
    rw [← ModularCurve.adjoin_jBar_jNBar_eq_top ℂ N]
    apply IntermediateField.adjoin.mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h <;> rw [h]
    · exact hrange jq (jq_mem_full N)
    · exact hrange (qExpand ℚ N jq) (jqd_mem_full N (dvd_refl N))
  have key := AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed
    (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) ℂ (FC N)
    (ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar N)
    ⟨_, ModularCurve.transcendental_coeffEmb_jq ℂ N, ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full ℂ N⟩
    hgen v
  exact key

theorem ord_eq_of_comap_eq (σ : AlgebraicClosure ℚ →+* ℂ)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) (w : Place ℂ (FC N))
    (h : v.toValuationSubring = w.toValuationSubring.comap (phi N σ)) (y : ↥(modularFunctionFieldBar N)) :
    w.ord (phi N σ y) = v.ord y := by
  obtain ⟨w₀, -, hord, huniq⟩ := exists_unique_place_over σ v
  rw [huniq w h.symm]
  exact hord y

theorem pt_eq_pt_of_comap_eq (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) {τ τ' : ℍ}
    (h : v.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ))
    (h' : v.toValuationSubring = (D.pt τ').toValuationSubring.comap (phi N σ)) :
    D.pt τ = D.pt τ' := by
  obtain ⟨w₀, -, -, huniq⟩ := exists_unique_place_over σ v
  rw [huniq _ h.symm, huniq _ h'.symm]

theorem ord_pt_eq_zero_of_forall_mem (σ : AlgebraicClosure ℚ →+* ℂ) (w : Place ℂ (FC N))
    (h : ∀ y : ↥(modularFunctionFieldBar N), phi N σ y ∈ w.toValuationSubring)
    (y : ↥(modularFunctionFieldBar N)) (hy : y ≠ 0) : w.ord (phi N σ y) = 0 := by
  have h1 := (AlgebraicCurve.Place.mem_iff_ord_nonneg _ (phi_ne_zero σ hy)).mp (h y)
  have h2 := (AlgebraicCurve.Place.mem_iff_ord_nonneg _ (phi_ne_zero σ (inv_ne_zero hy))).mp (h y⁻¹)
  rw [map_inv₀, Place.ord_inv] at h2
  omega

set_option synthInstance.maxHeartbeats 800000 in

theorem forall_mem_or_exists_comap (σ : AlgebraicClosure ℚ →+* ℂ) (w : Place ℂ (FC N)) :
    (∀ y : ↥(modularFunctionFieldBar N), phi N σ y ∈ w.toValuationSubring) ∨
    ∃ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      v.toValuationSubring = w.toValuationSubring.comap (phi N σ) := by
  by_cases hall : ∀ y : ↥(modularFunctionFieldBar N), phi N σ y ∈ w.toValuationSubring
  · exact Or.inl hall
  · right
    push_neg at hall
    haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jB N} : Set ↥(modularFunctionFieldBar N))) ↥(modularFunctionFieldBar N) :=
      ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N
    haveI : Algebra.IsSeparable
        (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jB N} : Set ↥(modularFunctionFieldBar N)))
        ↥(modularFunctionFieldBar N) := by
      first
        | infer_instance
        | exact Algebra.IsSeparable.of_finite _ _
    exact AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable (jB N) (phi N σ)
      w.toValuationSubring (fun a => by rw [phi_algebraMap]; exact w.algebraMap_mem' _) hall

end ZeroCount

section SigmaFinite

variable {N : ℕ} [NeZero N]

theorem exists_finiteDimensional_coeffMap_eq (x : LaurentSeries (AlgebraicClosure ℚ))
    (hx : x ∈ modularFunctionFieldBar N) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧
      ∀ σ σ' : AlgebraicClosure ℚ →+* ℂ, (∀ c ∈ K, σ c = σ' c) → coeffMap σ x = coeffMap σ' x := by
  rw [show modularFunctionFieldBar N = laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)
    from rfl, mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
    · refine ⟨IntermediateField.adjoin ℚ {a}, ?_, fun σ σ' h => ?_⟩
      · haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
        exact IntermediateField.adjoin.finiteDimensional
          (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) a).isIntegral
      · rw [algebraMap_laurentSeries_eq_single, coeffMap_single, coeffMap_single,
          h a (IntermediateField.mem_adjoin_simple_self ℚ a)]
    · refine ⟨⊥, inferInstance, fun σ σ' _ => ?_⟩
      rw [coeffEmb, coeffMap_coeffMap, coeffMap_coeffMap]
      exact (coeffMap_congr (Subsingleton.elim _ _) z)
  | one => exact ⟨⊥, inferInstance, fun σ σ' _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨K₁, hK₁, h₁⟩ := hx
    obtain ⟨K₂, hK₂, h₂⟩ := hy
    haveI := hK₁; haveI := hK₂
    refine ⟨K₁ ⊔ K₂, IntermediateField.finiteDimensional_sup K₁ K₂, fun σ σ' h => ?_⟩
    rw [map_add, map_add, h₁ σ σ' fun c hc => h c ((le_sup_left : K₁ ≤ K₁ ⊔ K₂) hc),
      h₂ σ σ' fun c hc => h c ((le_sup_right : K₂ ≤ K₁ ⊔ K₂) hc)]
  | neg x _ hx =>
    obtain ⟨K, hK, h⟩ := hx
    exact ⟨K, hK, fun σ σ' hσ => by rw [map_neg, map_neg, h σ σ' hσ]⟩
  | inv x _ hx =>
    obtain ⟨K, hK, h⟩ := hx
    exact ⟨K, hK, fun σ σ' hσ => by rw [map_inv₀, map_inv₀, h σ σ' hσ]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨K₁, hK₁, h₁⟩ := hx
    obtain ⟨K₂, hK₂, h₂⟩ := hy
    haveI := hK₁; haveI := hK₂
    refine ⟨K₁ ⊔ K₂, IntermediateField.finiteDimensional_sup K₁ K₂, fun σ σ' h => ?_⟩
    rw [map_mul, map_mul, h₁ σ σ' fun c hc => h c ((le_sup_left : K₁ ≤ K₁ ⊔ K₂) hc),
      h₂ σ σ' fun c hc => h c ((le_sup_right : K₂ ≤ K₁ ⊔ K₂) hc)]

theorem exists_finiteDimensional_phi_eq {r : ℕ} (s : Fin r → ↥(modularFunctionFieldBar N)) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧
      ∀ σ σ' : AlgebraicClosure ℚ →+* ℂ, (∀ c ∈ K, σ c = σ' c) → ∀ i, phi N σ (s i) = phi N σ' (s i) := by
  classical
  have h := fun i => exists_finiteDimensional_coeffMap_eq (N := N) ((s i : ↥(modularFunctionFieldBar N)) :
    LaurentSeries (AlgebraicClosure ℚ)) (s i).2
  choose K hK hKeq using h
  haveI := hK
  refine ⟨⨆ i, K i, ?_, fun σ σ' hσ i => ?_⟩
  · exact IntermediateField.finiteDimensional_iSup_of_finite
  · apply Subtype.ext
    exact hKeq i σ σ' fun c hc => hσ c ((le_iSup K i : K i ≤ ⨆ j, K j) hc)

theorem finite_range_phi_comp {r : ℕ} (s : Fin r → ↥(modularFunctionFieldBar N)) :
    (Set.range fun σ : AlgebraicClosure ℚ →+* ℂ => fun i => phi N σ (s i)).Finite := by
  classical
  obtain ⟨K, hK, hKeq⟩ := exists_finiteDimensional_phi_eq s
  haveI := hK

  let res : (AlgebraicClosure ℚ →+* ℂ) → (K →ₐ[ℚ] ℂ) := fun σ =>
    (σ.comp (algebraMap K (AlgebraicClosure ℚ))).toRatAlgHom
  have hres : ∀ σ σ', res σ = res σ' → (fun i => phi N σ (s i)) = fun i => phi N σ' (s i) := by
    intro σ σ' h
    funext i
    apply hKeq σ σ' (fun c hc => ?_) i
    have := congrArg (fun ψ : K →ₐ[ℚ] ℂ => ψ ⟨c, hc⟩) h
    simpa [res] using this
  haveI : Finite (K →ₐ[ℚ] ℂ) := inferInstance

  let g : (K →ₐ[ℚ] ℂ) → (Fin r → FC N) := fun ψ =>
    if h : ∃ σ : AlgebraicClosure ℚ →+* ℂ, res σ = ψ then (fun i => phi N h.choose (s i)) else fun _ => 0
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨res σ, ?_⟩
  have hex : ∃ σ₀ : AlgebraicClosure ℚ →+* ℂ, res σ₀ = res σ := ⟨σ, rfl⟩
  simp only [g, dif_pos hex]
  exact hres _ _ hex.choose_spec

end SigmaFinite

section SectionZeros

variable {N : ℕ} [NeZero N]

theorem place_under_unique (σ : AlgebraicClosure ℚ →+* ℂ) (w : Place ℂ (FC N))
    {v v' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}
    (hv : v.toValuationSubring = w.toValuationSubring.comap (phi N σ))
    (hv' : v'.toValuationSubring = w.toValuationSubring.comap (phi N σ)) : v = v' :=
  Place.ext (hv.trans hv'.symm)

end SectionZeros

section Immersion

variable {N : ℕ} [NeZero N]

end Immersion

section ComplexRR

variable {N : ℕ} [NeZero N]

theorem ell_eq_degree_add_one_sub_genusFF_FC (N : ℕ) [NeZero N] (D : Divisor ℂ (FC N))
    (hD : 2 * (genusFF ℂ (FC N) : ℤ) - 1 ≤ D.degree) :
    (ell D : ℤ) = D.degree + 1 - (genusFF ℂ (FC N) : ℤ) := by
  have key := ModularCurve.ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC ℂ N
  rw [← ModularCurve.laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC ℂ N] at key
  exact key D hD

theorem deg_eq_one_FC (w : Place ℂ (FC N)) : w.deg = 1 := by
  haveI : IsCurveOver ℂ (FC N) := ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull ℂ N
  exact IsCurveOver.deg_eq_one_of_isAlgClosed w

set_option maxHeartbeats 6400000 in

theorem exists_mem_lSpace_ord_add_eq_one_FC (E' : Divisor ℂ (FC N))
    (hE : E'.degree = 2 * (genusFF ℂ (FC N) : ℤ) + 1) (w : Place ℂ (FC N)) :
    ∃ f : FC N, f ≠ 0 ∧ f ∈ LSpace E' ∧ w.ord f + E' w = 1 := by
  classical
  set g : ℕ := genusFF ℂ (FC N) with hg
  have hdeg1 : ∀ v : Place ℂ (FC N), (v.deg : ℤ) = 1 := fun v => by exact_mod_cast deg_eq_one_FC v
  set D₁ : Divisor ℂ (FC N) := E' - Finsupp.single w 1 with hD₁
  set D₂ : Divisor ℂ (FC N) := E' - Finsupp.single w 2 with hD₂
  have hdeg₁ : D₁.degree = 2 * g := by rw [hD₁, map_sub, hE, Divisor.degree_single, hdeg1]; ring
  have hdeg₂ : D₂.degree = 2 * g - 1 := by rw [hD₂, map_sub, hE, Divisor.degree_single, hdeg1]; ring
  have hell₁ : (ell D₁ : ℤ) = g + 1 := by
    have h := ell_eq_degree_add_one_sub_genusFF_FC N D₁ (by rw [hdeg₁]; omega)
    rw [hdeg₁] at h; rw [h]; ring
  have hell₂ : (ell D₂ : ℤ) = g := by
    have h := ell_eq_degree_add_one_sub_genusFF_FC N D₂ (by rw [hdeg₂])
    rw [hdeg₂] at h; rw [h]; ring
  have hD₁w : D₁ w = E' w - 1 := by simp [hD₁]
  have hD₂w : D₂ w = E' w - 2 := by simp [hD₂]
  have hD₁v : ∀ v, v ≠ w → D₁ v = E' v := fun v hv => by simp [hD₁, Finsupp.single_apply, Ne.symm hv]
  have hD₂v : ∀ v, v ≠ w → D₂ v = E' v := fun v hv => by simp [hD₂, Finsupp.single_apply, Ne.symm hv]
  have hle : LSpace D₂ ≤ LSpace D₁ := by
    refine AlgebraicCurve.lSpace_mono (fun v => ?_)
    by_cases hv : v = w
    · subst hv; rw [hD₁w, hD₂w]; omega
    · rw [hD₁v v hv, hD₂v v hv]
  have hlt : LSpace D₂ < LSpace D₁ := by
    refine Submodule.lt_of_le_of_finrank_lt_finrank hle ?_
    have e1 : Module.finrank ℂ ↥(LSpace D₁) = ell D₁ := rfl
    have e2 : Module.finrank ℂ ↥(LSpace D₂) = ell D₂ := rfl
    rw [e1, e2]
    omega
  obtain ⟨f, hf₁, hf₂⟩ := SetLike.exists_of_lt hlt
  have hf0 : f ≠ 0 := by rintro rfl; exact hf₂ (zero_mem _)
  refine ⟨f, hf0, AlgebraicCurve.lSpace_mono (fun v => ?_) hf₁, ?_⟩
  · by_cases hv : v = w
    · subst hv; rw [hD₁w]; omega
    · rw [hD₁v v hv]
  · have hf₁' := hf₁
    have hf₂' := hf₂
    rw [show LSpace D₁ = riemannRochSpace D₁ from rfl, mem_riemannRochSpace_iff] at hf₁'
    rw [show LSpace D₂ = riemannRochSpace D₂ from rfl, mem_riemannRochSpace_iff] at hf₂'
    push_neg at hf₂'
    obtain ⟨v, -, hv⟩ := hf₂'
    have h1 := (hf₁' w).resolve_left hf0
    rw [hD₁w] at h1
    by_cases hvw : v = w
    · subst hvw
      rw [hD₂w] at hv
      omega
    · have := (hf₁' v).resolve_left hf0
      rw [hD₁v v hvw] at this
      rw [hD₂v v hvw] at hv
      omega

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_mem_span_ord_eq_one {r : ℕ} (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ)
    (s : Fin r → ↥(modularFunctionFieldBar N)) (hs : IsEmbBasis N s) (τ₀ : ℍ)
    (hj : jC N ∈ (D.pt τ₀).toValuationSubring) :
    ∃ f : FC N, f ∈ Submodule.span ℂ (Set.range fun i => phi N σ (s i)) ∧ f ≠ 0 ∧
      (D.pt τ₀).ord f = 1 := by
  classical

  have hU := fun v => exists_unique_place_over (N := N) σ v
  choose lift hlift_comap hlift_ord hlift_uniq using hU
  have hlift_inj : Function.Injective lift := fun v v' h =>
    Place.ext ((hlift_comap v).symm.trans (h ▸ hlift_comap v'))
  have hlift_new : ∀ w : Place ℂ (FC N), (∀ v, lift v ≠ w) →
      ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        w.toValuationSubring.comap (phi N σ) ≠ v.toValuationSubring := by
    intro w hw v h
    exact hw v (hlift_uniq v w h).symm

  letI : Algebra (AlgebraicClosure ℚ) ℂ := σ.toAlgebra
  letI : Algebra ↥(modularFunctionFieldBar N) (FC N) := (phi N σ).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (FC N) := ((algebraMap ℂ (FC N)).comp σ).toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ (FC N) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (FC N) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      show ((algebraMap ℂ (FC N)).comp σ) c = phi N σ (algebraMap (AlgebraicClosure ℚ) _ c)
      rw [phi_algebraMap]; rfl
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : IsCurveOver ℂ (FC N) := ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull ℂ N
  have hrange : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionFieldFull N),
      (⟨coeffEmb ℂ y, coeffEmb_mem_laurentBaseChange ℂ hy⟩ : FC N) ∈
        Set.range (algebraMap ↥(modularFunctionFieldBar N) (FC N)) := fun y hy =>
    ⟨⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩,
      phi_coeffEmb σ y hy⟩
  have hgen : IntermediateField.adjoin ℂ (Set.range (algebraMap ↥(modularFunctionFieldBar N) (FC N))) = ⊤ := by
    apply top_le_iff.mp
    rw [← ModularCurve.adjoin_jBar_jNBar_eq_top ℂ N]
    apply IntermediateField.adjoin.mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h <;> rw [h]
    · exact hrange jq (jq_mem_full N)
    · exact hrange (qExpand ℚ N jq) (jqd_mem_full N (dvd_refl N))
  have hfg := ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar N
  have hfg' : ∃ x : FC N, Transcendental ℂ x ∧ FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set (FC N))) (FC N) :=
    ⟨_, ModularCurve.transcendental_coeffEmb_jq ℂ N, ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full ℂ N⟩

  have hgg : genusFF ℂ (FC N) = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed
      (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) ℂ (FC N) hfg hfg' hgen

  have hembs : embDivisor N = Finsupp.single (cuspInftyBar N) (embDegree N : ℤ) := by
    rw [embDivisor, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hmapEC : Finsupp.mapDomain lift (embDivisor N) =
      Finsupp.single (lift (cuspInftyBar N)) (embDegree N : ℤ) := by
    rw [hembs, Finsupp.mapDomain_single]
  set EC : Divisor ℂ (FC N) := Finsupp.single (lift (cuspInftyBar N)) (embDegree N : ℤ) with hEC

  have hne : D.pt τ₀ ≠ lift (cuspInftyBar N) := by
    intro h
    have hc : (D.pt τ₀).toValuationSubring.comap (phi N σ) = (cuspInftyBar N).toValuationSubring := by
      rw [h]; exact hlift_comap _
    have : jB N ∈ (cuspInftyBar N).toValuationSubring := by
      rw [← hc, ValuationSubring.mem_comap, phi_jB]; exact hj
    apply absurd this
    unfold cuspInftyBar
    rw [qInftyPlaceBar_toValuationSubring]
    exact notMem_qIntegersBar_of_order_eq_neg_one (order_coeffEmb_jq (AlgebraicClosure ℚ))
  have hEC0 : EC (D.pt τ₀) = 0 := by
    rw [hEC, Finsupp.single_apply, if_neg (Ne.symm hne)]
  have hdegEC : EC.degree = 2 * (genusFF ℂ (FC N) : ℤ) + 1 := by
    rw [hEC, Divisor.degree_single, deg_eq_one_FC, hgg, embDegree]
    push_cast
    ring

  obtain ⟨f, hf0, hfL, hford⟩ := exists_mem_lSpace_ord_add_eq_one_FC EC hdegEC (D.pt τ₀)
  rw [hEC0, add_zero] at hford
  refine ⟨f, ?_, hf0, hford⟩

  have hfL' : f ∈ LSpace (K := ℂ) (Finsupp.mapDomain lift (embDivisor N)) := by rw [hmapEC]; exact hfL
  have hspan := AlgebraicCurve.lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
    (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) ℂ (FC N) hfg hfg' hgen lift hlift_ord hlift_inj hlift_new
    (embDivisor N) hfL'
  refine Submodule.span_le.mpr ?_ hspan
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by
    rw [hs.2]; exact hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hy'
  show phi N σ y ∈ _
  rw [← hc, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, phi_algebraMap, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end ComplexRR

section WeakCharts

variable {N : ℕ} [NeZero N]

theorem exists_forall_of_eventually_atImInfty {r : ℕ} {P : Fin r → ℍ → Prop}
    (h : ∀ i, ∀ᶠ τ in atImInfty, P i τ) : ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ τ : ℍ, A₀ ≤ τ.im → ∀ i, P i τ := by
  classical
  have h' := fun i => (UpperHalfPlane.atImInfty_mem _).mp (h i)
  choose A hA using h'
  refine ⟨(∑ i, |A i|) + 1, by positivity, fun τ hτ i => hA i τ ?_⟩
  have : |A i| ≤ ∑ j, |A j| := Finset.single_le_sum (f := fun j => |A j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  show A i ≤ τ.im
  linarith [le_abs_self (A i)]

end WeakCharts

section CuspExpansion

variable {N : ℕ} [NeZero N]

def IsPres (x : FC N) (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) : Prop :=
  h ≠ 0 ∧ (x : LaurentSeries ℂ) * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
    ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)

theorem exists_isPres (x : FC N) : ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), IsPres x k g h := by
  obtain ⟨k, g, h, hh, hp⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N (x : LaurentSeries ℂ) x.2
  exact ⟨k, g, h, hh, hp⟩

theorem strictPeriods_one_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _

theorem coe_eq_of_qExpansion_eq {Γ : Subgroup (GL (Fin 2) ℝ)} {a b : ℤ} (F : ModularForm Γ a)
    (F' : ModularForm Γ b) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ Γ.strictPeriods)
    (h : qExpansion w (F : ℍ → ℂ) = qExpansion w (F' : ℍ → ℂ)) : (F : ℍ → ℂ) = (F' : ℍ → ℂ) := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods hw hΓ⟩
  funext τ
  have h1 := UpperHalfPlane.hasSum_qExpansion hw (SlashInvariantFormClass.periodic_comp_ofComplex F hΓ)
    (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ
  have h2 := UpperHalfPlane.hasSum_qExpansion hw (SlashInvariantFormClass.periodic_comp_ofComplex F' hΓ)
    (ModularFormClass.holo F') (ModularFormClass.bdd_at_infty F') τ
  rw [h] at h1
  exact h1.unique h2

theorem coe_eq_zero_of_qExpansion_eq_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F₁ : Type*} [FunLike F₁ ℍ ℂ]
    [ModularFormClass F₁ Γ k] (F : F₁) {w : ℝ}
    (hw : 0 < w) (hΓ : w ∈ Γ.strictPeriods) (h0 : qExpansion w (F : ℍ → ℂ) = 0) : ∀ τ, F τ = 0 := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods hw hΓ⟩
  intro τ
  have h1 := UpperHalfPlane.hasSum_qExpansion hw (SlashInvariantFormClass.periodic_comp_ofComplex F hΓ)
    (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ
  rw [h0] at h1
  simp only [map_zero, zero_smul, zero_mul] at h1
  exact h1.unique hasSum_zero

theorem qExpansion_ne_zero_width {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (F : ModularForm Γ k) {w : ℝ}
    (hw : 0 < w) (hΓ : w ∈ Γ.strictPeriods) (hF : F ≠ 0) : qExpansion w (F : ℍ → ℂ) ≠ 0 := by
  intro h0
  apply hF
  apply DFunLike.ext
  intro τ
  rw [ModularForm.zero_apply]
  exact coe_eq_zero_of_qExpansion_eq_zero F hw hΓ h0 τ

noncomputable def presWt (x : FC N) : ℤ := (exists_isPres x).choose
noncomputable def presNum (x : FC N) : ModularForm (CongruenceSubgroup.Gamma0 N) (presWt x) :=
  (exists_isPres x).choose_spec.choose
noncomputable def presDen (x : FC N) : ModularForm (CongruenceSubgroup.Gamma0 N) (presWt x) :=
  (exists_isPres x).choose_spec.choose_spec.choose
theorem isPres_pres (x : FC N) : IsPres x (presWt x) (presNum x) (presDen x) :=
  (exists_isPres x).choose_spec.choose_spec.choose_spec

theorem isPres_mul {x y : FC N} {k₁ k₂ : ℤ} {g₁ h₁ : ModularForm (CongruenceSubgroup.Gamma0 N) k₁}
    {g₂ h₂ : ModularForm (CongruenceSubgroup.Gamma0 N) k₂} (h1 : IsPres x k₁ g₁ h₁) (h2 : IsPres y k₂ g₂ h₂) :
    IsPres (x * y) (k₁ + k₂) (g₁.mul g₂) (h₁.mul h₂) := by
  have hΓ₁ := strictPeriods_one_Gamma0 N
  refine ⟨?_, ?_⟩
  · intro h0
    obtain ⟨A₁, hA₁⟩ := exists_forall_ne_zero_of_le_im_width h₁ one_pos hΓ₁ h1.1
    obtain ⟨A₂, hA₂⟩ := exists_forall_ne_zero_of_le_im_width h₂ one_pos hΓ₁ h2.1
    set τ : ℍ := ⟨(max (max A₁ A₂) 1 : ℝ) * Complex.I, by simp⟩ with hτ
    have hτim : τ.im = max (max A₁ A₂) 1 := by
      show ((max (max A₁ A₂) 1 : ℝ) * Complex.I).im = _
      simp
    have := congrArg (fun F : ModularForm _ (k₁ + k₂) => (F : ℍ → ℂ) τ) h0
    simp only [ModularForm.coe_mul, Pi.mul_apply, ModularForm.zero_apply] at this
    rcases mul_eq_zero.mp this with h | h
    · exact hA₁ τ (by rw [hτim]; exact (le_max_left _ _).trans (le_max_left _ _)) h
    · exact hA₂ τ (by rw [hτim]; exact (le_max_right _ _).trans (le_max_left _ _)) h
  · have hcoe : ((x * y : FC N) : LaurentSeries ℂ) = (x : LaurentSeries ℂ) * (y : LaurentSeries ℂ) := by
      first | rfl | simp
    rw [hcoe, ModularForm.qExpansion_mul one_pos hΓ₁, ModularForm.qExpansion_mul one_pos hΓ₁, map_mul, map_mul,
      ← h1.2, ← h2.2]
    ring

theorem isPres_add {x y : FC N} {k₁ k₂ : ℤ} {g₁ h₁ : ModularForm (CongruenceSubgroup.Gamma0 N) k₁}
    {g₂ h₂ : ModularForm (CongruenceSubgroup.Gamma0 N) k₂} (h1 : IsPres x k₁ g₁ h₁) (h2 : IsPres y k₂ g₂ h₂) :
    IsPres (x + y) (k₁ + k₂) (g₁.mul h₂ + h₁.mul g₂) (h₁.mul h₂) := by
  have hΓ₁ := strictPeriods_one_Gamma0 N
  refine ⟨(isPres_mul h1 h2).1, ?_⟩
  have hcoe : ((x + y : FC N) : LaurentSeries ℂ) = (x : LaurentSeries ℂ) + (y : LaurentSeries ℂ) := by
    first | rfl | simp
  rw [hcoe, ModularForm.coe_add, ModularFormClass.qExpansion_add one_pos hΓ₁,
    ModularForm.qExpansion_mul one_pos hΓ₁, ModularForm.qExpansion_mul one_pos hΓ₁,
    ModularForm.qExpansion_mul one_pos hΓ₁, map_add, map_mul, map_mul, map_mul, ← h1.2, ← h2.2]
  ring

end CuspExpansion

section CuspPlace

variable {N : ℕ} [NeZero N]

abbrev Γ1 : Subgroup (GL (Fin 2) ℝ) := (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range

theorem LaurentSeries.order_inv' {K : Type*} [Field K] {x : LaurentSeries K} (hx : x ≠ 0) :
    (x⁻¹).order = -x.order := by
  have h := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one] at h
  omega

def qadicSubring (K : Type*) [Field K] : ValuationSubring (LaurentSeries K) where
  carrier := {f | 0 ≤ f.order}
  mul_mem' {a b} ha hb := by
    show 0 ≤ (a * b).order
    by_cases ha0 : a = 0; · simp [ha0]
    by_cases hb0 : b = 0; · simp [hb0]
    rw [HahnSeries.order_mul ha0 hb0]; exact add_nonneg ha hb
  one_mem' := by show 0 ≤ (1 : LaurentSeries K).order; simp
  add_mem' {a b} ha hb := by
    show 0 ≤ (a + b).order
    by_cases hab : a + b = 0; · simp [hab]
    by_cases ha0 : a = 0; · simpa [ha0] using hb
    by_cases hb0 : b = 0; · simpa [hb0] using ha
    exact (le_min ha hb).trans (HahnSeries.min_order_le_order_add hab)
  zero_mem' := by show 0 ≤ (0 : LaurentSeries K).order; simp
  neg_mem' {a} ha := by show 0 ≤ (-a).order; rwa [HahnSeries.order_neg]
  mem_or_inv_mem' a := by
    by_cases ha0 : a = 0
    · left; show 0 ≤ a.order; simp [ha0]
    rcases le_or_gt 0 a.order with h | h
    · exact Or.inl h
    · right; show 0 ≤ (a⁻¹).order; rw [LaurentSeries.order_inv' ha0]; omega

theorem mem_qadicSubring_iff {K : Type*} [Field K] {f : LaurentSeries K} : f ∈ qadicSubring K ↔ 0 ≤ f.order := Iff.rfl

theorem coeffEmb_jq_eq_jqModC' : coeffEmb ℂ jq = jqModC ℂ := by
  rw [← jqModC_rat, coeffEmb]
  exact coeffMap_jqModC (algebraMap ℚ ℂ)

theorem one_mem_strictPeriods_range :
    (1 : ℝ) ∈ Γ1.strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  have h := mapGL_T_zpow 1
  simp only [Nat.cast_one] at h
  rw [← h]
  exact ⟨_, rfl⟩

theorem hasSum_qExpansion_mul_levelOne {a k : ℤ} {F₁ : Type*} [FunLike F₁ ℍ ℂ] [ModularFormClass F₁ Γ1 a]
    (F : F₁)
    (H : ModularForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (qExpansion 1 ((F : ℍ → ℂ) * (H : ℍ → ℂ))) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ n) (((F : ℍ → ℂ) * (H : ℍ → ℂ)) τ) := by
  have hΓ₁ := strictPeriods_one_Gamma0 N
  have hR := one_mem_strictPeriods_range
  haveI : Fact (IsCusp OnePoint.infty ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ₁⟩
  haveI : Fact (IsCusp OnePoint.infty Γ1) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hR⟩
  have h1 := SlashInvariantFormClass.periodic_comp_ofComplex F hR
  have h2 := SlashInvariantFormClass.periodic_comp_ofComplex H hΓ₁
  refine UpperHalfPlane.hasSum_qExpansion one_pos ?_ ?_ ?_ τ
  · intro z
    have e1 := h1 z
    have e2 := h2 z
    simp only [Function.comp_apply, Pi.mul_apply] at e1 e2 ⊢
    rw [e1, e2]
  · exact (ModularFormClass.holo F).mul (ModularFormClass.holo H)
  · exact (ModularFormClass.bdd_at_infty F).mul (ModularFormClass.bdd_at_infty H)

theorem analyticAt_cuspFunction_levelOne {a : ℤ} {F₁ : Type*} [FunLike F₁ ℍ ℂ] [ModularFormClass F₁ Γ1 a] (F : F₁) :
    AnalyticAt ℂ (cuspFunction 1 (F : ℍ → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero F one_pos one_mem_strictPeriods_range

theorem analyticAt_cuspFunction_gamma0 {k : ℤ} (H : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    AnalyticAt ℂ (cuspFunction 1 (H : ℍ → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero H one_pos (strictPeriods_one_Gamma0 N)

theorem mul_eq_mul_of_qExpansion_eq {a b k k' : ℤ} {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ] [ModularFormClass F₁ Γ1 a]
    [FunLike F₂ ℍ ℂ] [ModularFormClass F₂ Γ1 b]
    (F : F₁)
    (F' : F₂)
    (H : ModularForm (CongruenceSubgroup.Gamma0 N) k) (H' : ModularForm (CongruenceSubgroup.Gamma0 N) k')
    (h : qExpansion 1 ((F : ℍ → ℂ) * (H : ℍ → ℂ)) = qExpansion 1 ((F' : ℍ → ℂ) * (H' : ℍ → ℂ))) :
    (F : ℍ → ℂ) * (H : ℍ → ℂ) = (F' : ℍ → ℂ) * (H' : ℍ → ℂ) := by
  funext τ
  have h1 := hasSum_qExpansion_mul_levelOne F H τ
  have h2 := hasSum_qExpansion_mul_levelOne F' H' τ
  rw [h] at h1
  exact h1.unique h2

noncomputable def E4cube : ModularForm Γ1 12 :=
  ModularForm.mcast (by norm_num) ((ModularForm.E₄.mul ModularForm.E₄).mul ModularForm.E₄)

theorem coe_E4cube : (E4cube : ℍ → ℂ) = (ModularForm.E₄ : ℍ → ℂ) ^ 3 := by
  funext τ
  show ((ModularForm.E₄.mul ModularForm.E₄).mul ModularForm.E₄) τ = _
  simp only [ModularForm.coe_mul, Pi.mul_apply, Pi.pow_apply]
  ring

theorem qExpansion_E4cube :
    ((qExpansion 1 (E4cube : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 := by
  have hE := analyticAt_cuspFunction_levelOne ModularForm.E₄
  have hE2 : AnalyticAt ℂ (cuspFunction 1 ((ModularForm.E₄ : ℍ → ℂ) * (ModularForm.E₄ : ℍ → ℂ))) 0 := by
    have := analyticAt_cuspFunction_levelOne (ModularForm.E₄.mul ModularForm.E₄)
    first
      | simpa [ModularForm.coe_mul] using this
      | (have h' := this; simp [ModularForm.coe_mul] at h'; exact h')
      | (simp [ModularForm.coe_mul]; exact this)
      | exact this
  rw [coe_E4cube, pow_succ, pow_two, UpperHalfPlane.qExpansion_mul hE2 hE, UpperHalfPlane.qExpansion_mul hE hE]
  simp only [map_mul]
  ring

theorem slash_levelOne {a : ℤ} {F₁ : Type*} [FunLike F₁ ℍ ℂ] [SlashInvariantFormClass F₁ Γ1 a] (F : F₁) (γ : SL(2, ℤ)) :
    (F : ℍ → ℂ) ∣[a] γ = (F : ℍ → ℂ) := by
  rw [ModularForm.SL_slash]
  exact SlashInvariantForm.slash_action_eqn F _ ⟨γ, rfl⟩

end CuspPlace

section CuspOrder

variable {N : ℕ} [NeZero N]

theorem LaurentSeries.order_pow' {K : Type*} [Field K] {x : LaurentSeries K} (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).order = n * x.order := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, HahnSeries.order_mul (pow_ne_zero _ hx) hx, ih]
    push_cast
    ring

theorem Place.ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {x : F} (hx : x ≠ 0) (n : ℕ) :
    v.ord (x ^ n) = n * v.ord x := by
  induction n with
  | zero => simp [v.ord_one]
  | succ n ih =>
    rw [pow_succ, v.ord_mul (pow_ne_zero _ hx) hx, ih]
    push_cast
    ring

end CuspOrder

section WidthGeneric

variable {N : ℕ} [NeZero N]

theorem gamma0_map_le_range' (N : ℕ) :
    (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ) ≤ Γ1 := by
  rintro _ ⟨g, -, rfl⟩; exact ⟨g, rfl⟩

theorem strictPeriods_conjGamma0_le_Gamma1 (N : ℕ) (γ : SL(2, ℤ)) {w : ℝ}
    (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) : w ∈ Γ1.strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff] at hΓ ⊢
  set U := Matrix.GeneralLinearGroup.upperRightHom w with hU
  have h1 : (ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹)⁻¹ • U ∈
      (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hΓ
  have h2 : (ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹)⁻¹ • U ∈ Γ1 := gamma0_map_le_range' N h1
  rw [← map_inv, inv_inv, ConjAct.toConjAct_smul] at h2
  have hγ : (γ : GL (Fin 2) ℝ) ∈ Γ1 := ⟨γ, rfl⟩
  have : U = (γ : GL (Fin 2) ℝ)⁻¹ * ((γ : GL (Fin 2) ℝ) * U * (γ : GL (Fin 2) ℝ)⁻¹) * (γ : GL (Fin 2) ℝ) := by group
  rw [this]
  exact Γ1.mul_mem (Γ1.mul_mem (Γ1.inv_mem hγ) h2) hγ

theorem analyticAt_cuspFunction_slashW {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) :
    AnalyticAt ℂ (cuspFunction w ((f : ℍ → ℂ) ∣[k] γ)) 0 := by
  rw [← coe_translate_SL N f γ]
  exact ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.translate f (γ : GL (Fin 2) ℝ))
    hw hΓ

theorem slashQuot_eq_of_isPresW {x : FC N} {k₁ k₂ : ℤ} {g₁ h₁ : ModularForm (CongruenceSubgroup.Gamma0 N) k₁}
    {g₂ h₂ : ModularForm (CongruenceSubgroup.Gamma0 N) k₂} (h1 : IsPres x k₁ g₁ h₁) (h2 : IsPres x k₂ g₂ h₂)
    (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) : slashQuot N g₁ h₁ γ w = slashQuot N g₂ h₂ γ w := by
  have hΓ₁ := strictPeriods_one_Gamma0 N

  have hqq : qExpansion 1 ((g₁.mul h₂ : ModularForm _ (k₁ + k₂)) : ℍ → ℂ) =
      qExpansion 1 ((g₂.mul h₁ : ModularForm _ (k₂ + k₁)) : ℍ → ℂ) := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [ModularForm.qExpansion_mul one_pos hΓ₁, ModularForm.qExpansion_mul one_pos hΓ₁, map_mul, map_mul,
      ← h1.2, ← h2.2]
    ring
  have hfun : (g₁ : ℍ → ℂ) * (h₂ : ℍ → ℂ) = (g₂ : ℍ → ℂ) * (h₁ : ℍ → ℂ) := by
    have := coe_eq_of_qExpansion_eq (g₁.mul h₂) (g₂.mul h₁) one_pos hΓ₁ hqq
    simpa [ModularForm.coe_mul] using this

  have hsl : ((g₁ : ℍ → ℂ) ∣[k₁] γ) * ((h₂ : ℍ → ℂ) ∣[k₂] γ) =
      ((g₂ : ℍ → ℂ) ∣[k₂] γ) * ((h₁ : ℍ → ℂ) ∣[k₁] γ) := by
    rw [← ModularForm.mul_slash_SL2, ← ModularForm.mul_slash_SL2, hfun, add_comm]

  have hqN : qExpansion w ((g₁ : ℍ → ℂ) ∣[k₁] γ) * qExpansion w ((h₂ : ℍ → ℂ) ∣[k₂] γ) =
      qExpansion w ((g₂ : ℍ → ℂ) ∣[k₂] γ) * qExpansion w ((h₁ : ℍ → ℂ) ∣[k₁] γ) := by
    rw [← UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_slashW g₁ γ hw hΓ) (analyticAt_cuspFunction_slashW h₂ γ hw hΓ),
      ← UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_slashW g₂ γ hw hΓ) (analyticAt_cuspFunction_slashW h₁ γ hw hΓ),
      hsl]

  have hH₁ : ((qExpansion w ((h₁ : ℍ → ℂ) ∣[k₁] γ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [← coe_translate_SL N h₁ γ, Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
    exact qExpansion_ne_zero_width _ hw hΓ (translate_ne_zero N h₁ h1.1 γ)
  have hH₂ : ((qExpansion w ((h₂ : ℍ → ℂ) ∣[k₂] γ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [← coe_translate_SL N h₂ γ, Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
    exact qExpansion_ne_zero_width _ hw hΓ (translate_ne_zero N h₂ h2.1 γ)
  rw [slashQuot, slashQuot, div_eq_div_iff hH₁ hH₂, ← map_mul, ← map_mul, hqN]

noncomputable def cuspExpW (γ : SL(2, ℤ)) (w : ℝ) (x : FC N) : LaurentSeries ℂ :=
  slashQuot N (presNum x) (presDen x) γ w

theorem cuspExpW_eq_slashQuot (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) {x : FC N} {k : ℤ} {g h : ModularForm (CongruenceSubgroup.Gamma0 N) k}
    (hp : IsPres x k g h) : cuspExpW γ w x = slashQuot N g h γ w :=
  slashQuot_eq_of_isPresW (isPres_pres x) hp γ hw hΓ

theorem slashQuot_mulW {k₁ k₂ : ℤ} (g₁ h₁ : ModularForm (CongruenceSubgroup.Gamma0 N) k₁)
    (g₂ h₂ : ModularForm (CongruenceSubgroup.Gamma0 N) k₂) (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) :
    slashQuot N (g₁.mul g₂) (h₁.mul h₂) γ w = slashQuot N g₁ h₁ γ w * slashQuot N g₂ h₂ γ w := by
  simp only [slashQuot, ModularForm.coe_mul, ModularForm.mul_slash_SL2]
  rw [UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_slashW g₁ γ hw hΓ) (analyticAt_cuspFunction_slashW g₂ γ hw hΓ),
    UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_slashW h₁ γ hw hΓ) (analyticAt_cuspFunction_slashW h₂ γ hw hΓ),
    map_mul, map_mul, mul_div_mul_comm]

theorem slashQuot_addPresW {k₁ k₂ : ℤ} (g₁ h₁ : ModularForm (CongruenceSubgroup.Gamma0 N) k₁)
    (g₂ h₂ : ModularForm (CongruenceSubgroup.Gamma0 N) k₂) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) :
    slashQuot N (g₁.mul h₂ + h₁.mul g₂) (h₁.mul h₂) γ w = slashQuot N g₁ h₁ γ w + slashQuot N g₂ h₂ γ w := by
  have hH₁ : ((qExpansion w ((h₁ : ℍ → ℂ) ∣[k₁] γ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [← coe_translate_SL N h₁ γ, Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
    exact qExpansion_ne_zero_width _ hw hΓ (translate_ne_zero N h₁ hh₁ γ)
  have hH₂ : ((qExpansion w ((h₂ : ℍ → ℂ) ∣[k₂] γ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [← coe_translate_SL N h₂ γ, Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
    exact qExpansion_ne_zero_width _ hw hΓ (translate_ne_zero N h₂ hh₂ γ)
  have han := fun {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) => analyticAt_cuspFunction_slashW f γ hw hΓ
  simp only [slashQuot, ModularForm.coe_add, ModularForm.coe_mul, ModularForm.mul_slash_SL2]
  rw [show (((g₁ : ℍ → ℂ) * (h₂ : ℍ → ℂ) + (h₁ : ℍ → ℂ) * (g₂ : ℍ → ℂ)) ∣[k₁ + k₂] γ) =
      ((g₁ : ℍ → ℂ) ∣[k₁] γ) * ((h₂ : ℍ → ℂ) ∣[k₂] γ) + ((h₁ : ℍ → ℂ) ∣[k₁] γ) * ((g₂ : ℍ → ℂ) ∣[k₂] γ) by
      rw [SlashAction.add_slash, ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2]]
  have hA : AnalyticAt ℂ (cuspFunction w (((g₁ : ℍ → ℂ) ∣[k₁] γ) * ((h₂ : ℍ → ℂ) ∣[k₂] γ))) 0 := by
    have := han (g₁.mul h₂)
    simpa [ModularForm.coe_mul, ModularForm.mul_slash_SL2] using this
  have hB : AnalyticAt ℂ (cuspFunction w (((h₁ : ℍ → ℂ) ∣[k₁] γ) * ((g₂ : ℍ → ℂ) ∣[k₂] γ))) 0 := by
    have := han (h₁.mul g₂)
    simpa [ModularForm.coe_mul, ModularForm.mul_slash_SL2] using this
  rw [UpperHalfPlane.qExpansion_add hA hB, UpperHalfPlane.qExpansion_mul (han g₁) (han h₂),
    UpperHalfPlane.qExpansion_mul (han h₁) (han g₂), UpperHalfPlane.qExpansion_mul (han h₁) (han h₂)]
  simp only [map_add, map_mul]
  field_simp
  try ring

noncomputable def cuspExpHomW (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) : FC N →+* LaurentSeries ℂ where
  toFun := cuspExpW γ w
  map_one' := by
    obtain ⟨k, g, h, hp⟩ := exists_isPres (1 : FC N)
    have hp' : IsPres (1 : FC N) k h h := ⟨hp.1, by simp⟩
    rw [cuspExpW_eq_slashQuot γ hw hΓ hp', slashQuot]
    have hH : ((qExpansion w ((h : ℍ → ℂ) ∣[k] γ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
      rw [← coe_translate_SL N h γ, Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
      exact qExpansion_ne_zero_width _ hw hΓ (translate_ne_zero N h hp.1 γ)
    exact div_self hH
  map_mul' x y := by
    rw [cuspExpW_eq_slashQuot γ hw hΓ (isPres_mul (isPres_pres x) (isPres_pres y)), slashQuot_mulW _ _ _ _ γ hw hΓ]
    rfl
  map_zero' := by
    obtain ⟨k, g, h, hp⟩ := exists_isPres (1 : FC N)
    have hp' : IsPres (0 : FC N) k 0 h := ⟨hp.1, by simp [UpperHalfPlane.qExpansion_zero]⟩
    rw [cuspExpW_eq_slashQuot γ hw hΓ hp', slashQuot]
    simp [UpperHalfPlane.qExpansion_zero]
  map_add' x y := by
    rw [cuspExpW_eq_slashQuot γ hw hΓ (isPres_add (isPres_pres x) (isPres_pres y)),
      slashQuot_addPresW _ _ _ _ (isPres_pres x).1 (isPres_pres y).1 γ hw hΓ]
    rfl

theorem cuspExpHomW_apply (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) (x : FC N) : cuspExpHomW γ hw hΓ x = cuspExpW γ w x := rfl

theorem cuspExpHomW_algebraMap (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) (c : ℂ) :
    cuspExpHomW γ hw hΓ (algebraMap ℂ (FC N) c) = HahnSeries.C c := by
  obtain ⟨k, g, h, hp⟩ := exists_isPres (1 : FC N)
  have hΓ₁ := strictPeriods_one_Gamma0 N
  have hfun : ((c • h : ModularForm _ k) : ℍ → ℂ) = c • (h : ℍ → ℂ) := by ext; simp
  have hp' : IsPres (algebraMap ℂ (FC N) c) k (c • h) h := by
    refine ⟨hp.1, ?_⟩
    have hcoe : ((algebraMap ℂ (FC N) c : FC N) : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) c := by
      first | rfl | simp
    rw [hcoe, hfun, ModularFormClass.qExpansion_smul one_pos hΓ₁, PowerSeries.smul_eq_C_mul, map_mul,
      HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]
  rw [cuspExpHomW_apply, cuspExpW_eq_slashQuot γ hw hΓ hp', slashQuot, hfun, ModularForm.SL_smul_slash]
  have hH : ((qExpansion w ((h : ℍ → ℂ) ∣[k] γ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [← coe_translate_SL N h γ, Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
    exact qExpansion_ne_zero_width _ hw hΓ (translate_ne_zero N h hp.1 γ)
  rw [show qExpansion w (c • ((h : ℍ → ℂ) ∣[k] γ)) = PowerSeries.C c * qExpansion w ((h : ℍ → ℂ) ∣[k] γ) by
    rw [← coe_translate_SL N h γ, ← PowerSeries.smul_eq_C_mul,
      ← ModularFormClass.qExpansion_smul hw hΓ]
    try (congr 1; ext τ; simp [ModularForm.coe_smul])]
  rw [map_mul, HahnSeries.ofPowerSeries_C, mul_div_assoc, div_self hH, mul_one]

theorem slash_chart_cuspExpW (x : FC N) (hx : x ≠ 0) (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) :
    cuspExpHomW γ hw hΓ x ≠ 0 ∧ ∃ Φ : ℂ → ℂ, AnalyticAt ℂ Φ 0 ∧
      Φ 0 = (cuspExpHomW γ hw hΓ x).coeff (cuspExpHomW γ hw hΓ x).order ∧
      ∀ᶠ τ in atImInfty, realize N (x : LaurentSeries ℂ) (γ • τ) =
        Function.Periodic.qParam w (τ : ℂ) ^ (cuspExpHomW γ hw hΓ x).order * Φ (Function.Periodic.qParam w (τ : ℂ)) := by
  have hp := isPres_pres x
  exact slash_chart N x hx (presNum x) (presDen x) hp.1 hp.2 γ hw
    hΓ

noncomputable def cuspExpBW (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) (σ : AlgebraicClosure ℚ →+* ℂ) :
    ↥(modularFunctionFieldBar N) →+* LaurentSeries ℂ := (cuspExpHomW γ hw hΓ).comp (phi N σ)

theorem cuspExpBW_apply (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) (σ : AlgebraicClosure ℚ →+* ℂ) (y : ↥(modularFunctionFieldBar N)) :
    cuspExpBW γ hw hΓ σ y = cuspExpHomW γ hw hΓ (phi N σ y) := rfl

theorem order_cuspExpHomW_jC_neg (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) : (cuspExpHomW γ hw hΓ (jC N)).order < 0 := by
  classical
  have hp := isPres_pres (jC N)
  set k := presWt (jC N)
  set G := presNum (jC N)
  set H := presDen (jC N)
  set Δf : CuspForm Γ1 12 := CuspForm.discriminant with hΔf
  have hcoeΔ : (Δf : ℍ → ℂ) = ModularForm.discriminant := rfl

  have hjq : ((jC N : FC N) : LaurentSeries ℂ) =
      ((qExpansion 1 (E4cube : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion 1 (Δf : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    show coeffEmb ℂ jq = _
    rw [coeffEmb_jq_eq_jqModC', ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, qExpansion_E4cube, hcoeΔ]
  have hΔ0 : ((qExpansion 1 (Δf : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
    intro h0
    exact ModularForm.discriminant_ne_zero UpperHalfPlane.I
      (coe_eq_zero_of_qExpansion_eq_zero Δf one_pos one_mem_strictPeriods_range h0 UpperHalfPlane.I)
  have hformal : ((qExpansion 1 (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) *
      ((qExpansion 1 (Δf : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (E4cube : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) *
        ((qExpansion 1 (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [← hp.2, hjq]
    field_simp

  have hfun : (Δf : ℍ → ℂ) * (G : ℍ → ℂ) = (E4cube : ℍ → ℂ) * (H : ℍ → ℂ) := by
    apply mul_eq_mul_of_qExpansion_eq
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_levelOne Δf) (analyticAt_cuspFunction_gamma0 G),
      UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_levelOne E4cube) (analyticAt_cuspFunction_gamma0 H),
      map_mul, map_mul, mul_comm, hformal]

  have hsl : (Δf : ℍ → ℂ) * ((G : ℍ → ℂ) ∣[k] γ) = (E4cube : ℍ → ℂ) * ((H : ℍ → ℂ) ∣[k] γ) := by
    have h1 := congrArg (fun f : ℍ → ℂ => f ∣[(12 : ℤ) + k] γ) hfun
    simp only [ModularForm.mul_slash_SL2, slash_levelOne] at h1
    exact h1

  have hRN : w ∈ Γ1.strictPeriods := strictPeriods_conjGamma0_le_Gamma1 N γ hΓ
  have hanΔ : AnalyticAt ℂ (cuspFunction w (Δf : ℍ → ℂ)) 0 := ModularFormClass.analyticAt_cuspFunction_zero Δf hw hRN
  have hanE : AnalyticAt ℂ (cuspFunction w (E4cube : ℍ → ℂ)) 0 := ModularFormClass.analyticAt_cuspFunction_zero E4cube hw hRN
  have hqN : qExpansion w (Δf : ℍ → ℂ) * qExpansion w ((G : ℍ → ℂ) ∣[k] γ) =
      qExpansion w (E4cube : ℍ → ℂ) * qExpansion w ((H : ℍ → ℂ) ∣[k] γ) := by
    rw [← UpperHalfPlane.qExpansion_mul hanΔ (analyticAt_cuspFunction_slashW G γ hw hΓ),
      ← UpperHalfPlane.qExpansion_mul hanE (analyticAt_cuspFunction_slashW H γ hw hΓ), hsl]

  have hH : ((qExpansion w ((H : ℍ → ℂ) ∣[k] γ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [← coe_translate_SL N H γ, Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
    exact qExpansion_ne_zero_width _ hw hΓ (translate_ne_zero N H hp.1 γ)
  have hΔN0 : ((qExpansion w (Δf : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
    intro h0
    exact ModularForm.discriminant_ne_zero UpperHalfPlane.I
      (coe_eq_zero_of_qExpansion_eq_zero Δf hw hRN h0 UpperHalfPlane.I)
  have hθ : cuspExpHomW γ hw hΓ (jC N) =
      ((qExpansion w (E4cube : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion w (Δf : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [cuspExpHomW_apply, cuspExpW, slashQuot, div_eq_div_iff hH hΔN0, ← map_mul, ← map_mul, mul_comm, hqN, mul_comm]

  have hE0 : PowerSeries.coeff 0 (qExpansion w (E4cube : ℍ → ℂ)) ≠ 0 := by

    rw [UpperHalfPlane.qExpansion_coeff_zero hw hanE (SlashInvariantFormClass.periodic_comp_ofComplex E4cube hRN),
      ← UpperHalfPlane.qExpansion_coeff_zero one_pos (analyticAt_cuspFunction_levelOne E4cube)
        (SlashInvariantFormClass.periodic_comp_ofComplex E4cube one_mem_strictPeriods_range)]
    have h4 : PowerSeries.coeff 0 (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) = 1 :=
      EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
    have hcube : qExpansion 1 (E4cube : ℍ → ℂ) = qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) ^ 3 := by
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
      rw [qExpansion_E4cube, map_pow]
    have h4' : PowerSeries.constantCoeff (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) = 1 := by
      rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [hcube, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, h4']
    norm_num
  have hΔ00 : PowerSeries.coeff 0 (qExpansion w (Δf : ℍ → ℂ)) = 0 := by
    rw [UpperHalfPlane.qExpansion_coeff_zero hw hanΔ (SlashInvariantFormClass.periodic_comp_ofComplex Δf hRN), hcoeΔ]
    exact UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero ModularForm.discriminant_isZeroAtImInfty
  have hordE : (((qExpansion w (E4cube : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)).order = 0 := by
    have := order_coe_eq (n := 0) hE0 (fun i hi => absurd hi (Nat.not_lt_zero i))
    simpa using this

  have hΔne : qExpansion w (Δf : ℍ → ℂ) ≠ 0 := fun h0 =>
    hΔN0 (by rw [h0, map_zero])
  have hex : ∃ n, PowerSeries.coeff n (qExpansion w (Δf : ℍ → ℂ)) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hΔne (PowerSeries.ext fun n => by simpa using hall n)
  have hordΔ : 1 ≤ (((qExpansion w (Δf : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)).order := by
    have hn := Nat.find_spec hex
    have hmin : ∀ i < Nat.find hex, PowerSeries.coeff i (qExpansion w (Δf : ℍ → ℂ)) = 0 := fun i hi => by
      have := Nat.find_min hex hi; push_neg at this; exact this
    rw [order_coe_eq hn hmin]
    have h0 : Nat.find hex ≠ 0 := fun h => hn (by rw [h]; exact hΔ00)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
  have hEN0 : (((qExpansion w (E4cube : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) ≠ 0 := by
    intro h0
    apply hE0
    have h1 : qExpansion w (E4cube : ℍ → ℂ) = 0 :=
      HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero])
    rw [h1, map_zero]
  rw [hθ, div_eq_mul_inv, HahnSeries.order_mul hEN0 (inv_ne_zero hΔN0), LaurentSeries.order_inv' hΔN0, hordE]
  omega

theorem cuspExpBW_algebraMap (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) (σ : AlgebraicClosure ℚ →+* ℂ) (a : AlgebraicClosure ℚ) :
    cuspExpBW γ hw hΓ σ (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) a) = HahnSeries.C (σ a) := by
  rw [cuspExpBW_apply, phi_algebraMap, cuspExpHomW_algebraMap]

set_option synthInstance.maxHeartbeats 800000 in

theorem exists_place_cuspW (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) (σ : AlgebraicClosure ℚ →+* ℂ) :
    ∃ p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ) := by
  haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({jB N} : Set ↥(modularFunctionFieldBar N))) ↥(modularFunctionFieldBar N) :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jB N} : Set ↥(modularFunctionFieldBar N)))
      ↥(modularFunctionFieldBar N) := by
    first
      | infer_instance
      | exact Algebra.IsSeparable.of_finite _ _
  refine AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable (jB N) (cuspExpBW γ hw hΓ σ)
    (qadicSubring ℂ) (fun a => ?_) ⟨jB N, ?_⟩
  · rw [cuspExpBW_algebraMap, mem_qadicSubring_iff]
    by_cases ha : σ a = 0
    · simp [ha]
    · rw [HahnSeries.C_apply, HahnSeries.order_single ha]
  · rw [mem_qadicSubring_iff, cuspExpBW_apply, phi_jB, not_le]
    exact order_cuspExpHomW_jC_neg γ hw hΓ

theorem mem_place_cuspW_iff {γ : SL(2, ℤ)} {w : ℝ} {hw : 0 < w} {hΓ : w ∈ (conjGamma0 N γ).strictPeriods} {σ : AlgebraicClosure ℚ →+* ℂ}
    {p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}
    (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ)) (y : ↥(modularFunctionFieldBar N)) :
    y ∈ p.toValuationSubring ↔ 0 ≤ (cuspExpHomW γ hw hΓ (phi N σ y)).order := by
  rw [hp, ValuationSubring.mem_comap, mem_qadicSubring_iff, cuspExpBW_apply]

theorem exists_pivot_order_leW {r : ℕ} (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) (σ : AlgebraicClosure ℚ →+* ℂ)
    (s : Fin r → ↥(modularFunctionFieldBar N)) (hs : IsEmbBasis N s)
    (k : ℕ) (u : ↥(modularFunctionFieldBar N)) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) :
    ∃ i₀ : Fin r, (∀ i, (cuspExpHomW γ hw hΓ (phi N σ (s i₀))).order ≤ (cuspExpHomW γ hw hΓ (phi N σ (s i))).order) ∧
      (k : ℤ) * (cuspExpHomW γ hw hΓ (phi N σ (s i₀))).order ≤ (cuspExpHomW γ hw hΓ (phi N σ u)).order := by
  obtain ⟨p, hp⟩ := exists_place_cuspW (N := N) γ hw hΓ σ
  obtain ⟨i₀, hi₀⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs p
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hsmem : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := fun i => by
    rw [← hs.2]; exact Submodule.subset_span ⟨i, rfl⟩

  have hθ0 : ∀ y : ↥(modularFunctionFieldBar N), y ≠ 0 → cuspExpHomW γ hw hΓ (phi N σ y) ≠ 0 := fun y hy =>
    (map_ne_zero_iff _ (cuspExpHomW γ hw hΓ).injective).mpr (phi_ne_zero σ hy)

  have hkey : ∀ y : ↥(modularFunctionFieldBar N), y ≠ 0 → 0 ≤ p.ord y → 0 ≤ (cuspExpHomW γ hw hΓ (phi N σ y)).order :=
    fun y hy h => (mem_place_cuspW_iff hp y).mp ((AlgebraicCurve.Place.mem_iff_ord_nonneg _ hy).mpr h)
  refine ⟨i₀, fun i => ?_, ?_⟩
  ·
    have hord : 0 ≤ p.ord (s i * (s i₀)⁻¹) := by
      rw [p.ord_mul (hs0 i) (inv_ne_zero (hs0 i₀)), p.ord_inv]
      rcases (mem_riemannRochSpace_iff.mp (hsmem i)) p with h0 | h
      · exact absurd h0 (hs0 i)
      · omega
    have h := hkey _ (mul_ne_zero (hs0 i) (inv_ne_zero (hs0 i₀))) hord
    rw [map_mul, map_inv₀, map_mul, map_inv₀, HahnSeries.order_mul (hθ0 _ (hs0 i)) (inv_ne_zero (hθ0 _ (hs0 i₀))),
      LaurentSeries.order_inv' (hθ0 _ (hs0 i₀))] at h
    omega
  ·
    have hord : 0 ≤ p.ord (u * ((s i₀)⁻¹) ^ k) := by
      rw [p.ord_mul hu (pow_ne_zero _ (inv_ne_zero (hs0 i₀))), Place.ord_pow' p (inv_ne_zero (hs0 i₀)), p.ord_inv]
      rcases (mem_riemannRochSpace_iff.mp huL) p with h0 | h
      · exact absurd h0 hu
      · simp only [Finsupp.smul_apply, smul_eq_mul] at h
        nlinarith [h, hi₀]
    have h := hkey _ (mul_ne_zero hu (pow_ne_zero _ (inv_ne_zero (hs0 i₀)))) hord
    rw [map_mul, map_pow, map_inv₀, map_mul, map_pow, map_inv₀,
      HahnSeries.order_mul (hθ0 _ hu) (pow_ne_zero _ (inv_ne_zero (hθ0 _ (hs0 i₀)))),
      LaurentSeries.order_pow' (inv_ne_zero (hθ0 _ (hs0 i₀))), LaurentSeries.order_inv' (hθ0 _ (hs0 i₀))] at h
    nlinarith [h]

end WidthGeneric

section PencilUB

variable {N : ℕ} [NeZero N]

private noncomputable def _root_.CUSPATLAS.val (D : ComplexPlaceDictionary N) (x : FC N) (τ : ℍ) : ℂ := (D.pt τ).evalAt x

p2m_export "CUSPATLAS" "val"

theorem ord_pivotIndex_le' {r : ℕ} (s : Fin r → ↥(modularFunctionFieldBar N))
    (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) (hr : 0 < r) (j : Fin r) :
    w.ord (s (pivotIndex s w hr)) ≤ w.ord (s j) := by
  classical
  have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => w.ord (s i)) Finset.univ_nonempty
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  simp only [pivotIndex, dif_pos hex]
  exact Classical.choose_spec hex j

end PencilUB

section Final

variable {N : ℕ} [NeZero N]

end Final

end CUSPATLAS

namespace CUSPATLAS

section CuspIndex

variable {N : ℕ} [NeZero N]
variable {γ : SL(2, ℤ)} {w : ℝ} {hw : 0 < w} {hΓ : w ∈ (conjGamma0 N γ).strictPeriods}
variable {σ : AlgebraicClosure ℚ →+* ℂ} {p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}

theorem LaurentSeries.order_zpow' {K : Type*} [Field K] {x : LaurentSeries K} (hx : x ≠ 0) (n : ℤ) :
    (x ^ n).order = n * x.order := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, LaurentSeries.order_pow' hx]
  · rw [zpow_neg, zpow_natCast, LaurentSeries.order_inv' (pow_ne_zero _ hx), LaurentSeries.order_pow' hx]
    ring

theorem cuspExpBW_ne_zero (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ))
    {y : ↥(modularFunctionFieldBar N)} (hy : y ≠ 0) : cuspExpHomW γ hw hΓ (phi N σ y) ≠ 0 :=
  (map_ne_zero_iff _ (cuspExpHomW γ hw hΓ).injective).mpr (phi_ne_zero σ hy)

theorem order_cuspExp_eq_zero_of_ord_eq_zero
    (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ))
    {y : ↥(modularFunctionFieldBar N)} (hy : y ≠ 0) (h0 : p.ord y = 0) :
    (cuspExpHomW γ hw hΓ (phi N σ y)).order = 0 := by
  have h1 : 0 ≤ (cuspExpHomW γ hw hΓ (phi N σ y)).order :=
    (mem_place_cuspW_iff hp y).mp ((AlgebraicCurve.Place.mem_iff_ord_nonneg _ hy).mpr h0.ge)
  have h2 : 0 ≤ (cuspExpHomW γ hw hΓ (phi N σ y⁻¹)).order :=
    (mem_place_cuspW_iff hp y⁻¹).mp
      ((AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hy)).mpr (by rw [p.ord_inv, h0, neg_zero]))
  rw [map_inv₀, map_inv₀, LaurentSeries.order_inv' (cuspExpBW_ne_zero hp hy)] at h2
  omega

theorem exists_index_cuspPlace (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ)) :
    ∃ f : ℕ, 1 ≤ f ∧ ∀ y : ↥(modularFunctionFieldBar N), y ≠ 0 →
      (cuspExpHomW γ hw hΓ (phi N σ y)).order = (f : ℤ) * p.ord y := by
  obtain ⟨t, ht⟩ := AlgebraicCurve.Place.exists_ord_eq_one p
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [p.ord_zero] at ht
    exact zero_ne_one ht
  set et : ℤ := (cuspExpHomW γ hw hΓ (phi N σ t)).order with het
  have het_nn : 0 ≤ et :=
    (mem_place_cuspW_iff hp t).mp ((AlgebraicCurve.Place.mem_iff_ord_nonneg _ ht0).mpr (by rw [ht]; norm_num))
  have het_pos : 0 < et := by
    by_contra hle
    push_neg at hle
    have h0 : et = 0 := le_antisymm hle het_nn

    have hinv : 0 ≤ (cuspExpHomW γ hw hΓ (phi N σ t⁻¹)).order := by
      rw [map_inv₀, map_inv₀, LaurentSeries.order_inv' (cuspExpBW_ne_zero hp ht0), ← het, h0]; norm_num
    have hmem := (mem_place_cuspW_iff hp t⁻¹).mpr hinv
    have := (AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero ht0)).mp hmem
    rw [p.ord_inv, ht] at this
    omega
  refine ⟨et.toNat, by omega, fun y hy => ?_⟩
  rw [Int.toNat_of_nonneg het_nn]

  set n : ℤ := p.ord y with hn
  have hz0 : y * t ^ (-n) ≠ 0 := mul_ne_zero hy (zpow_ne_zero _ ht0)
  have hzord : p.ord (y * t ^ (-n)) = 0 := by
    rw [p.ord_mul hy (zpow_ne_zero _ ht0), p.ord_zpow, ht]; ring
  have hz := order_cuspExp_eq_zero_of_ord_eq_zero hp hz0 hzord
  rw [map_mul, map_mul, HahnSeries.order_mul (cuspExpBW_ne_zero hp hy) (cuspExpBW_ne_zero hp (zpow_ne_zero _ ht0)),
    map_zpow₀, map_zpow₀, LaurentSeries.order_zpow' (cuspExpBW_ne_zero hp ht0)] at hz
  linarith

theorem order_pos_iff (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ))
    {y : ↥(modularFunctionFieldBar N)} (hy : y ≠ 0) :
    0 < p.ord y ↔ 0 < (cuspExpHomW γ hw hΓ (phi N σ y)).order := by
  obtain ⟨f, hf, hall⟩ := exists_index_cuspPlace hp
  rw [hall y hy]
  have hf' : (0 : ℤ) < f := by exact_mod_cast hf
  constructor
  · intro h; positivity
  · intro h; by_contra hle; push_neg at hle; nlinarith

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem coeff_zero_cuspExp_eq (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ))
    {y : ↥(modularFunctionFieldBar N)} (hy : y ∈ p.toValuationSubring) :
    (cuspExpHomW γ hw hΓ (phi N σ y)).coeff 0 = σ (p.evalAt y) := by
  classical
  have hrat : p.IsRational := isRational_FB p
  set a : AlgebraicClosure ℚ := p.evalAt y with ha
  set z : ↥(modularFunctionFieldBar N) := y - algebraMap (AlgebraicClosure ℚ) _ a with hz

  have hzmem : z ∈ p.toValuationSubring := sub_mem hy (p.algebraMap_mem' a)
  have hθz : cuspExpHomW γ hw hΓ (phi N σ z) = cuspExpHomW γ hw hΓ (phi N σ y) - HahnSeries.C (σ a) := by
    rw [hz, map_sub, map_sub, phi_algebraMap, cuspExpHomW_algebraMap]
  by_cases hz0 : z = 0
  · have : cuspExpHomW γ hw hΓ (phi N σ y) = HahnSeries.C (σ a) := by
      rw [← sub_eq_zero, ← hθz, hz0, map_zero, map_zero]
    rw [this]
    simp [HahnSeries.C_apply]
  ·
    have hres : IsLocalRing.residue p.toValuationSubring (⟨z, hzmem⟩ : p.toValuationSubring) = 0 := by
      have h1 := p.algebraMap_evalAt hrat hy
      have hcoe : (⟨z, hzmem⟩ : p.toValuationSubring) =
          ⟨y, hy⟩ - algebraMap (AlgebraicClosure ℚ) p.toValuationSubring a := by
        apply Subtype.ext
        show z = y - ((algebraMap (AlgebraicClosure ℚ) p.toValuationSubring a : p.toValuationSubring) : ↥(modularFunctionFieldBar N))
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, ← h1]
      show algebraMap (AlgebraicClosure ℚ) p.ResidueField (p.evalAt y) -
        algebraMap p.toValuationSubring p.ResidueField (algebraMap (AlgebraicClosure ℚ) p.toValuationSubring a) = 0
      rw [← IsScalarTower.algebraMap_apply, ha, sub_self]
    have hmax : (⟨z, hzmem⟩ : p.toValuationSubring) ∈ IsLocalRing.maximalIdeal p.toValuationSubring :=
      (IsLocalRing.residue_eq_zero_iff _).mp hres
    have hordz : 0 < p.ord z := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax
      have hnn := (AlgebraicCurve.Place.mem_iff_ord_nonneg _ hz0).mp hzmem
      rcases hnn.eq_or_lt with h | h
      · exfalso; apply hmax
        have hinvmem : z⁻¹ ∈ p.toValuationSubring :=
          (AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hz0)).mpr (by rw [p.ord_inv, ← h, neg_zero])
        exact ⟨⟨⟨z, hzmem⟩, ⟨z⁻¹, hinvmem⟩, Subtype.ext (mul_inv_cancel₀ hz0), Subtype.ext (inv_mul_cancel₀ hz0)⟩, rfl⟩
      · exact h
    have hθord : 0 < (cuspExpHomW γ hw hΓ (phi N σ z)).order := (order_pos_iff hp hz0).mp hordz
    have hcoef : (cuspExpHomW γ hw hΓ (phi N σ z)).coeff 0 = 0 := HahnSeries.coeff_eq_zero_of_lt_order hθord
    rw [hθz] at hcoef
    have h2 : (cuspExpHomW γ hw hΓ (phi N σ y)).coeff 0 - σ a = 0 := by
      first
        | simpa [HahnSeries.C_apply] using hcoef
        | (rw [HahnSeries.sub_coeff] at hcoef; simpa [HahnSeries.C_apply] using hcoef)
    exact sub_eq_zero.mp h2

end CuspIndex

section CuspInj

variable {N : ℕ} [NeZero N]

theorem mapGL_T_zpow_int (n : ℤ) :
    (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n) : GL (Fin 2) ℝ) =
      Matrix.GeneralLinearGroup.upperRightHom (n : ℝ) := by
  have hT : ModularGroup.T ^ n = ⟨!![1, n; 0, 1], by simp [Matrix.det_fin_two_of]⟩ :=
    Subtype.ext (ModularGroup.coe_T_zpow n)
  rw [hT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.upperRightHom_apply, Matrix.SpecialLinearGroup.mapGL,
      Matrix.SpecialLinearGroup.map_apply_coe]

theorem intCast_mem_strictPeriods_conjGamma0 (γ : SL(2, ℤ)) (n : ℤ)
    (h : γ * ModularGroup.T ^ n * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N) :
    (n : ℝ) ∈ (conjGamma0 N γ).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, ← mapGL_T_zpow_int]
  have hmem : (Matrix.SpecialLinearGroup.mapGL ℝ (γ * ModularGroup.T ^ n * γ⁻¹) : GL (Fin 2) ℝ) ∈
      (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
    Subgroup.mem_map_of_mem _ h
  have h2 := Subgroup.smul_mem_pointwise_smul _ (ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹) _ hmem
  convert h2 using 1
  rw [ConjAct.toConjAct_smul, inv_inv, map_mul, map_mul, map_inv]
  show _ = ((γ : GL (Fin 2) ℝ))⁻¹ *
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ) * (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n)) *
      ((Matrix.SpecialLinearGroup.mapGL ℝ γ))⁻¹) * (γ : GL (Fin 2) ℝ)
  have hc : (γ : GL (Fin 2) ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := rfl
  rw [hc]
  group

theorem strictPeriods_conjGamma0_subset (γ : SL(2, ℤ)) :
    ((conjGamma0 N γ).strictPeriods : Set ℝ) ⊆ (AddSubgroup.zmultiples (1 : ℝ) : Set ℝ) := by
  intro x hx
  have := strictPeriods_conjGamma0_le_Gamma1 N γ hx
  rwa [Subgroup.strictPeriods_SL2Z] at this

scoped instance discreteTopology_strictPeriods_conjGamma0 (γ : SL(2, ℤ)) :
    DiscreteTopology ↥((conjGamma0 N γ).strictPeriods) :=
  DiscreteTopology.of_subset (X := ℝ) (s := ((AddSubgroup.zmultiples (1 : ℝ) : AddSubgroup ℝ) : Set ℝ))
    (inferInstanceAs (DiscreteTopology (AddSubgroup.zmultiples (1 : ℝ))))
    (strictPeriods_conjGamma0_subset γ)

theorem apply_one_zero_eq_zero_of_im_gt (M : SL(2, ℤ)) (τ : ℍ) (hτ : 1 < τ.im) (hMτ : 1 < (M • τ).im) :
    M 1 0 = 0 := by
  by_contra hc
  have him := ModularGroup.im_smul_eq_div_normSq M τ
  have hle := UpperHalfPlane.c_mul_im_sq_le_normSq_denom (M : GL (Fin 2) ℝ) τ
  have hcR : ((M : GL (Fin 2) ℝ) 1 0 : ℝ) = ((M 1 0 : ℤ) : ℝ) := by
    first | rfl | simp [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.map_apply_coe]
  have hc1 : (1 : ℝ) ≤ |((M 1 0 : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
  have hpos : 0 < Complex.normSq (denom (M : GL (Fin 2) ℝ) (τ : ℂ)) :=
    UpperHalfPlane.normSq_denom_pos _ τ.im_ne_zero
  have him0 := τ.im_pos
  have h1 : τ.im ^ 2 ≤ Complex.normSq (denom (M : GL (Fin 2) ℝ) (τ : ℂ)) := by
    rw [hcR] at hle
    have hτle : τ.im ≤ |((M 1 0 : ℤ) : ℝ)| * τ.im := le_mul_of_one_le_left him0.le hc1
    calc τ.im ^ 2 ≤ (|((M 1 0 : ℤ) : ℝ)| * τ.im) ^ 2 := by
            first
              | exact pow_le_pow_left₀ him0.le hτle 2
              | nlinarith [abs_nonneg (((M 1 0 : ℤ) : ℝ))]
      _ = (((M 1 0 : ℤ) : ℝ) * τ.im) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
      _ ≤ _ := hle
  have hcoe : Complex.normSq (denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) M)) (τ : ℂ)) =
      Complex.normSq (denom (M : GL (Fin 2) ℝ) (τ : ℂ)) := rfl
  rw [hcoe] at him

  have h2 : (M • τ).im ≤ 1 / τ.im := by
    rw [him, div_le_div_iff₀ hpos him0]
    nlinarith [h1, him0]
  have h3 : 1 / τ.im < 1 := by rw [div_lt_one him0]; exact hτ
  linarith

theorem SL_neg_smul' (g : SL(2, ℤ)) (z : ℍ) : -g • z = g • z := by simp

theorem exists_eq_T_zpow_of_apply_one_zero_eq_zero (M : SL(2, ℤ)) (hc : M 1 0 = 0) :
    ∃ n : ℤ, (M = ModularGroup.T ^ n ∨ M = -ModularGroup.T ^ n) ∧
      ∀ τ : ℍ, ((M • τ : ℍ) : ℂ) = (τ : ℂ) + n := by
  have hdet : M 0 0 * M 1 1 = 1 := by
    have := M.2
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at this
    exact this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · have hM : M = ModularGroup.T ^ (M 0 1) := by
      apply Subtype.ext
      rw [ModularGroup.coe_T_zpow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hc, hd]
    refine ⟨M 0 1, Or.inl hM, fun τ => ?_⟩
    conv_lhs => rw [hM]
    exact ModularGroup.coe_T_zpow_smul_eq τ
  · have hM : M = -ModularGroup.T ^ (-(M 0 1)) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hc, hd]
    refine ⟨-(M 0 1), Or.inr hM, fun τ => ?_⟩
    conv_lhs => rw [hM, SL_neg_smul']
    exact ModularGroup.coe_T_zpow_smul_eq τ

theorem strictWidthInfty_conjGamma0_pos (γ : SL(2, ℤ)) : 0 < Subgroup.strictWidthInfty (conjGamma0 N γ) := by
  rcases (Subgroup.strictWidthInfty_nonneg (conjGamma0 N γ)).eq_or_lt with h | h
  · exfalso
    have hN := natCast_mem_strictPeriods_conjGamma0 N γ
    rw [Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty, ← h, AddSubgroup.mem_zmultiples_iff] at hN
    obtain ⟨k, hk⟩ := hN
    simp at hk
    exact (NeZero.ne N) (by exact_mod_cast hk.symm)
  · exact h

theorem qParam_add_int_mul (h : ℝ) (hh : h ≠ 0) (z : ℂ) (k : ℤ) :
    Function.Periodic.qParam h (z + k * h) = Function.Periodic.qParam h z := by
  simp only [Function.Periodic.qParam]
  have hC : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  rw [show 2 * ↑Real.pi * Complex.I * (z + ↑k * ↑h) / ↑h =
      2 * ↑Real.pi * Complex.I * z / ↑h + ↑k * (2 * ↑Real.pi * Complex.I) by
      first | (field_simp; ring) | field_simp]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem cusp_chart_inj (γ : SL(2, ℤ)) : ∃ Y₀ : ℝ, ∀ τ τ' : ℍ, Y₀ < τ.im → Y₀ < τ'.im →
    ∀ δ ∈ CongruenceSubgroup.Gamma0 N, δ • (γ • τ) = γ • τ' →
      Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N γ)) (τ : ℂ) =
        Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N γ)) (τ' : ℂ) := by
  refine ⟨1, fun τ τ' hτ hτ' δ hδ heq => ?_⟩
  set h : ℝ := Subgroup.strictWidthInfty (conjGamma0 N γ) with hh
  have hpos : 0 < h := strictWidthInfty_conjGamma0_pos γ
  set M : SL(2, ℤ) := γ⁻¹ * δ * γ with hM
  have hMτ : M • τ = τ' := by
    rw [hM, mul_smul, mul_smul, heq, ← mul_smul, inv_mul_cancel, one_smul]
  have hc : M 1 0 = 0 := apply_one_zero_eq_zero_of_im_gt M τ hτ (by rw [hMτ]; exact hτ')
  obtain ⟨n, hMT, hact⟩ := exists_eq_T_zpow_of_apply_one_zero_eq_zero M hc

  have hconj : γ * ModularGroup.T ^ n * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
    rcases hMT with h1 | h1
    · have : γ * ModularGroup.T ^ n * γ⁻¹ = δ := by rw [← h1, hM]; group
      rw [this]; exact hδ
    · have : γ * ModularGroup.T ^ n * γ⁻¹ = -δ := by
        rw [show ModularGroup.T ^ n = -M by rw [h1, neg_neg], hM]
        simp only [mul_neg, neg_mul]
        congr 1; group
      rw [this]
      rw [CongruenceSubgroup.Gamma0_mem] at hδ ⊢
      simpa [Matrix.SpecialLinearGroup.coe_neg] using hδ
  have hper : (n : ℝ) ∈ (conjGamma0 N γ).strictPeriods := intCast_mem_strictPeriods_conjGamma0 γ n hconj
  rw [Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty, AddSubgroup.mem_zmultiples_iff] at hper
  obtain ⟨k, hk⟩ := hper
  have hnR : (n : ℝ) = (k : ℝ) * h := by rw [hh, ← zsmul_eq_mul]; exact hk.symm
  have hnC : ((n : ℤ) : ℂ) = (k : ℂ) * (h : ℂ) := by
    have e : ((n : ℤ) : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
    rw [e, hnR]; push_cast; ring
  have hτ'eq : (τ' : ℂ) = (τ : ℂ) + n := by rw [← hMτ]; exact hact τ
  rw [hτ'eq, hnC]
  exact (qParam_add_int_mul h hpos.ne' (τ : ℂ) k).symm

end CuspInj

section CuspFactor

variable {N : ℕ} [NeZero N]

section Idx
variable {γ : SL(2, ℤ)} {w : ℝ} {hw : 0 < w} {hΓ : w ∈ (conjGamma0 N γ).strictPeriods}
variable {σ : AlgebraicClosure ℚ →+* ℂ} {p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}

noncomputable def cuspIdx (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ)) : ℕ :=
  (exists_index_cuspPlace hp).choose

theorem one_le_cuspIdx (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ)) :
    1 ≤ cuspIdx hp :=
  (exists_index_cuspPlace hp).choose_spec.1

theorem order_eq_cuspIdx_mul (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ))
    {y : ↥(modularFunctionFieldBar N)} (hy : y ≠ 0) :
    (cuspExpHomW γ hw hΓ (phi N σ y)).order = (cuspIdx hp : ℤ) * p.ord y :=
  (exists_index_cuspPlace hp).choose_spec.2 y hy

end Idx

theorem eventually_apply_smul_ne_zero {k : ℤ} (h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (γ : SL(2, ℤ)) : ∀ᶠ τ : ℍ in atImInfty, (h : ℍ → ℂ) (γ • τ) ≠ 0 := by
  have hΓN := natCast_mem_strictPeriods_conjGamma0 N γ
  obtain ⟨A, hA⟩ := exists_forall_ne_zero_of_le_im_width
    (ModularForm.translate h (γ : GL (Fin 2) ℝ) : ModularForm (conjGamma0 N γ) k) (natCast_pos_of_neZero N) hΓN
    (translate_ne_zero N h hh γ)
  rw [UpperHalfPlane.atImInfty, Filter.eventually_comap]
  filter_upwards [Filter.eventually_ge_atTop A] with m hm τ hτ
  have h1 := hA τ (by rw [hτ]; exact hm)
  intro h0
  apply h1
  rw [coe_translate_SL, ModularForm.SL_slash_apply, h0, zero_mul]

theorem realize_add_smul_eventually (x y : FC N) (γ : SL(2, ℤ)) :
    ∀ᶠ τ : ℍ in atImInfty, realize N ((x + y : FC N) : LaurentSeries ℂ) (γ • τ) =
      realize N (x : LaurentSeries ℂ) (γ • τ) + realize N (y : LaurentSeries ℂ) (γ • τ) := by
  obtain ⟨k₁, g₁, h₁, hh₁, hp₁⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N (x : LaurentSeries ℂ) x.2
  obtain ⟨k₂, g₂, h₂, hh₂, hp₂⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N (y : LaurentSeries ℂ) y.2
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  set G : ModularForm _ (k₁ + k₂) := g₁.mul h₂ + h₁.mul g₂ with hGdef
  set H : ModularForm _ (k₁ + k₂) := h₁.mul h₂ with hHdef
  have hpres : ((x + y : FC N) : LaurentSeries ℂ) *
      ((qExpansion 1 (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    have hcoe : ((x + y : FC N) : LaurentSeries ℂ) = (x : LaurentSeries ℂ) + (y : LaurentSeries ℂ) := by
      first | rfl | simp
    rw [hcoe, hHdef, hGdef, ModularForm.coe_add, ModularFormClass.qExpansion_add one_pos hΓ,
      ModularForm.qExpansion_mul one_pos hΓ, ModularForm.qExpansion_mul one_pos hΓ,
      ModularForm.qExpansion_mul one_pos hΓ, map_add, map_mul, map_mul, map_mul, add_mul,
      ← mul_assoc, hp₁, mul_comm ((qExpansion 1 (h₁ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ),
      ← mul_assoc, hp₂]
    ring
  filter_upwards [eventually_apply_smul_ne_zero h₁ hh₁ γ, eventually_apply_smul_ne_zero h₂ hh₂ γ] with τ h1 h2
  have hH : (H : ℍ → ℂ) (γ • τ) ≠ 0 := by
    rw [hHdef, ModularForm.coe_mul, Pi.mul_apply]; exact mul_ne_zero h1 h2
  rw [ModularCurve.realize_eq_div N G H _ hpres _ hH, ModularCurve.realize_eq_div N g₁ h₁ _ hp₁ _ h1,
    ModularCurve.realize_eq_div N g₂ h₂ _ hp₂ _ h2, hGdef, hHdef]
  simp only [ModularForm.coe_add, ModularForm.coe_mul, Pi.add_apply, Pi.mul_apply]
  field_simp
  try ring

theorem realize_smul_smul_eventually (c : ℂ) (x : FC N) (γ : SL(2, ℤ)) :
    ∀ᶠ τ : ℍ in atImInfty, realize N ((c • x : FC N) : LaurentSeries ℂ) (γ • τ) =
      c * realize N (x : LaurentSeries ℂ) (γ • τ) := by
  obtain ⟨k, g, h, hh, hp⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N (x : LaurentSeries ℂ) x.2
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  have hfun : ((c • g : ModularForm _ k) : ℍ → ℂ) = c • (g : ℍ → ℂ) := by ext; simp
  have hpres : ((c • x : FC N) : LaurentSeries ℂ) *
      ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 ((c • g : ModularForm _ k) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    have hcoe : ((c • x : FC N) : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) c * (x : LaurentSeries ℂ) := by
      rw [Algebra.smul_def]
      first | rfl | simp [Algebra.smul_def]
    rw [hcoe, mul_assoc, hp, hfun, ModularFormClass.qExpansion_smul one_pos hΓ, PowerSeries.smul_eq_C_mul,
      map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]
  filter_upwards [eventually_apply_smul_ne_zero h hh γ] with τ h1
  rw [ModularCurve.realize_eq_div N (c • g) h _ hpres _ h1, ModularCurve.realize_eq_div N g h _ hp _ h1, hfun]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem realize_sub_smul_smul_eventually (x y : FC N) (c : ℂ) (γ : SL(2, ℤ)) :
    ∀ᶠ τ : ℍ in atImInfty, realize N ((x - c • y : FC N) : LaurentSeries ℂ) (γ • τ) =
      realize N (x : LaurentSeries ℂ) (γ • τ) - c * realize N (y : LaurentSeries ℂ) (γ • τ) := by
  have hxy : (x - c • y : FC N) = x + (-c) • y := by
    rw [Algebra.smul_def, Algebra.smul_def, map_neg]; ring
  filter_upwards [realize_add_smul_eventually x ((-c) • y) γ, realize_smul_smul_eventually (-c) y γ] with τ h1 h2
  rw [hxy, h1, h2]
  ring

theorem im_invQParam_gt_width {w A : ℝ} (hw : 0 < w) {q : ℂ} (hq0 : q ≠ 0)
    (hq : ‖q‖ < Real.exp (-2 * Real.pi * A / w)) : A < (Function.Periodic.invQParam w q).im := by
  rw [Function.Periodic.im_invQParam]
  have hlog : Real.log ‖q‖ < -2 * Real.pi * A / w := by
    have := Real.log_lt_log (norm_pos_iff.mpr hq0) hq
    rwa [Real.log_exp] at this
  have h2 : 0 < 2 * Real.pi := by positivity
  rw [show -w / (2 * Real.pi) * Real.log ‖q‖ = (w * (-Real.log ‖q‖)) / (2 * Real.pi) by ring,
    lt_div_iff₀ h2]
  have h3 : -Real.log ‖q‖ > 2 * Real.pi * A / w := by rw [neg_mul, neg_mul, neg_div] at hlog; linarith
  have h4 := mul_lt_mul_of_pos_left h3 hw
  rw [show w * (2 * Real.pi * A / w) = A * (2 * Real.pi) by field_simp] at h4
  linarith

theorem eventually_nhdsNE_of_forall_qParam {w : ℝ} (hw : 0 < w) {P : ℂ → Prop} {A : ℝ}
    (h : ∀ τ : ℍ, A ≤ τ.im → P (Function.Periodic.qParam w (τ : ℂ))) : ∀ᶠ Q in 𝓝[≠] (0 : ℂ), P Q := by
  set A' : ℝ := max A 1 with hA'
  have hε : 0 < Real.exp (-2 * Real.pi * A' / w) := Real.exp_pos _
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨Real.exp (-2 * Real.pi * A' / w), hε, fun Q hQ hQ0 => ?_⟩
  rw [dist_zero_right] at hQ
  have him : A' < (Function.Periodic.invQParam w Q).im := im_invQParam_gt_width hw hQ0 hQ
  have him0 : 0 < (Function.Periodic.invQParam w Q).im := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_right A 1) him)
  have hc : ((ofComplex (Function.Periodic.invQParam w Q) : ℍ) : ℂ) = Function.Periodic.invQParam w Q := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him0]; try rfl
  have hP := h (ofComplex (Function.Periodic.invQParam w Q))
    (by rw [← UpperHalfPlane.coe_im, hc]; exact (le_max_left A 1).trans him.le)
  rwa [hc, Function.Periodic.qParam_right_inv hw.ne' hQ0] at hP

theorem eventuallyEq_of_forall_qParam {w : ℝ} (hw : 0 < w) {F G : ℂ → ℂ} (hF : ContinuousAt F 0)
    (hG : ContinuousAt G 0) {A : ℝ} (h : ∀ τ : ℍ, A ≤ τ.im → F (Function.Periodic.qParam w (τ : ℂ)) = G (Function.Periodic.qParam w (τ : ℂ))) :
    ∀ᶠ Q in 𝓝 (0 : ℂ), F Q = G Q := by
  have hne : ∀ᶠ Q in 𝓝[≠] (0 : ℂ), F Q = G Q := eventually_nhdsNE_of_forall_qParam hw (P := fun Q => F Q = G Q) h
  have h0 : F 0 = G 0 := by
    have hF' : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 (F 0)) := hF.tendsto.mono_left nhdsWithin_le_nhds
    have hG' : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 (G 0)) := hG.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hF' (hG'.congr' (hne.mono fun Q hQ => hQ.symm))
  rw [← nhdsNE_sup_pure (0 : ℂ), Filter.eventually_sup]
  exact ⟨hne, by simpa using h0⟩

theorem zpow_chart_exponent {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 ≠ 0)
    {n : ℤ} (h : ∀ᶠ Q in 𝓝[≠] (0 : ℂ), F Q = Q ^ n * G Q) :
    0 ≤ n ∧ F 0 = (if n = 0 then G 0 else 0) ∧ (∀ᶠ Q in 𝓝 (0 : ℂ), F Q = Q ^ n.toNat * G Q) ∧
      analyticOrderAt F 0 = (n.toNat : ℕ∞) := by
  have hFt : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 (F 0)) := hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hGt : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 (G 0)) := hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hid : Tendsto (fun Q : ℂ => Q) (𝓝[≠] (0 : ℂ)) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

  have hn : 0 ≤ n := by
    by_contra hneg
    push_neg at hneg
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩

    have hGeq : ∀ᶠ Q in 𝓝[≠] (0 : ℂ), G Q = F Q * Q ^ (m + 1) := by
      filter_upwards [h, self_mem_nhdsWithin] with Q hQ hQ0
      rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hQ0
      rw [hQ, hm, zpow_neg, mul_comm (_⁻¹) (G Q), mul_assoc, ← zpow_natCast, Nat.cast_add, Nat.cast_one,
        inv_mul_cancel₀ (zpow_ne_zero _ hQ0), mul_one]
    have hlim : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 (F 0 * 0 ^ (m + 1))) :=
      (hFt.mul (hid.pow (m + 1))).congr' (hGeq.mono fun Q hQ => hQ.symm)
    rw [zero_pow (Nat.succ_ne_zero m), mul_zero] at hlim
    exact hG0 (tendsto_nhds_unique hGt hlim)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
  simp only [Int.toNat_natCast]
  have h' : ∀ᶠ Q in 𝓝[≠] (0 : ℂ), F Q = Q ^ k * G Q := by
    filter_upwards [h] with Q hQ; rwa [zpow_natCast] at hQ
  have hF0 : F 0 = if (k : ℤ) = 0 then G 0 else 0 := by
    have hlim : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 ((0 : ℂ) ^ k * G 0)) :=
      ((hid.pow k).mul hGt).congr' (h'.mono fun Q hQ => hQ.symm)
    have := tendsto_nhds_unique hFt hlim
    rw [this]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · rw [zero_pow hk.ne', zero_mul, if_neg (by exact_mod_cast hk.ne')]
  have hall : ∀ᶠ Q in 𝓝 (0 : ℂ), F Q = Q ^ k * G Q := by
    rw [← nhdsNE_sup_pure (0 : ℂ), Filter.eventually_sup]
    refine ⟨h', ?_⟩
    simp only [Filter.eventually_pure]
    rw [hF0]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · rw [zero_pow hk.ne', zero_mul, if_neg (by exact_mod_cast hk.ne')]
  refine ⟨hn, hF0, hall, ?_⟩
  rw [hF.analyticOrderAt_eq_natCast]
  exact ⟨G, hG, hG0, by filter_upwards [hall] with Q hQ; rw [hQ, sub_zero, smul_eq_mul]⟩

theorem LaurentSeries.leadingCoeff_div' {K : Type*} [Field K] {a b : LaurentSeries K} (hb : b ≠ 0) :
    (a / b).leadingCoeff = a.leadingCoeff / b.leadingCoeff := by
  have h := HahnSeries.leadingCoeff_mul (a / b) b
  rw [div_mul_cancel₀ a hb] at h
  rw [h, mul_div_assoc, div_self (HahnSeries.leadingCoeff_ne_zero.mpr hb), mul_one]

theorem LaurentSeries.order_div' {K : Type*} [Field K] {a b : LaurentSeries K} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a / b).order = a.order - b.order := by
  rw [div_eq_mul_inv, HahnSeries.order_mul ha (inv_ne_zero hb), LaurentSeries.order_inv' hb]; ring

theorem LaurentSeries.coeff_zero_div' {K : Type*} [Field K] {a b : LaurentSeries K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hle : b.order ≤ a.order) :
    (a / b).coeff 0 = if a.order = b.order then a.leadingCoeff / b.leadingCoeff else 0 := by
  have hord : (a / b).order = a.order - b.order := LaurentSeries.order_div' ha hb
  split_ifs with h
  · rw [← LaurentSeries.leadingCoeff_div' hb, HahnSeries.leadingCoeff_eq, hord, h, sub_self]
  · apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [hord]; omega

theorem LaurentSeries.order_pos_of_coeff_zero' {K : Type*} [Field K] {a : LaurentSeries K} (ha : a ≠ 0)
    (h0 : 0 ≤ a.order) (hc : a.coeff 0 = 0) : 0 < a.order := by
  rcases h0.eq_or_lt with h | h
  · exfalso
    have := (HahnSeries.coeff_order_eq_zero.not.mpr) ha
    rw [← h] at this
    exact this hc
  · exact h

section Main
variable {γ : SL(2, ℤ)} {w : ℝ} {hw : 0 < w} {hΓ : w ∈ (conjGamma0 N γ).strictPeriods}
variable {σ : AlgebraicClosure ℚ →+* ℂ} {p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}

theorem centre_value (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ))
    {r : ℕ} (s : Fin r → ↥(modularFunctionFieldBar N)) (hs0 : ∀ i, s i ≠ 0) {piv i : Fin r}
    (hle : (cuspExpHomW γ hw hΓ (phi N σ (s piv))).order ≤ (cuspExpHomW γ hw hΓ (phi N σ (s i))).order) :
    s i / s piv ∈ p.toValuationSubring ∧
    σ (p.evalAt (s i / s piv)) =
      if (cuspExpHomW γ hw hΓ (phi N σ (s i))).order = (cuspExpHomW γ hw hΓ (phi N σ (s piv))).order then
        (cuspExpHomW γ hw hΓ (phi N σ (s i))).leadingCoeff / (cuspExpHomW γ hw hΓ (phi N σ (s piv))).leadingCoeff
      else 0 := by
  have hθ0 : ∀ j, cuspExpHomW γ hw hΓ (phi N σ (s j)) ≠ 0 := fun j =>
    (map_ne_zero_iff _ (cuspExpHomW γ hw hΓ).injective).mpr (phi_ne_zero σ (hs0 j))
  have hdiv : cuspExpHomW γ hw hΓ (phi N σ (s i / s piv)) =
      cuspExpHomW γ hw hΓ (phi N σ (s i)) / cuspExpHomW γ hw hΓ (phi N σ (s piv)) := by
    rw [map_div₀, map_div₀]
  have hmem : s i / s piv ∈ p.toValuationSubring := by
    rw [mem_place_cuspW_iff hp, hdiv, LaurentSeries.order_div' (hθ0 i) (hθ0 piv)]
    omega
  refine ⟨hmem, ?_⟩
  rw [← coeff_zero_cuspExp_eq hp hmem, hdiv, LaurentSeries.coeff_zero_div' (hθ0 i) (hθ0 piv) hle]

theorem ord_eq_neg_embDivisor_of_forall_le {r : ℕ} (s : Fin r → ↥(modularFunctionFieldBar N)) (hs : IsEmbBasis N s)
    (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) {piv : Fin r}
    (hle : ∀ i, p.ord (s piv) ≤ p.ord (s i)) : p.ord (s piv) = -(embDivisor N p) := by
  obtain ⟨j, hj⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs p
  have hmem : s piv ∈ riemannRochSpace (embDivisor N) := by
    rw [← hs.2]; exact Submodule.subset_span ⟨piv, rfl⟩
  rcases (mem_riemannRochSpace_iff.mp hmem) p with h0 | h
  · exact absurd h0 (hs.1.ne_zero piv)
  · have := hle j; omega

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 8000000 in

theorem cusp_chart_factor {r : ℕ} (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods)
    (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → ↥(modularFunctionFieldBar N)) (hs : IsEmbBasis N s)
    {p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}
    (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ))
    (hRR : ∃ g ∈ riemannRochSpace (embDivisor N), g ≠ 0 ∧ p.ord g + embDivisor N p = 1)
    (Φ : ℂ → (Fin r → ℂ)) (m : ℤ) (hA : ∀ i, AnalyticAt ℂ (fun q => Φ q i) 0) {A₀ : ℝ}
    (hΦ : ∀ τ : ℍ, A₀ ≤ τ.im → ∀ i, Φ (Function.Periodic.qParam w (τ : ℂ)) i =
      Function.Periodic.qParam w (τ : ℂ) ^ m * realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (γ • τ))
    (piv : Fin r) (hpiv : Φ 0 piv ≠ 0) :
    ∃ Ψ : ℂ → (Fin r → ℂ), (∀ i, AnalyticAt ℂ (fun q => Ψ q i) 0) ∧
      (∀ᶠ Q in 𝓝 (0 : ℂ), ∀ i, Φ Q i * Φ 0 piv - Φ Q piv * Φ 0 i = Q ^ cuspIdx hp * Ψ Q i) ∧
      ∃ i, Ψ 0 i ≠ 0 := by
  classical
  have hf1 : 1 ≤ cuspIdx hp := one_le_cuspIdx hp
  have hf0 : (0 : ℤ) < cuspIdx hp := by exact_mod_cast hf1
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hx0 : ∀ i, (phi N σ (s i) : FC N) ≠ 0 := fun i => phi_ne_zero σ (hs0 i)
  have hθ0 : ∀ y : ↥(modularFunctionFieldBar N), y ≠ 0 → cuspExpHomW γ hw hΓ (phi N σ y) ≠ 0 := fun y hy =>
    (map_ne_zero_iff _ (cuspExpHomW γ hw hΓ).injective).mpr (phi_ne_zero σ hy)
  have he_idx : ∀ i, (cuspExpHomW γ hw hΓ (phi N σ (s i))).order = (cuspIdx hp : ℤ) * p.ord (s i) := fun i =>
    order_eq_cuspIdx_mul hp (hs0 i)
  have hA0ev : ∀ᶠ τ : ℍ in atImInfty, A₀ ≤ τ.im :=
    (UpperHalfPlane.atImInfty_mem {τ : ℍ | A₀ ≤ τ.im}).mpr ⟨A₀, fun τ h => h⟩

  have hsc := fun i => slash_chart_cuspExpW (phi N σ (s i) : FC N) (hx0 i) γ hw hΓ
  choose hne Φc hΦc hΦc0 hev using hsc
  have hΦc_ne : ∀ i, Φc i 0 ≠ 0 := fun i => by
    rw [hΦc0 i]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) (hne i)

  have hpunct : ∀ i, ∀ᶠ Q in 𝓝[≠] (0 : ℂ), Φ Q i = Q ^ (m + (cuspExpHomW γ hw hΓ (phi N σ (s i))).order) * Φc i Q := by
    intro i
    obtain ⟨A₁, hA₁⟩ := (UpperHalfPlane.atImInfty_mem _).mp (hev i)
    have h1 : ∀ᶠ Q in 𝓝[≠] (0 : ℂ), Q ≠ 0 → Φ Q i = Q ^ (m + (cuspExpHomW γ hw hΓ (phi N σ (s i))).order) * Φc i Q := by
      refine eventually_nhdsNE_of_forall_qParam hw (A := max A₀ A₁)
        (P := fun Q => Q ≠ 0 → Φ Q i = Q ^ (m + (cuspExpHomW γ hw hΓ (phi N σ (s i))).order) * Φc i Q) (fun τ hτ hq0 => ?_)
      have h2 := hA₁ τ ((le_max_right _ _).trans hτ)
      simp only [Set.mem_setOf_eq] at h2
      rw [hΦ τ ((le_max_left _ _).trans hτ) i, h2, ← mul_assoc, ← zpow_add₀ hq0]
    filter_upwards [h1, self_mem_nhdsWithin] with Q h hQ using h hQ
  have hbook := fun i => zpow_chart_exponent (G := Φc i) (hA i) (hΦc i) (hΦc_ne i) (hpunct i)
  have hm : m + (cuspExpHomW γ hw hΓ (phi N σ (s piv))).order = 0 := by
    have h0 := (hbook piv).2.1
    by_contra hne'
    rw [if_neg hne'] at h0
    exact hpiv h0
  have hmin : ∀ i, (cuspExpHomW γ hw hΓ (phi N σ (s piv))).order ≤ (cuspExpHomW γ hw hΓ (phi N σ (s i))).order := fun i => by
    have := (hbook i).1; omega
  have hΦ0 : ∀ i, Φ 0 i = if (cuspExpHomW γ hw hΓ (phi N σ (s i))).order = (cuspExpHomW γ hw hΓ (phi N σ (s piv))).order then
      (cuspExpHomW γ hw hΓ (phi N σ (s i))).leadingCoeff else 0 := by
    intro i
    rw [(hbook i).2.1, hΦc0 i, ← HahnSeries.leadingCoeff_eq]
    by_cases h : (cuspExpHomW γ hw hΓ (phi N σ (s i))).order = (cuspExpHomW γ hw hΓ (phi N σ (s piv))).order
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hΦ0piv : Φ 0 piv = (cuspExpHomW γ hw hΓ (phi N σ (s piv))).leadingCoeff := by
    rw [hΦ0 piv, if_pos rfl]

  have hordle : ∀ i, p.ord (s piv) ≤ p.ord (s i) := fun i =>
    le_of_mul_le_mul_left (by rw [← he_idx, ← he_idx]; exact hmin i) hf0
  have hordpiv : p.ord (s piv) = -(embDivisor N p) := ord_eq_neg_embDivisor_of_forall_le s hs p hordle
  obtain ⟨a, ha⟩ : ∃ a : Fin r → AlgebraicClosure ℚ, ∀ i, a i = p.evalAt (s i / s piv) := ⟨_, fun i => rfl⟩
  have hcv := fun i => centre_value hp s hs0 (piv := piv) (i := i) (hmin i)
  have hymem : ∀ i, s i / s piv ∈ p.toValuationSubring := fun i => (hcv i).1
  have hΦ0' : ∀ i, Φ 0 i = Φ 0 piv * σ (a i) := by
    intro i
    rw [ha i, (hcv i).2, hΦ0 i, hΦ0piv]
    split_ifs with h
    · rw [mul_div_cancel₀ _ (by rw [← hΦ0piv]; exact hpiv)]
    · rw [mul_zero]

  obtain ⟨v, hv⟩ : ∃ v : Fin r → ↥(modularFunctionFieldBar N),
      ∀ i, v i = s i / s piv - algebraMap (AlgebraicClosure ℚ) _ (a i) := ⟨_, fun i => rfl⟩
  have hθv : ∀ i, cuspExpHomW γ hw hΓ (phi N σ (v i)) = cuspExpHomW γ hw hΓ (phi N σ (s i / s piv)) - HahnSeries.C (σ (a i)) := by
    intro i; rw [hv i, map_sub, map_sub, phi_algebraMap, cuspExpHomW_algebraMap]
  have hvmem : ∀ i, v i ∈ p.toValuationSubring := fun i => by
    rw [hv i]; exact sub_mem (hymem i) (p.algebraMap_mem' (a i))
  have hvord : ∀ i, v i ≠ 0 → 1 ≤ p.ord (v i) := by
    intro i hvi
    have hnn : 0 ≤ (cuspExpHomW γ hw hΓ (phi N σ (v i))).order := (mem_place_cuspW_iff hp (v i)).mp (hvmem i)
    have hc0 : (cuspExpHomW γ hw hΓ (phi N σ (v i))).coeff 0 = 0 := by
      rw [hθv i, HahnSeries.coeff_sub, coeff_zero_cuspExp_eq hp (hymem i), HahnSeries.C_apply,
        HahnSeries.coeff_single, if_pos rfl, ← ha i, sub_self]
    have hpos := LaurentSeries.order_pos_of_coeff_zero' (hθ0 _ hvi) hnn hc0
    rw [order_eq_cuspIdx_mul hp hvi] at hpos
    by_contra hlt
    push_neg at hlt
    have : (cuspIdx hp : ℤ) * p.ord (v i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf0.le (by omega)
    omega

  obtain ⟨u, hu⟩ : ∃ u : Fin r → ↥(modularFunctionFieldBar N),
      ∀ i, u i = s i - algebraMap (AlgebraicClosure ℚ) _ (a i) * s piv := ⟨_, fun i => rfl⟩
  have hu_eq : ∀ i, u i = s piv * v i := by
    intro i; rw [hu i, hv i, mul_sub, mul_div_cancel₀ _ (hs0 piv)]; ring
  have hphiu : ∀ i, (phi N σ (u i) : FC N) = phi N σ (s i) - σ (a i) • phi N σ (s piv) := by
    intro i; rw [hu i, map_sub, map_mul, phi_algebraMap, Algebra.smul_def]

  have hMτ : ∀ i, ∀ᶠ τ : ℍ in atImInfty,
      Φ (Function.Periodic.qParam w (τ : ℂ)) i * Φ 0 piv - Φ (Function.Periodic.qParam w (τ : ℂ)) piv * Φ 0 i =
        Φ 0 piv * (Function.Periodic.qParam w (τ : ℂ) ^ m *
          realize N ((phi N σ (u i) : FC N) : LaurentSeries ℂ) (γ • τ)) := by
    intro i
    filter_upwards [realize_sub_smul_smul_eventually (phi N σ (s i) : FC N) (phi N σ (s piv)) (σ (a i)) γ, hA0ev]
      with τ h1 hτ
    rw [hΦ τ hτ i, hΦ τ hτ piv, hΦ0' i, hphiu i, h1]
    ring

  have hΨ : ∀ i, ∃ Ψi : ℂ → ℂ, AnalyticAt ℂ Ψi 0 ∧
      (∀ᶠ Q in 𝓝 (0 : ℂ), Φ Q i * Φ 0 piv - Φ Q piv * Φ 0 i = Q ^ cuspIdx hp * Ψi Q) ∧
      (v i ≠ 0 → p.ord (v i) = 1 → Ψi 0 ≠ 0) := by
    intro i
    have hMan : AnalyticAt ℂ (fun Q => Φ Q i * Φ 0 piv - Φ Q piv * Φ 0 i) 0 :=
      ((hA i).mul analyticAt_const).sub ((hA piv).mul analyticAt_const)
    by_cases hvi : v i = 0
    ·
      have hui : u i = 0 := by rw [hu_eq i, hvi, mul_zero]
      refine ⟨fun _ => 0, analyticAt_const, ?_, fun h => absurd hvi h⟩
      have hMτ0 : ∀ᶠ τ : ℍ in atImInfty,
          Φ (Function.Periodic.qParam w (τ : ℂ)) i * Φ 0 piv - Φ (Function.Periodic.qParam w (τ : ℂ)) piv * Φ 0 i = 0 := by
        filter_upwards [hMτ i] with τ h
        rw [h, hui, map_zero, ZeroMemClass.coe_zero, realize_zero', mul_zero, mul_zero]
      obtain ⟨A₁, hA₁⟩ := (UpperHalfPlane.atImInfty_mem _).mp hMτ0
      have heq := eventuallyEq_of_forall_qParam hw (F := fun Q => Φ Q i * Φ 0 piv - Φ Q piv * Φ 0 i)
        (G := fun _ => (0 : ℂ)) hMan.continuousAt continuousAt_const (A := A₁)
        (fun τ hτ => by have h := hA₁ τ hτ; simpa only [Set.mem_setOf_eq] using h)
      filter_upwards [heq] with Q hQ
      rw [hQ, mul_zero]
    · have hui : u i ≠ 0 := by rw [hu_eq i]; exact mul_ne_zero (hs0 piv) hvi
      have hxu : (phi N σ (u i) : FC N) ≠ 0 := phi_ne_zero σ hui
      obtain ⟨hneu, Φu, hΦu, hΦu0, hevu⟩ := slash_chart_cuspExpW (phi N σ (u i) : FC N) hxu γ hw hΓ
      have hΦu_ne : Φu 0 ≠ 0 := by rw [hΦu0]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) hneu
      have hk1 : 1 ≤ p.ord (v i) := hvord i hvi

      have hexp : m + (cuspExpHomW γ hw hΓ (phi N σ (u i))).order = (cuspIdx hp : ℤ) * p.ord (v i) := by
        rw [order_eq_cuspIdx_mul hp hui, hu_eq i, p.ord_mul (hs0 piv) hvi]
        have hm' : m = -((cuspIdx hp : ℤ) * p.ord (s piv)) := by rw [← he_idx piv]; omega
        rw [hm']; ring
      have hpm : ∀ᶠ Q in 𝓝[≠] (0 : ℂ), Φ Q i * Φ 0 piv - Φ Q piv * Φ 0 i =
          Q ^ ((cuspIdx hp : ℤ) * p.ord (v i)) * (Φ 0 piv * Φu Q) := by
        obtain ⟨A₁, hA₁⟩ := (UpperHalfPlane.atImInfty_mem _).mp ((hMτ i).and hevu)
        have h1 : ∀ᶠ Q in 𝓝[≠] (0 : ℂ), Q ≠ 0 → Φ Q i * Φ 0 piv - Φ Q piv * Φ 0 i =
            Q ^ ((cuspIdx hp : ℤ) * p.ord (v i)) * (Φ 0 piv * Φu Q) := by
          refine eventually_nhdsNE_of_forall_qParam hw (A := A₁)
            (P := fun Q => Q ≠ 0 → Φ Q i * Φ 0 piv - Φ Q piv * Φ 0 i =
              Q ^ ((cuspIdx hp : ℤ) * p.ord (v i)) * (Φ 0 piv * Φu Q)) (fun τ hτ hq0 => ?_)
          obtain ⟨h2, h3⟩ := hA₁ τ hτ
          rw [h2, h3, ← hexp, zpow_add₀ hq0]; ring
        filter_upwards [h1, self_mem_nhdsWithin] with Q h hQ using h hQ
      have hbk := zpow_chart_exponent (G := fun Q => Φ 0 piv * Φu Q) hMan (analyticAt_const.mul hΦu)
        (mul_ne_zero hpiv hΦu_ne) hpm
      obtain ⟨n, hn⟩ : ∃ n : ℕ, p.ord (v i) = n + 1 := ⟨(p.ord (v i) - 1).toNat, by omega⟩
      refine ⟨fun Q => Q ^ (cuspIdx hp * n) * (Φ 0 piv * Φu Q), ?_, ?_, ?_⟩
      · first
          | exact (analyticAt_id.pow (cuspIdx hp * n)).mul (analyticAt_const.mul hΦu)
          | fun_prop
      · filter_upwards [hbk.2.2.1] with Q hQ
        rw [hQ, hn]
        have : ((cuspIdx hp : ℤ) * ((n : ℤ) + 1)).toNat = cuspIdx hp + cuspIdx hp * n := by
          rw [show ((cuspIdx hp : ℤ) * ((n : ℤ) + 1)) = ((cuspIdx hp + cuspIdx hp * n : ℕ) : ℤ) by push_cast; ring,
            Int.toNat_natCast]
        rw [this, pow_add]; ring
      · intro _ hk'
        have hn0 : n = 0 := by omega
        subst hn0
        simpa using mul_ne_zero hpiv hΦu_ne
  choose Ψ hΨa hΨe hΨ0 using hΨ
  refine ⟨fun Q i => Ψ i Q, hΨa, Filter.eventually_all.mpr hΨe, ?_⟩

  obtain ⟨g, hgL, hg0, hgord⟩ := hRR
  have hgspan : g ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by rw [hs.2]; exact hgL
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hgspan
  have hy_eq : ∀ i, s i / s piv = v i + algebraMap (AlgebraicClosure ℚ) _ (a i) := fun i => by
    rw [hv i]; ring
  have hsum : g / s piv - algebraMap (AlgebraicClosure ℚ) _ (∑ i, b i * a i) = ∑ i, b i • v i := by
    rw [← hb, Finset.sum_div, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_div_assoc, hy_eq i, smul_add]
    simp only [Algebra.smul_def, map_mul]
    ring
  have hιg : (cuspExpHomW γ hw hΓ (phi N σ (g / s piv))).order = cuspIdx hp := by
    rw [order_eq_cuspIdx_mul hp (div_ne_zero hg0 (hs0 piv)), div_eq_mul_inv,
      p.ord_mul hg0 (inv_ne_zero (hs0 piv)), p.ord_inv, hordpiv]
    have : p.ord g + - -(embDivisor N) p = 1 := by rw [neg_neg]; exact hgord
    rw [this, mul_one]
  have hex : ∃ i, v i ≠ 0 ∧ p.ord (v i) = 1 := by
    by_contra hcon
    push_neg at hcon
    have h2 : ∀ i, v i ≠ 0 → 2 ≤ p.ord (v i) := fun i hi => by
      have := hvord i hi; have := hcon i hi; omega
    have hcoef : ∀ i, (cuspExpHomW γ hw hΓ (phi N σ (b i • v i))).coeff (cuspIdx hp : ℤ) = 0 := by
      intro i
      by_cases hvi : v i = 0
      · rw [hvi, smul_zero, map_zero, map_zero]; rfl
      · rw [Algebra.smul_def, map_mul, map_mul, phi_algebraMap, cuspExpHomW_algebraMap, HahnSeries.C_mul_eq_smul,
          HahnSeries.coeff_smul, smul_eq_mul]
        apply mul_eq_zero_of_right
        apply HahnSeries.coeff_eq_zero_of_lt_order
        rw [order_eq_cuspIdx_mul hp hvi]
        nlinarith [h2 i hvi, hf0]
    have hL := congrArg (fun z : ↥(modularFunctionFieldBar N) => (cuspExpHomW γ hw hΓ (phi N σ z)).coeff (cuspIdx hp : ℤ)) hsum
    beta_reduce at hL
    rw [map_sub, map_sub, HahnSeries.coeff_sub] at hL
    have hc : (cuspExpHomW γ hw hΓ (phi N σ (algebraMap (AlgebraicClosure ℚ) _ (∑ i, b i * a i)))).coeff (cuspIdx hp : ℤ) = 0 := by
      rw [phi_algebraMap, cuspExpHomW_algebraMap, HahnSeries.C_apply, HahnSeries.coeff_single, if_neg]
      exact_mod_cast (show cuspIdx hp ≠ 0 by omega)
    rw [hc, sub_zero, map_sum (phi N σ), map_sum (cuspExpHomW γ hw hΓ), HahnSeries.coeff_sum,
      Finset.sum_eq_zero (fun i _ => hcoef i)] at hL
    have hlead : (cuspExpHomW γ hw hΓ (phi N σ (g / s piv))).coeff (cuspIdx hp : ℤ) ≠ 0 := by
      rw [← hιg]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) (hθ0 _ (div_ne_zero hg0 (hs0 piv)))
    exact hlead hL
  obtain ⟨i, hvi, hvi1⟩ := hex
  exact ⟨i, hΨ0 i hvi hvi1⟩

end Main

end CuspFactor

section CuspRegularity

variable {N : ℕ} [NeZero N]

theorem tendsto_im_atImInfty' : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := by
  rw [UpperHalfPlane.atImInfty]; exact Filter.tendsto_comap

theorem eq_zero_of_tendsto_exp_mul_im {c L : ℝ} (hL : 0 < L)
    (h : Tendsto (fun τ : ℍ => Real.exp (c * τ.im)) atImInfty (𝓝 L)) : c = 0 := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · exfalso
    have h1 : Tendsto (fun τ : ℍ => (-c) * τ.im) atImInfty atTop :=
      tendsto_im_atImInfty'.const_mul_atTop (neg_pos.mpr hc)
    have h2 : Tendsto (fun τ : ℍ => c * τ.im) atImInfty atBot := by
      have := Filter.tendsto_neg_atTop_atBot.comp h1
      refine this.congr fun τ => ?_
      simp only [Function.comp_apply]; ring
    have h0 : Tendsto (fun τ : ℍ => Real.exp (c * τ.im)) atImInfty (𝓝 0) := Real.tendsto_exp_atBot.comp h2
    have := tendsto_nhds_unique h h0
    linarith
  · exact hc
  · exfalso
    have h1 : Tendsto (fun τ : ℍ => Real.exp (c * τ.im)) atImInfty atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_im_atImInfty'.const_mul_atTop hc)
    exact not_tendsto_nhds_of_tendsto_atTop h1 L h

theorem norm_qParam_zpow (w : ℝ) (τ : ℍ) (a : ℤ) :
    ‖Function.Periodic.qParam w (τ : ℂ) ^ a‖ = Real.exp ((-2 * Real.pi * a / w) * τ.im) := by
  rw [norm_zpow, Function.Periodic.norm_qParam, UpperHalfPlane.coe_im, ← Real.rpow_intCast, ← Real.exp_mul]
  congr 1; ring

theorem order_mul_width_eq (x : FC N) (hx : x ≠ 0) (γ : SL(2, ℤ)) {w w' : ℝ} (hw : 0 < w)
    (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) (hw' : 0 < w') (hΓ' : w' ∈ (conjGamma0 N γ).strictPeriods) :
    ((cuspExpHomW γ hw hΓ x).order : ℝ) * w' = ((cuspExpHomW γ hw' hΓ' x).order : ℝ) * w := by
  obtain ⟨h0, Φ, hΦ, hΦ0, hev⟩ := slash_chart_cuspExpW x hx γ hw hΓ
  obtain ⟨h0', Ψ, hΨ, hΨ0, hev'⟩ := slash_chart_cuspExpW x hx γ hw' hΓ'
  set a : ℤ := (cuspExpHomW γ hw hΓ x).order with ha
  set b : ℤ := (cuspExpHomW γ hw' hΓ' x).order with hb
  have hΦne : Φ 0 ≠ 0 := by rw [hΦ0]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) h0
  have hΨne : Ψ 0 ≠ 0 := by rw [hΨ0]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) h0'
  have hΦt : Tendsto (fun τ : ℍ => ‖Φ (Function.Periodic.qParam w (τ : ℂ))‖) atImInfty (𝓝 ‖Φ 0‖) :=
    (hΦ.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty hw)).norm
  have hΨt : Tendsto (fun τ : ℍ => ‖Ψ (Function.Periodic.qParam w' (τ : ℂ))‖) atImInfty (𝓝 ‖Ψ 0‖) :=
    (hΨ.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty hw')).norm
  set c : ℝ := (-2 * Real.pi * a / w) - (-2 * Real.pi * b / w') with hc
  have hev2 : ∀ᶠ τ : ℍ in atImInfty, Real.exp (c * τ.im) =
      ‖Ψ (Function.Periodic.qParam w' (τ : ℂ))‖ / ‖Φ (Function.Periodic.qParam w (τ : ℂ))‖ := by
    filter_upwards [hev, hev', hΦt.eventually_ne (norm_ne_zero_iff.mpr hΦne)] with τ h1 h2 hne
    have heq : Function.Periodic.qParam w (τ : ℂ) ^ a * Φ (Function.Periodic.qParam w (τ : ℂ)) =
        Function.Periodic.qParam w' (τ : ℂ) ^ b * Ψ (Function.Periodic.qParam w' (τ : ℂ)) := by rw [← h1, ← h2]
    have hn := congrArg (fun z : ℂ => ‖z‖) heq
    simp only [norm_mul, norm_qParam_zpow] at hn
    rw [eq_div_iff hne, hc, sub_mul, Real.exp_sub, div_mul_eq_mul_div, div_eq_iff (Real.exp_pos _).ne', hn, mul_comm]
  have hlim : Tendsto (fun τ : ℍ => Real.exp (c * τ.im)) atImInfty (𝓝 (‖Ψ 0‖ / ‖Φ 0‖)) :=
    (hΨt.div hΦt (norm_ne_zero_iff.mpr hΦne)).congr' (hev2.mono fun τ h => h.symm)
  have hc0 := eq_zero_of_tendsto_exp_mul_im (div_pos (norm_pos_iff.mpr hΨne) (norm_pos_iff.mpr hΦne)) hlim
  have h4 : (-2 * Real.pi) * ((a : ℝ) / w - b / w') = 0 := by rw [← hc0, hc]; ring
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exfalso; linarith [Real.pi_pos]
  · rw [sub_eq_zero, div_eq_div_iff hw.ne' hw'.ne'] at h5
    linarith [h5]

theorem order_nonneg_iff_width (x : FC N) (γ : SL(2, ℤ)) {w w' : ℝ} (hw : 0 < w)
    (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) (hw' : 0 < w') (hΓ' : w' ∈ (conjGamma0 N γ).strictPeriods) :
    0 ≤ (cuspExpHomW γ hw hΓ x).order ↔ 0 ≤ (cuspExpHomW γ hw' hΓ' x).order := by
  by_cases hx : x = 0
  · simp [hx]
  have h := order_mul_width_eq x hx γ hw hΓ hw' hΓ'
  constructor <;> intro h1
  · have h2 : (0 : ℝ) ≤ ((cuspExpHomW γ hw hΓ x).order : ℝ) * w' := mul_nonneg (by exact_mod_cast h1) hw'.le
    rw [h] at h2
    exact_mod_cast (mul_nonneg_iff_of_pos_right hw).mp h2
  · have h2 : (0 : ℝ) ≤ ((cuspExpHomW γ hw' hΓ' x).order : ℝ) * w := mul_nonneg (by exact_mod_cast h1) hw.le
    rw [← h] at h2
    exact_mod_cast (mul_nonneg_iff_of_pos_right hw').mp h2

theorem discriminant_mul_presNum_jC :
    ((CuspForm.discriminant : CuspForm Γ1 12) : ℍ → ℂ) * (presNum (jC N) : ℍ → ℂ) =
      (E4cube : ℍ → ℂ) * (presDen (jC N) : ℍ → ℂ) := by
  classical
  have hp := isPres_pres (jC N)
  set Δf : CuspForm Γ1 12 := CuspForm.discriminant with hΔf
  have hcoeΔ : (Δf : ℍ → ℂ) = ModularForm.discriminant := rfl
  have hjq : ((jC N : FC N) : LaurentSeries ℂ) =
      ((qExpansion 1 (E4cube : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion 1 (Δf : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    show coeffEmb ℂ jq = _
    rw [coeffEmb_jq_eq_jqModC', ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, qExpansion_E4cube, hcoeΔ]
  have hΔ0 : ((qExpansion 1 (Δf : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
    intro h0
    exact ModularForm.discriminant_ne_zero UpperHalfPlane.I
      (coe_eq_zero_of_qExpansion_eq_zero Δf one_pos one_mem_strictPeriods_range h0 UpperHalfPlane.I)
  have hformal : ((qExpansion 1 (presNum (jC N) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) *
      ((qExpansion 1 (Δf : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (E4cube : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) *
        ((qExpansion 1 (presDen (jC N) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [← hp.2, hjq]
    field_simp
  apply mul_eq_mul_of_qExpansion_eq
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  rw [UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_levelOne Δf) (analyticAt_cuspFunction_gamma0 (presNum (jC N))),
    UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_levelOne E4cube) (analyticAt_cuspFunction_gamma0 (presDen (jC N))),
    map_mul, map_mul, mul_comm, hformal]

theorem levelOne_apply_smul {a : ℤ} {F₁ : Type*} [FunLike F₁ ℍ ℂ] [SlashInvariantFormClass F₁ Γ1 a] (F : F₁)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    (F : ℍ → ℂ) (γ • τ) = (F : ℍ → ℂ) τ * denom (γ : GL (Fin 2) ℝ) (τ : ℂ) ^ a := by
  have h := congrFun (slash_levelOne F γ) τ
  rw [ModularForm.SL_slash_apply] at h
  have hd : denom (γ : GL (Fin 2) ℝ) (τ : ℂ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hcoe : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ) =
      denom (γ : GL (Fin 2) ℝ) (τ : ℂ) := rfl
  rw [hcoe] at h
  rw [← h, mul_assoc, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, mul_one]

theorem realize_jC_smul_eventually (γ : SL(2, ℤ)) :
    ∀ᶠ τ : ℍ in atImInfty, realize N ((jC N : FC N) : LaurentSeries ℂ) (γ • τ) =
      (E4cube : ℍ → ℂ) τ / ModularForm.discriminant τ := by
  have hp := isPres_pres (jC N)
  filter_upwards [eventually_apply_smul_ne_zero (presDen (jC N)) hp.1 γ] with τ hH
  rw [ModularCurve.realize_eq_div N (presNum (jC N)) (presDen (jC N)) _ hp.2 _ hH]
  have hfun := congrFun (discriminant_mul_presNum_jC (N := N)) (γ • τ)
  simp only [Pi.mul_apply] at hfun
  have hΔγ : ((CuspForm.discriminant : CuspForm Γ1 12) : ℍ → ℂ) (γ • τ) ≠ 0 := ModularForm.discriminant_ne_zero _
  have hΔ : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero _
  rw [div_eq_div_iff hH hΔ]

  have hE := levelOne_apply_smul E4cube γ τ
  have hD := levelOne_apply_smul (CuspForm.discriminant : CuspForm Γ1 12) γ τ
  have hcoeΔ : ((CuspForm.discriminant : CuspForm Γ1 12) : ℍ → ℂ) = ModularForm.discriminant := rfl
  rw [hcoeΔ] at hD hfun hΔγ

  have hd : denom (γ : GL (Fin 2) ℝ) (τ : ℂ) ^ (12 : ℤ) ≠ 0 := zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _)
  rw [hE, hD] at hfun
  have : (presNum (jC N) : ℍ → ℂ) (γ • τ) * ModularForm.discriminant τ * denom (γ : GL (Fin 2) ℝ) (τ : ℂ) ^ (12 : ℤ) =
      (E4cube : ℍ → ℂ) τ * (presDen (jC N) : ℍ → ℂ) (γ • τ) * denom (γ : GL (Fin 2) ℝ) (τ : ℂ) ^ (12 : ℤ) := by
    linear_combination hfun
  exact mul_right_cancel₀ hd this

theorem tendsto_E4cube_atImInfty : Tendsto (fun τ : ℍ => (E4cube : ℍ → ℂ) τ) atImInfty (𝓝 1) := by
  have hR := one_mem_strictPeriods_range
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E₄) hR
  have han := analyticAt_cuspFunction_levelOne ModularForm.E₄
  have hE : Tendsto (fun τ : ℍ => (ModularForm.E₄ : ℍ → ℂ) τ) atImInfty (𝓝 (cuspFunction 1 (ModularForm.E₄ : ℍ → ℂ) 0)) := by
    have h1 := han.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)
    refine h1.congr fun τ => ?_
    simp only [Function.comp_apply]
    exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero hper
  have hval : cuspFunction 1 (ModularForm.E₄ : ℍ → ℂ) 0 = 1 := by
    have h := UpperHalfPlane.qExpansion_coeff (ModularForm.E₄ : ℍ → ℂ) (h := 1) 0
    simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedDeriv_zero] at h
    rw [← h]
    exact EisensteinSeries.E_qExpansion_coeff_zero _ (by decide)
  rw [hval] at hE
  have h3 := hE.pow 3
  simp only [one_pow] at h3
  refine h3.congr fun τ => ?_
  rw [coe_E4cube]; rfl

theorem order_cuspExpHomW_jC_eq (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) :
    ((cuspExpHomW γ hw hΓ (jC N)).order : ℝ) = -w := by
  have hj0 : (jC N : FC N) ≠ 0 := by
    intro h0
    have := order_cuspExpHomW_jC_neg (N := N) γ hw hΓ
    rw [h0, map_zero, HahnSeries.order_zero] at this
    exact lt_irrefl _ this
  obtain ⟨h0, Φ, hΦ, hΦ0, hev⟩ := slash_chart_cuspExpW (jC N) hj0 γ hw hΓ
  set a : ℤ := (cuspExpHomW γ hw hΓ (jC N)).order with ha
  have hΦne : Φ 0 ≠ 0 := by rw [hΦ0]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) h0
  have hΦt : Tendsto (fun τ : ℍ => ‖Φ (Function.Periodic.qParam w (τ : ℂ))‖) atImInfty (𝓝 ‖Φ 0‖) :=
    (hΦ.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty hw)).norm
  have hPt := ModularForm.discriminant_bounded_factor
  have hEt := tendsto_E4cube_atImInfty
  set P : ℍ → ℂ := fun τ => ∏' (n : ℕ), (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24 with hP
  set c : ℝ := (-2 * Real.pi * a / w) + (-2 * Real.pi * (1 : ℤ) / 1) with hc

  have hev2 : ∀ᶠ τ : ℍ in atImInfty, Real.exp (c * τ.im) =
      ‖(E4cube : ℍ → ℂ) τ‖ / (‖Φ (Function.Periodic.qParam w (τ : ℂ))‖ * ‖P τ‖) := by
    filter_upwards [hev, realize_jC_smul_eventually (N := N) γ, hΦt.eventually_ne (norm_ne_zero_iff.mpr hΦne),
      hPt.eventually_ne one_ne_zero] with τ h1 h2 hne hPne
    have hΔ : ModularForm.discriminant τ = Function.Periodic.qParam 1 (τ : ℂ) * P τ := ModularForm.discriminant_eq_q_prod τ
    have hΔ0 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
    have heq : Function.Periodic.qParam w (τ : ℂ) ^ a * Φ (Function.Periodic.qParam w (τ : ℂ)) *
        (Function.Periodic.qParam 1 (τ : ℂ) ^ (1 : ℤ) * P τ) = (E4cube : ℍ → ℂ) τ := by
      rw [zpow_one, ← hΔ, ← h1, h2, div_mul_cancel₀ _ hΔ0]
    have hn := congrArg (fun z : ℂ => ‖z‖) heq
    simp only [norm_mul, norm_qParam_zpow] at hn
    have hPn : ‖P τ‖ ≠ 0 := norm_ne_zero_iff.mpr hPne
    rw [eq_div_iff (mul_ne_zero hne hPn), hc, add_mul, Real.exp_add, ← hn]
    ring
  have hlim : Tendsto (fun τ : ℍ => Real.exp (c * τ.im)) atImInfty (𝓝 (‖(1 : ℂ)‖ / (‖Φ 0‖ * ‖(1 : ℂ)‖))) :=
    (hEt.norm.div (hΦt.mul hPt.norm) (mul_ne_zero (norm_ne_zero_iff.mpr hΦne) (by simp))).congr'
      (hev2.mono fun τ h => h.symm)
  have hc0 := eq_zero_of_tendsto_exp_mul_im (by simpa using norm_pos_iff.mpr hΦne) hlim
  have h4 : (-2 * Real.pi) * ((a : ℝ) / w + 1) = 0 := by rw [← hc0, hc]; push_cast; ring
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exfalso; linarith [Real.pi_pos]
  · field_simp at h5
    linarith [h5]

theorem mapGL_real_injective : Function.Injective (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) → GL (Fin 2) ℝ) := by
  intro a b h
  ext i j
  have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simpa [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.map_apply_coe] using this

theorem conj_T_zpow_mem_of_intCast_mem_strictPeriods (γ : SL(2, ℤ)) (n : ℤ)
    (h : (n : ℝ) ∈ (conjGamma0 N γ).strictPeriods) : γ * ModularGroup.T ^ n * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  rw [Subgroup.mem_strictPeriods_iff, ← mapGL_T_zpow_int] at h
  have h1 : (ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹)⁻¹ • (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ n) : GL (Fin 2) ℝ) ∈
      (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp h
  rw [← map_inv, inv_inv, ConjAct.toConjAct_smul] at h1
  obtain ⟨δ, hδ, hδeq⟩ := Subgroup.mem_map.mp h1
  have hc : (γ : GL (Fin 2) ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := rfl
  rw [hc, ← map_inv, ← map_mul, ← map_mul] at hδeq
  have := mapGL_real_injective hδeq
  rw [← this]; exact hδ

theorem strictWidthInfty_eq_cuspWidth (γ : SL(2, ℤ)) :
    Subgroup.strictWidthInfty (conjGamma0 N γ) =
      (ModularCurve.CuspSpace.cuspWidth (ModularCurve.CuspSpace.mk N
        (Matrix.SpecialLinearGroup.mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ))) : ℝ) := by
  have hN : N ≠ 0 := NeZero.ne N
  set W : ℕ := ModularCurve.CuspSpace.cuspWidth (ModularCurve.CuspSpace.mk N
        (Matrix.SpecialLinearGroup.mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ))) with hW
  have hpos : 0 < Subgroup.strictWidthInfty (conjGamma0 N γ) := strictWidthInfty_conjGamma0_pos γ
  have hWpos : 0 < W := ModularCurve.CuspSpace.cuspWidth_pos hN _

  have hWmem : ((W : ℤ) : ℝ) ∈ (conjGamma0 N γ).strictPeriods :=
    intCast_mem_strictPeriods_conjGamma0 γ W
      ((ModularCurve.CuspSpace.conj_T_zpow_mem_Gamma0_iff hN γ W).mpr (dvd_refl _))
  rw [Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty, AddSubgroup.mem_zmultiples_iff] at hWmem
  obtain ⟨k, hk⟩ := hWmem
  rw [zsmul_eq_mul] at hk

  have hhmem : Subgroup.strictWidthInfty (conjGamma0 N γ) ∈ (conjGamma0 N γ).strictPeriods :=
    Subgroup.strictWidthInfty_mem_strictPeriods _
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℝ) = Subgroup.strictWidthInfty (conjGamma0 N γ) := by
    have := strictPeriods_conjGamma0_subset γ hhmem
    rw [SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff] at this
    obtain ⟨n, hn⟩ := this
    exact ⟨n, by rw [← hn, zsmul_eq_mul, mul_one]⟩
  have hnmem : (n : ℝ) ∈ (conjGamma0 N γ).strictPeriods := by rw [hn]; exact hhmem
  have hdvd : (W : ℤ) ∣ n := (ModularCurve.CuspSpace.conj_T_zpow_mem_Gamma0_iff hN γ n).mp
      (conj_T_zpow_mem_of_intCast_mem_strictPeriods γ n hnmem)
  obtain ⟨j, hj⟩ := hdvd

  have hn0 : (0 : ℝ) < n := by rw [hn]; exact hpos
  have hn0' : 0 < n := by exact_mod_cast hn0
  have hkR : ((W : ℤ) : ℝ) = k * n := by rw [← hn] at hk; linarith [hk]
  have hkZ : (W : ℤ) = k * n := by exact_mod_cast hkR
  have hW0 : (0 : ℤ) < W := by exact_mod_cast hWpos
  have hkj : k * j = 1 := by
    have : (W : ℤ) = k * j * W := by
      conv_lhs => rw [hkZ, hj]
      ring
    have h2 : (1 - k * j) * (W : ℤ) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · omega
  have hk1 : k = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hkj with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hkZ
      linarith
  rw [hk1, one_mul] at hkZ
  rw [← hn, ← hkZ, Int.cast_natCast]

noncomputable abbrev thetaN (γ : SL(2, ℤ)) : FC N →+* LaurentSeries ℂ :=
  cuspExpHomW γ (natCast_pos_of_neZero N) (natCast_mem_strictPeriods_conjGamma0 N γ)

theorem exp_coeff_eq_of_eventually_eq {A B : ℝ} {F G : ℍ → ℝ} {LF LG : ℝ} (hLF : 0 < LF) (hLG : 0 < LG)
    (hF : Tendsto F atImInfty (𝓝 LF)) (hG : Tendsto G atImInfty (𝓝 LG))
    (h : ∀ᶠ τ : ℍ in atImInfty, Real.exp (A * τ.im) * F τ = Real.exp (B * τ.im) * G τ) : A = B := by
  have hev2 : ∀ᶠ τ : ℍ in atImInfty, Real.exp ((A - B) * τ.im) = G τ / F τ := by
    filter_upwards [h, hF.eventually_ne hLF.ne'] with τ h1 hne
    rw [eq_div_iff hne, sub_mul, Real.exp_sub, div_mul_eq_mul_div, div_eq_iff (Real.exp_pos _).ne', h1, mul_comm]
  have hlim : Tendsto (fun τ : ℍ => Real.exp ((A - B) * τ.im)) atImInfty (𝓝 (LG / LF)) :=
    (hG.div hF hLF.ne').congr' (hev2.mono fun τ h => h.symm)
  have := eq_zero_of_tendsto_exp_mul_im (div_pos hLG hLF) hlim
  linarith

theorem gamma0_apply_smul {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    (f : ℍ → ℂ) (δ • z) = (f : ℍ → ℂ) z * denom (δ : GL (Fin 2) ℝ) (z : ℂ) ^ k := by
  have h0 : (f : ℍ → ℂ) ∣[k] δ = (f : ℍ → ℂ) := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantForm.slash_action_eqn f _ ⟨δ, hδ, rfl⟩
  have h := congrFun h0 z
  rw [ModularForm.SL_slash_apply] at h
  have hd : denom (δ : GL (Fin 2) ℝ) (z : ℂ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hcoe : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) δ)) (z : ℂ) =
      denom (δ : GL (Fin 2) ℝ) (z : ℂ) := rfl
  rw [hcoe] at h
  rw [← h, mul_assoc, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, mul_one]

theorem realize_gamma0_smul (x : FC N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ)
    (hz : (presDen x : ℍ → ℂ) z ≠ 0) :
    realize N (x : LaurentSeries ℂ) (δ • z) = realize N (x : LaurentSeries ℂ) z := by
  have hp := isPres_pres x
  have hd : denom (δ : GL (Fin 2) ℝ) (z : ℂ) ^ (presWt x) ≠ 0 := zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _)
  have hz' : (presDen x : ℍ → ℂ) (δ • z) ≠ 0 := by
    rw [gamma0_apply_smul (presDen x) hδ z]; exact mul_ne_zero hz hd
  rw [ModularCurve.realize_eq_div N (presNum x) (presDen x) _ hp.2 _ hz',
    ModularCurve.realize_eq_div N (presNum x) (presDen x) _ hp.2 _ hz,
    gamma0_apply_smul (presNum x) hδ z, gamma0_apply_smul (presDen x) hδ z, mul_div_mul_right _ _ hd]

theorem order_thetaN_gamma0_mul {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma0 N) (γ : SL(2, ℤ)) (x : FC N) (hx : x ≠ 0) :
    (thetaN (δ * γ) x).order = (thetaN γ x).order := by
  have hw : (0 : ℝ) < N := natCast_pos_of_neZero N
  obtain ⟨h1, Φ₁, hΦ₁, hΦ₁0, hev₁⟩ := slash_chart_cuspExpW x hx (δ * γ) hw (natCast_mem_strictPeriods_conjGamma0 N (δ * γ))
  obtain ⟨h2, Φ₂, hΦ₂, hΦ₂0, hev₂⟩ := slash_chart_cuspExpW x hx γ hw (natCast_mem_strictPeriods_conjGamma0 N γ)
  have hΦ₁ne : Φ₁ 0 ≠ 0 := by rw [hΦ₁0]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) h1
  have hΦ₂ne : Φ₂ 0 ≠ 0 := by rw [hΦ₂0]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) h2
  have hq := UpperHalfPlane.qParam_tendsto_atImInfty hw
  have key := exp_coeff_eq_of_eventually_eq (norm_pos_iff.mpr hΦ₁ne) (norm_pos_iff.mpr hΦ₂ne)
    ((hΦ₁.continuousAt.tendsto.comp hq).norm) ((hΦ₂.continuousAt.tendsto.comp hq).norm)
    (A := -2 * Real.pi * (thetaN (δ * γ) x).order / N) (B := -2 * Real.pi * (thetaN γ x).order / N) ?_
  · have hN0 : (N : ℝ) ≠ 0 := hw.ne'
    have h4 : (-2 * Real.pi / N) * (((thetaN (δ * γ) x).order : ℝ) - (thetaN γ x).order) = 0 := by
      have := sub_eq_zero.mpr key
      rw [← this]; ring
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hN0)
    · exact_mod_cast (sub_eq_zero.mp h5)
  · filter_upwards [hev₁, hev₂, eventually_apply_smul_ne_zero (presDen x) (isPres_pres x).1 γ] with τ e1 e2 hz
    have heq : realize N (x : LaurentSeries ℂ) ((δ * γ) • τ) = realize N (x : LaurentSeries ℂ) (γ • τ) := by
      rw [mul_smul]; exact realize_gamma0_smul x hδ _ hz
    rw [e1, e2] at heq
    have hn := congrArg (fun z : ℂ => ‖z‖) heq
    simp only [norm_mul, norm_qParam_zpow] at hn
    exact hn

theorem im_smul_of_apply_one_zero_eq_zero (M : SL(2, ℤ)) (hM : M 1 0 = 0) (τ : ℍ) : (M • τ).im = τ.im := by
  obtain ⟨n, -, hact⟩ := exists_eq_T_zpow_of_apply_one_zero_eq_zero M hM
  have h := congrArg Complex.im (hact τ)
  simp only [Complex.add_im, Complex.intCast_im, add_zero, UpperHalfPlane.coe_im] at h
  exact h

theorem tendsto_smul_atImInfty (M : SL(2, ℤ)) (hM : M 1 0 = 0) :
    Tendsto (fun τ : ℍ => M • τ) atImInfty atImInfty := by
  rw [UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]
  have : UpperHalfPlane.im ∘ (fun τ : ℍ => M • τ) = UpperHalfPlane.im := by
    funext τ; exact im_smul_of_apply_one_zero_eq_zero M hM τ
  rw [this]
  exact Filter.tendsto_comap

theorem order_thetaN_mul_upper (γ M : SL(2, ℤ)) (hM : M 1 0 = 0) (x : FC N) (hx : x ≠ 0) :
    (thetaN (γ * M) x).order = (thetaN γ x).order := by
  have hw : (0 : ℝ) < N := natCast_pos_of_neZero N
  obtain ⟨h1, Φ₁, hΦ₁, hΦ₁0, hev₁⟩ := slash_chart_cuspExpW x hx (γ * M) hw (natCast_mem_strictPeriods_conjGamma0 N (γ * M))
  obtain ⟨h2, Φ₂, hΦ₂, hΦ₂0, hev₂⟩ := slash_chart_cuspExpW x hx γ hw (natCast_mem_strictPeriods_conjGamma0 N γ)
  have hΦ₁ne : Φ₁ 0 ≠ 0 := by rw [hΦ₁0]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) h1
  have hΦ₂ne : Φ₂ 0 ≠ 0 := by rw [hΦ₂0]; exact (HahnSeries.coeff_order_eq_zero.not.mpr) h2
  have hMt := tendsto_smul_atImInfty M hM
  have hq := UpperHalfPlane.qParam_tendsto_atImInfty hw
  have hq' : Tendsto (fun τ : ℍ => Function.Periodic.qParam N ((M • τ : ℍ) : ℂ)) atImInfty (𝓝 0) := hq.comp hMt
  have key := exp_coeff_eq_of_eventually_eq (norm_pos_iff.mpr hΦ₁ne) (norm_pos_iff.mpr hΦ₂ne)
    ((hΦ₁.continuousAt.tendsto.comp hq).norm) ((hΦ₂.continuousAt.tendsto.comp hq').norm)
    (A := -2 * Real.pi * (thetaN (γ * M) x).order / N) (B := -2 * Real.pi * (thetaN γ x).order / N) ?_
  · have hN0 : (N : ℝ) ≠ 0 := hw.ne'
    have h4 : (-2 * Real.pi / N) * (((thetaN (γ * M) x).order : ℝ) - (thetaN γ x).order) = 0 := by
      have := sub_eq_zero.mpr key
      rw [← this]; ring
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd h5 (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hN0)
    · exact_mod_cast (sub_eq_zero.mp h5)
  · filter_upwards [hev₁, hMt.eventually hev₂] with τ e1 e2
    have heq : realize N (x : LaurentSeries ℂ) ((γ * M) • τ) = realize N (x : LaurentSeries ℂ) (γ • (M • τ)) := by
      rw [mul_smul]
    rw [e1, e2] at heq
    have hn := congrArg (fun z : ℂ => ‖z‖) heq
    simp only [norm_mul, norm_qParam_zpow, im_smul_of_apply_one_zero_eq_zero M hM] at hn
    exact hn

noncomputable def cuspPl (σ : AlgebraicClosure ℚ →+* ℂ) (γ : SL(2, ℤ)) :
    Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
  (exists_place_cuspW (N := N) γ (strictWidthInfty_conjGamma0_pos γ)
    (Subgroup.strictWidthInfty_mem_strictPeriods (conjGamma0 N γ)) σ).choose

theorem cuspPl_spec (σ : AlgebraicClosure ℚ →+* ℂ) (γ : SL(2, ℤ)) :
    (cuspPl (N := N) σ γ).toValuationSubring = (qadicSubring ℂ).comap
      (cuspExpBW γ (strictWidthInfty_conjGamma0_pos γ) (Subgroup.strictWidthInfty_mem_strictPeriods (conjGamma0 N γ)) σ) :=
  (exists_place_cuspW (N := N) γ (strictWidthInfty_conjGamma0_pos γ)
    (Subgroup.strictWidthInfty_mem_strictPeriods (conjGamma0 N γ)) σ).choose_spec

theorem mem_cuspPl_iff (σ : AlgebraicClosure ℚ →+* ℂ) (γ : SL(2, ℤ)) (y : ↥(modularFunctionFieldBar N)) :
    y ∈ (cuspPl σ γ).toValuationSubring ↔ 0 ≤ (thetaN γ (phi N σ y)).order := by
  rw [mem_place_cuspW_iff (cuspPl_spec σ γ)]
  exact order_nonneg_iff_width _ γ _ _ _ _

theorem cuspPl_rel (σ : AlgebraicClosure ℚ →+* ℂ) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma0 N)
    (γ M : SL(2, ℤ)) (hM : M 1 0 = 0) : cuspPl (N := N) σ (δ * γ * M) = cuspPl σ γ := by
  apply Place.ext
  ext y
  rw [mem_cuspPl_iff, mem_cuspPl_iff]
  by_cases hy : y = 0
  · simp [hy]
  have hx : (phi N σ y : FC N) ≠ 0 := phi_ne_zero σ hy
  rw [order_thetaN_mul_upper (δ * γ) M hM _ hx, order_thetaN_gamma0_mul hδ γ _ hx]

theorem exists_sigma_of_isCusp (w : Place ℂ (FC N)) (hc : IsCusp (jC N) w) :
    ∃ σ : SL(2, ℤ), ∀ x : FC N, x ≠ 0 → (x ∈ w.toValuationSubring ↔ 0 ≤ (thetaN σ x).order) := by
  set ζc : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hζc
  have hζprim : IsPrimitiveRoot ζc N := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hζ0 : ζc ≠ 0 := hζprim.ne_zero (NeZero.ne N)
  set ζ : ℂˣ := Units.mk0 ζc hζ0 with hζ
  obtain ⟨a, b, ha, hb, hab, hna, ι, hι₁, hι₂, hord⟩ :=
    ModularCurve.exists_slot_of_isCusp ℂ N ζ (by simpa [hζ] using hζprim) w hc
  haveI : NeZero a := hna
  obtain ⟨σ, hσ⟩ := ModularCurve.exists_algHom_slot_mul_qExpansion_slash_eq N ζ (by simp [hζ, hζc])
    a b ha hab ι hι₁ hι₂
  have he : 0 < a * Nat.gcd a (N / a) := by
    have ha0 : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
    exact Nat.mul_pos ha0 (Nat.gcd_pos_of_pos_left _ ha0)
  obtain ⟨hO, -⟩ := slot_detects w ι _ he hord
  refine ⟨σ, fun x hx => ?_⟩

  have hp := isPres_pres x
  have hw' : (0 : ℝ) < N := natCast_pos_of_neZero N
  have hιx : ι x = thetaN σ x := by
    have h1 := hσ x (presWt x) (presNum x) (presDen x) hp.2
    have hH : ((qExpansion N ((presDen x : ℍ → ℂ) ∣[presWt x] σ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
      rw [← coe_translate_SL N (presDen x) σ, Ne, map_eq_zero_iff _ (HahnSeries.ofPowerSeries_injective)]
      exact qExpansion_ne_zero_width _ hw' (natCast_mem_strictPeriods_conjGamma0 N σ) (translate_ne_zero N _ hp.1 σ)
    rw [show thetaN σ x = slashQuot N (presNum x) (presDen x) σ N from
      (cuspExpHomW_apply _ _ _ x).trans (cuspExpW_eq_slashQuot σ hw' (natCast_mem_strictPeriods_conjGamma0 N σ) hp),
      slashQuot, eq_div_iff hH]
    exact h1
  rw [hO x hx, hιx]

theorem exists_cuspPl_eq_of_ord_neg (σ : AlgebraicClosure ℚ →+* ℂ)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) (hv : v.ord (jB N) < 0) :
    ∃ γ : SL(2, ℤ), cuspPl (N := N) σ γ = v := by
  obtain ⟨w, hcomap, hordw, -⟩ := exists_unique_place_over (N := N) σ v
  have hj0 : jB N ≠ 0 := by
    intro h0; rw [h0, v.ord_zero] at hv; exact lt_irrefl _ hv
  have hc : IsCusp (jC N) w := by
    rw [isCusp_iff, ← phi_jB σ]
    intro hmem
    have h1 := (AlgebraicCurve.Place.mem_iff_ord_nonneg _ (phi_ne_zero σ hj0)).mp hmem
    rw [hordw] at h1
    omega
  obtain ⟨γ, hγ⟩ := exists_sigma_of_isCusp w hc
  refine ⟨γ, Place.ext ?_⟩
  ext y
  rw [mem_cuspPl_iff, ← hcomap, ValuationSubring.mem_comap]
  by_cases hy : y = 0
  · simp [hy]
  exact (hγ _ (phi_ne_zero σ hy)).symm

theorem jB_ne_zero : (jB N : ↥(modularFunctionFieldBar N)) ≠ 0 := by
  intro h0
  have : ((jB N : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)).order = -1 :=
    order_coeffEmb_jq (AlgebraicClosure ℚ)
  rw [h0] at this
  simp at this

theorem cuspIdx_mul_neg_ord_jB (σ : AlgebraicClosure ℚ →+* ℂ) (γ : SL(2, ℤ)) :
    (cuspIdx (cuspPl_spec (N := N) σ γ) : ℤ) * (-(cuspPl σ γ).ord (jB N)) =
      (ModularCurve.CuspSpace.cuspWidth (ModularCurve.CuspSpace.mk N
        (Matrix.SpecialLinearGroup.mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ))) : ℤ) := by
  have h1 := order_eq_cuspIdx_mul (cuspPl_spec (N := N) σ γ) (jB_ne_zero (N := N))
  rw [phi_jB] at h1
  have h2 := order_cuspExpHomW_jC_eq (N := N) γ (strictWidthInfty_conjGamma0_pos γ)
    (Subgroup.strictWidthInfty_mem_strictPeriods (conjGamma0 N γ))
  rw [h1] at h2
  replace h2 : (((cuspIdx (cuspPl_spec (N := N) σ γ) : ℤ) * (cuspPl σ γ).ord (jB N) : ℤ) : ℝ) =
      -((ModularCurve.CuspSpace.cuspWidth (ModularCurve.CuspSpace.mk N
        (Matrix.SpecialLinearGroup.mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ))) : ℕ) : ℝ) := by
    rw [← strictWidthInfty_eq_cuspWidth]; exact h2
  have h4 : (cuspIdx (cuspPl_spec (N := N) σ γ) : ℤ) * (cuspPl σ γ).ord (jB N) =
      -(ModularCurve.CuspSpace.cuspWidth (ModularCurve.CuspSpace.mk N
        (Matrix.SpecialLinearGroup.mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ))) : ℤ) := by
    have h3 : (((cuspIdx (cuspPl_spec (N := N) σ γ) : ℤ) * (cuspPl σ γ).ord (jB N) : ℤ) : ℝ) =
        ((-(ModularCurve.CuspSpace.cuspWidth (ModularCurve.CuspSpace.mk N
          (Matrix.SpecialLinearGroup.mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ))) : ℤ) : ℤ) : ℝ) := by
      push_cast at h2 ⊢; linarith [h2]
    exact_mod_cast h3
  linarith [h4]

theorem ord_jB_cuspPl_neg (σ : AlgebraicClosure ℚ →+* ℂ) (γ : SL(2, ℤ)) : (cuspPl (N := N) σ γ).ord (jB N) < 0 := by
  have h := cuspIdx_mul_neg_ord_jB (N := N) σ γ
  have hW : (0 : ℤ) < (ModularCurve.CuspSpace.cuspWidth (ModularCurve.CuspSpace.mk N
        (Matrix.SpecialLinearGroup.mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ))) : ℤ) := by
    exact_mod_cast ModularCurve.CuspSpace.cuspWidth_pos (NeZero.ne N) _
  have hf : (0 : ℤ) < cuspIdx (cuspPl_spec (N := N) σ γ) := by exact_mod_cast one_le_cuspIdx _
  by_contra hle
  push_neg at hle
  have : (cuspIdx (cuspPl_spec (N := N) σ γ) : ℤ) * (-(cuspPl σ γ).ord (jB N)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hf.le (by omega)
  omega

theorem exists_rel_of_mk_eq {γ γ' : SL(2, ℤ)}
    (h : ModularCurve.CuspSpace.mk N (Matrix.SpecialLinearGroup.mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ)) =
      ModularCurve.CuspSpace.mk N (Matrix.SpecialLinearGroup.mapGL ℚ γ' • (OnePoint.infty : OnePoint ℚ))) :
    ∃ δ ∈ CongruenceSubgroup.Gamma0 N, ∃ M : SL(2, ℤ), M 1 0 = 0 ∧ γ' = δ * γ * M := by
  obtain ⟨δ, hδ, hδeq⟩ := ModularCurve.CuspSpace.mk_eq_mk_iff.mp h

  set M : SL(2, ℤ) := γ⁻¹ * δ * γ' with hM
  have hfix : Matrix.SpecialLinearGroup.mapGL ℚ M • (OnePoint.infty : OnePoint ℚ) = OnePoint.infty := by
    rw [hM, map_mul, map_mul, mul_smul, mul_smul, hδeq, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hM10 : M 1 0 = 0 := by
    rw [ModularCurve.mapGL_smul_infty, ModularCurve.ratPoint_eq_infty_iff] at hfix
    exact hfix
  refine ⟨δ⁻¹, inv_mem hδ, M, hM10, ?_⟩
  rw [hM]; group

set_option maxHeartbeats 6400000 in

theorem cuspIdx_cuspPl_eq_one (σ : AlgebraicClosure ℚ →+* ℂ) (γ₀ : SL(2, ℤ)) :
    cuspIdx (cuspPl_spec (N := N) σ γ₀) = 1 := by
  classical
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : Fintype (ModularCurve.CuspSpace N) := Fintype.ofFinite _
  have hN : N ≠ 0 := NeZero.ne N

  set Wd : ModularCurve.CuspSpace N → ℤ := fun c => (ModularCurve.CuspSpace.cuspWidth c : ℤ) with hWd
  set f : SL(2, ℤ) → ℤ := fun γ => (cuspIdx (cuspPl_spec (N := N) σ γ) : ℤ) with hf
  set e : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) → ℤ := fun v => -v.ord (jB N) with he
  set cls : SL(2, ℤ) → ModularCurve.CuspSpace N := fun γ =>
    ModularCurve.CuspSpace.mk N (Matrix.SpecialLinearGroup.mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ)) with hcls
  have hkey : ∀ γ, f γ * e (cuspPl σ γ) = Wd (cls γ) := fun γ => cuspIdx_mul_neg_ord_jB (N := N) σ γ
  have hf1 : ∀ γ, 1 ≤ f γ := fun γ => by simp only [hf]; exact_mod_cast one_le_cuspIdx _
  have hepos : ∀ γ, 0 < e (cuspPl σ γ) := fun γ => by simp only [he]; linarith [ord_jB_cuspPl_neg (N := N) σ γ]

  have hrep : ∀ c : ModularCurve.CuspSpace N, ∃ γ : SL(2, ℤ), cls γ = c := by
    intro c
    obtain ⟨x, rfl⟩ := ModularCurve.CuspSpace.mk_surjective N c
    obtain ⟨g, hg⟩ := OnePoint.exists_mem_SL2 ℤ x
    exact ⟨g, by simp only [hcls, hg]⟩
  choose rep hrep using hrep

  obtain ⟨Dj, hDj, -⟩ := (AlgebraicCurve.IsCurveOver.hasPrincipalDivisors (K := AlgebraicClosure ℚ)
    (F := ↥(modularFunctionFieldBar N))).exists_divisor (jB N) jB_ne_zero
  set P : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) := Dj.support.filter (fun v => Dj v < 0) with hP
  have hPmem : ∀ v, v ∈ P ↔ v.ord (jB N) < 0 := by
    intro v
    rw [hP, Finset.mem_filter, Finsupp.mem_support_iff, hDj v]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.ne, h⟩

  have hsumW : ∑ c : ModularCurve.CuspSpace N, Wd c = ModularCurve.dedekindPsi N := by
    simp only [hWd]
    rw [← Nat.cast_sum]
    exact_mod_cast ModularCurve.CuspSpace.sum_cuspWidth_eq_dedekindPsi N Finset.univ (fun x => Finset.mem_univ x)
  have hsumE : ∑ v ∈ P, e v = ModularCurve.dedekindPsi N := by
    simp only [he]
    exact ModularCurve.sum_neg_ord_jBar_eq_dedekindPsi N P hPmem

  have hsurj : ∀ v ∈ P, ∃ c : ModularCurve.CuspSpace N, cuspPl σ (rep c) = v := by
    intro v hv
    obtain ⟨γ, hγ⟩ := exists_cuspPl_eq_of_ord_neg (N := N) σ v ((hPmem v).mp hv)
    refine ⟨cls γ, ?_⟩
    obtain ⟨δ, hδ, M, hM, hrel⟩ := exists_rel_of_mk_eq (N := N) (γ := γ) (γ' := rep (cls γ))
      (by show cls γ = cls (rep (cls γ)); rw [hrep])
    rw [hrel, cuspPl_rel σ hδ γ M hM, hγ]
  choose! back hback using hsurj

  have hinj : Set.InjOn back (P : Set _) := by
    intro v hv v' hv' hvv'
    rw [← hback v hv, ← hback v' hv', hvv']
  have hS1 : ∑ v ∈ P, e v ≤ ∑ c : ModularCurve.CuspSpace N, e (cuspPl σ (rep c)) := by
    calc ∑ v ∈ P, e v = ∑ v ∈ P, e (cuspPl σ (rep (back v))) := Finset.sum_congr rfl fun v hv => by rw [hback v hv]
      _ = ∑ c ∈ P.image back, e (cuspPl σ (rep c)) := by
          first
            | exact (Finset.sum_image (f := fun c => e (cuspPl σ (rep c))) hinj).symm
            | exact (Finset.sum_image (f := fun c => e (cuspPl σ (rep c))) fun x hx y hy hxy => hinj hx hy hxy).symm
      _ ≤ ∑ c : ModularCurve.CuspSpace N, e (cuspPl σ (rep c)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ => (hepos (rep c)).le

  have hS2 : ∑ c : ModularCurve.CuspSpace N, e (cuspPl σ (rep c)) ≤
      ∑ c : ModularCurve.CuspSpace N, f (rep c) * e (cuspPl σ (rep c)) :=
    Finset.sum_le_sum fun c _ => le_mul_of_one_le_left (hepos (rep c)).le (hf1 (rep c))
  have hS3 : ∑ c : ModularCurve.CuspSpace N, f (rep c) * e (cuspPl σ (rep c)) = ∑ c : ModularCurve.CuspSpace N, Wd c :=
    Finset.sum_congr rfl fun c _ => by rw [hkey, hrep]
  have hall : ∀ c : ModularCurve.CuspSpace N, f (rep c) * e (cuspPl σ (rep c)) - e (cuspPl σ (rep c)) = 0 := by
    have hsum0 : ∑ c : ModularCurve.CuspSpace N, (f (rep c) * e (cuspPl σ (rep c)) - e (cuspPl σ (rep c))) = 0 := by
      rw [Finset.sum_sub_distrib]; linarith [hS1, hS2, hS3, hsumW, hsumE]
    have hnn : ∀ c ∈ (Finset.univ : Finset (ModularCurve.CuspSpace N)),
        0 ≤ f (rep c) * e (cuspPl σ (rep c)) - e (cuspPl σ (rep c)) := fun c _ => by
      have := le_mul_of_one_le_left (hepos (rep c)).le (hf1 (rep c)); linarith
    exact fun c => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 c (Finset.mem_univ c)
  have hrep1 : ∀ c : ModularCurve.CuspSpace N, f (rep c) = 1 := by
    intro c
    have h := hall c
    have he0 := hepos (rep c)
    exact mul_right_cancel₀ he0.ne' (by linarith [h] : f (rep c) * e (cuspPl σ (rep c)) = 1 * e (cuspPl σ (rep c)))

  obtain ⟨δ, hδ, M, hM, hrel⟩ := exists_rel_of_mk_eq (N := N) (γ := γ₀) (γ' := rep (cls γ₀))
    (by show cls γ₀ = cls (rep (cls γ₀)); rw [hrep])
  have hpl : cuspPl (N := N) σ (rep (cls γ₀)) = cuspPl σ γ₀ := by rw [hrel, cuspPl_rel σ hδ γ₀ M hM]
  have h1 := hkey γ₀
  have h2 := hkey (rep (cls γ₀))
  rw [hrep, hpl] at h2
  have h3 : f γ₀ = f (rep (cls γ₀)) := mul_right_cancel₀ (hepos γ₀).ne' (h1.trans h2.symm)
  rw [hrep1] at h3
  simp only [hf] at h3
  exact_mod_cast h3

theorem cuspIdx_eq_one {γ : SL(2, ℤ)} {σ : AlgebraicClosure ℚ →+* ℂ}
    {p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)}
    {hw : 0 < Subgroup.strictWidthInfty (conjGamma0 N γ)}
    {hΓ : Subgroup.strictWidthInfty (conjGamma0 N γ) ∈ (conjGamma0 N γ).strictPeriods}
    (hp : p.toValuationSubring = (qadicSubring ℂ).comap (cuspExpBW γ hw hΓ σ)) : cuspIdx hp = 1 := by
  obtain rfl : p = cuspPl σ γ := Place.ext (hp.trans (cuspPl_spec σ γ).symm)
  exact cuspIdx_cuspPl_eq_one σ γ

theorem order_thetaX_eq_ord (σ : AlgebraicClosure ℚ →+* ℂ) (γ : SL(2, ℤ)) {y : ↥(modularFunctionFieldBar N)} (hy : y ≠ 0) :
    (cuspExpHomW γ (strictWidthInfty_conjGamma0_pos γ) (Subgroup.strictWidthInfty_mem_strictPeriods (conjGamma0 N γ))
      (phi N σ y)).order = (cuspPl σ γ).ord y := by
  rw [order_eq_cuspIdx_mul (cuspPl_spec σ γ) hy, cuspIdx_cuspPl_eq_one, Nat.cast_one, one_mul]

end CuspRegularity

section Cards

variable {N : ℕ} [NeZero N]

end Cards

section CuspInjective

variable {N : ℕ} [NeZero N]

set_option maxHeartbeats 6400000 in

theorem mk_eq_of_cuspPl_eq (σ : AlgebraicClosure ℚ →+* ℂ) {γ₁ γ₂ : SL(2, ℤ)}
    (hγ : cuspPl (N := N) σ γ₁ = cuspPl σ γ₂) :
    ModularCurve.CuspSpace.mk N (Matrix.SpecialLinearGroup.mapGL ℚ γ₁ • (OnePoint.infty : OnePoint ℚ)) =
      ModularCurve.CuspSpace.mk N (Matrix.SpecialLinearGroup.mapGL ℚ γ₂ • (OnePoint.infty : OnePoint ℚ)) := by
  classical
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : Fintype (ModularCurve.CuspSpace N) := Fintype.ofFinite _
  have hN : N ≠ 0 := NeZero.ne N
  set Wd : ModularCurve.CuspSpace N → ℤ := fun c => (ModularCurve.CuspSpace.cuspWidth c : ℤ) with hWd
  set f : SL(2, ℤ) → ℤ := fun γ => (cuspIdx (cuspPl_spec (N := N) σ γ) : ℤ) with hf
  set e : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) → ℤ := fun v => -v.ord (jB N) with he
  set cls : SL(2, ℤ) → ModularCurve.CuspSpace N := fun γ =>
    ModularCurve.CuspSpace.mk N (Matrix.SpecialLinearGroup.mapGL ℚ γ • (OnePoint.infty : OnePoint ℚ)) with hcls
  have hkey : ∀ γ, f γ * e (cuspPl σ γ) = Wd (cls γ) := fun γ => cuspIdx_mul_neg_ord_jB (N := N) σ γ
  have hf1 : ∀ γ, 1 ≤ f γ := fun γ => by simp only [hf]; exact_mod_cast one_le_cuspIdx _
  have hepos : ∀ γ, 0 < e (cuspPl σ γ) := fun γ => by simp only [he]; linarith [ord_jB_cuspPl_neg (N := N) σ γ]
  have hrep : ∀ c : ModularCurve.CuspSpace N, ∃ γ : SL(2, ℤ), cls γ = c := by
    intro c
    obtain ⟨x, rfl⟩ := ModularCurve.CuspSpace.mk_surjective N c
    obtain ⟨g, hg⟩ := OnePoint.exists_mem_SL2 ℤ x
    exact ⟨g, by simp only [hcls, hg]⟩
  choose rep hrep using hrep
  obtain ⟨Dj, hDj, -⟩ := (AlgebraicCurve.IsCurveOver.hasPrincipalDivisors (K := AlgebraicClosure ℚ)
    (F := ↥(modularFunctionFieldBar N))).exists_divisor (jB N) jB_ne_zero
  set P : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) := Dj.support.filter (fun v => Dj v < 0) with hP
  have hPmem : ∀ v, v ∈ P ↔ v.ord (jB N) < 0 := by
    intro v
    rw [hP, Finset.mem_filter, Finsupp.mem_support_iff, hDj v]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.ne, h⟩
  have hsumW : ∑ c : ModularCurve.CuspSpace N, Wd c = ModularCurve.dedekindPsi N := by
    simp only [hWd]
    rw [← Nat.cast_sum]
    exact_mod_cast ModularCurve.CuspSpace.sum_cuspWidth_eq_dedekindPsi N Finset.univ (fun x => Finset.mem_univ x)
  have hsumE : ∑ v ∈ P, e v = ModularCurve.dedekindPsi N := by
    simp only [he]
    exact ModularCurve.sum_neg_ord_jBar_eq_dedekindPsi N P hPmem
  have hsurj : ∀ v ∈ P, ∃ c : ModularCurve.CuspSpace N, cuspPl σ (rep c) = v := by
    intro v hv
    obtain ⟨γ, hγ'⟩ := exists_cuspPl_eq_of_ord_neg (N := N) σ v ((hPmem v).mp hv)
    refine ⟨cls γ, ?_⟩
    obtain ⟨δ, hδ, M, hM, hrel⟩ := exists_rel_of_mk_eq (N := N) (γ := γ) (γ' := rep (cls γ))
      (by show cls γ = cls (rep (cls γ)); rw [hrep])
    rw [hrel, cuspPl_rel σ hδ γ M hM, hγ']
  choose! back hback using hsurj
  have hinj : Set.InjOn back (P : Set _) := by
    intro v hv v' hv' hvv'
    rw [← hback v hv, ← hback v' hv', hvv']

  have hE1 : ∑ v ∈ P, e v = ∑ c ∈ P.image back, e (cuspPl σ (rep c)) := by
    calc ∑ v ∈ P, e v = ∑ v ∈ P, e (cuspPl σ (rep (back v))) := Finset.sum_congr rfl fun v hv => by rw [hback v hv]
      _ = ∑ c ∈ P.image back, e (cuspPl σ (rep c)) := by
          first
            | exact (Finset.sum_image (f := fun c => e (cuspPl σ (rep c))) hinj).symm
            | exact (Finset.sum_image (f := fun c => e (cuspPl σ (rep c))) fun x hx y hy hxy => hinj hx hy hxy).symm
  have hS1 : ∑ c ∈ P.image back, e (cuspPl σ (rep c)) ≤ ∑ c : ModularCurve.CuspSpace N, e (cuspPl σ (rep c)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ => (hepos (rep c)).le
  have hS2 : ∑ c : ModularCurve.CuspSpace N, e (cuspPl σ (rep c)) ≤
      ∑ c : ModularCurve.CuspSpace N, f (rep c) * e (cuspPl σ (rep c)) :=
    Finset.sum_le_sum fun c _ => le_mul_of_one_le_left (hepos (rep c)).le (hf1 (rep c))
  have hS3 : ∑ c : ModularCurve.CuspSpace N, f (rep c) * e (cuspPl σ (rep c)) = ∑ c : ModularCurve.CuspSpace N, Wd c :=
    Finset.sum_congr rfl fun c _ => by rw [hkey, hrep]
  have hEq : ∑ c ∈ P.image back, e (cuspPl σ (rep c)) = ∑ c : ModularCurve.CuspSpace N, e (cuspPl σ (rep c)) := by
    linarith [hE1, hS1, hS2, hS3, hsumW, hsumE]

  have huniv : ∀ c : ModularCurve.CuspSpace N, c ∈ P.image back := by
    intro c
    by_contra hc
    have hsplit := Finset.sum_sdiff (f := fun c => e (cuspPl σ (rep c))) (Finset.subset_univ (P.image back))
    have hzero : ∑ c ∈ Finset.univ \ P.image back, e (cuspPl σ (rep c)) = 0 := by linarith [hsplit, hEq]
    have hnn : ∀ c' ∈ Finset.univ \ P.image back, 0 ≤ e (cuspPl σ (rep c')) := fun c' _ => (hepos (rep c')).le
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero c (Finset.mem_sdiff.mpr ⟨Finset.mem_univ c, hc⟩)
    linarith [hepos (rep c)]

  have hplace : ∀ γ : SL(2, ℤ), cuspPl (N := N) σ (rep (cls γ)) = cuspPl σ γ := by
    intro γ
    obtain ⟨δ, hδ, M, hM, hrel⟩ := exists_rel_of_mk_eq (N := N) (γ := γ) (γ' := rep (cls γ))
      (by show cls γ = cls (rep (cls γ)); rw [hrep])
    rw [hrel, cuspPl_rel σ hδ γ M hM]
  obtain ⟨v₁, hv₁, hb₁⟩ := Finset.mem_image.mp (huniv (cls γ₁))
  obtain ⟨v₂, hv₂, hb₂⟩ := Finset.mem_image.mp (huniv (cls γ₂))
  have e₁ : v₁ = cuspPl σ γ₁ := by rw [← hback v₁ hv₁, hb₁, hplace]
  have e₂ : v₂ = cuspPl σ γ₂ := by rw [← hback v₂ hv₂, hb₂, hplace]
  have hv : v₁ = v₂ := by rw [e₁, e₂, hγ]
  show cls γ₁ = cls γ₂
  rw [← hb₁, ← hb₂, hv]

theorem cuspPl_inj (σ : AlgebraicClosure ℚ →+* ℂ) {γ₁ γ₂ : SL(2, ℤ)} (hγ : cuspPl (N := N) σ γ₁ = cuspPl σ γ₂) :
    ∃ δ ∈ CongruenceSubgroup.Gamma0 N, ∃ M : SL(2, ℤ), M 1 0 = 0 ∧ γ₂ = δ * γ₁ * M :=
  exists_rel_of_mk_eq (mk_eq_of_cuspPl_eq σ hγ)

end CuspInjective

end CUSPATLAS
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

set_option autoImplicit false

open UpperHalfPlane Filter AlgebraicCurve ModularCurve
open scoped Topology

open scoped ComplexConjugate MatrixGroups

noncomputable section

namespace Cay

noncomputable def cay (τ₀ : ℍ) (z : ℂ) : ℂ := (z - (τ₀ : ℂ)) / (z - conj (τ₀ : ℂ))

noncomputable def inv (τ₀ : ℍ) (w : ℂ) : ℂ := ((τ₀ : ℂ) - conj (τ₀ : ℂ) * w) / (1 - w)

theorem im_sub_conj (τ₀ : ℍ) (z : ℂ) : (z - conj (τ₀ : ℂ)).im = z.im + τ₀.im := by
  simp [Complex.sub_im, Complex.conj_im, UpperHalfPlane.coe_im]

theorem sub_conj_ne_zero (τ₀ : ℍ) {z : ℂ} (hz : 0 ≤ z.im) : z - conj (τ₀ : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [im_sub_conj, Complex.zero_im] at this
  linarith [τ₀.im_pos]

theorem cay_self (τ₀ : ℍ) : cay τ₀ (τ₀ : ℂ) = 0 := by simp [cay]

theorem normSq_sub_lt (τ₀ : ℍ) {z : ℂ} (hz : 0 < z.im) :
    Complex.normSq (z - (τ₀ : ℂ)) < Complex.normSq (z - conj (τ₀ : ℂ)) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
    UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
  nlinarith [τ₀.im_pos, hz]

theorem norm_cay_lt_one (τ₀ : ℍ) {z : ℂ} (hz : 0 < z.im) : ‖cay τ₀ z‖ < 1 := by
  have hne := sub_conj_ne_zero τ₀ hz.le
  rw [cay, norm_div, div_lt_one (norm_pos_iff.2 hne)]
  have h := normSq_sub_lt τ₀ hz
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h

theorem inv_cay (τ₀ : ℍ) {z : ℂ} (hz : 0 < z.im) : inv τ₀ (cay τ₀ z) = z := by
  have hne := sub_conj_ne_zero τ₀ hz.le
  have h2 : (τ₀ : ℂ) - conj (τ₀ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.im h
    simp [Complex.sub_im, UpperHalfPlane.coe_im] at this; linarith [τ₀.im_pos]
  simp only [inv, cay]
  field_simp [hne, h2]
  ring

theorem one_sub_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
  intro h
  have : w = 1 := by linear_combination -h
  rw [this, norm_one] at hw
  exact lt_irrefl _ hw

theorem cay_inv (τ₀ : ℍ) {w : ℂ} (hw : ‖w‖ < 1) : cay τ₀ (inv τ₀ w) = w := by
  have h1 := one_sub_ne_zero hw
  have h2 : (τ₀ : ℂ) - conj (τ₀ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.im h
    simp [Complex.sub_im, UpperHalfPlane.coe_im] at this; linarith [τ₀.im_pos]
  have hA : inv τ₀ w - (τ₀ : ℂ) = w * ((τ₀ : ℂ) - conj (τ₀ : ℂ)) / (1 - w) := by
    rw [inv, eq_div_iff h1]; field_simp [h1]; ring
  have hB : inv τ₀ w - conj (τ₀ : ℂ) = ((τ₀ : ℂ) - conj (τ₀ : ℂ)) / (1 - w) := by
    rw [inv, eq_div_iff h1]; field_simp [h1]; ring
  rw [cay, hA, hB]
  field_simp [h1, h2]

theorem im_inv (τ₀ : ℍ) (w : ℂ) (h1 : (1 : ℂ) - w ≠ 0) :
    (inv τ₀ w).im = τ₀.im * (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  rw [inv, Complex.div_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, Complex.normSq_apply]
  have hn : Complex.normSq (1 - w) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  rw [Complex.normSq_apply] at hn
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hn
  field_simp
  ring

theorem im_inv_pos (τ₀ : ℍ) {w : ℂ} (hw : ‖w‖ < 1) : 0 < (inv τ₀ w).im := by
  have h1 := one_sub_ne_zero hw
  rw [im_inv τ₀ w h1]
  have hn : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.2 h1
  have hw2 : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  apply div_pos (mul_pos τ₀.im_pos (by linarith)) hn

theorem analyticAt_inv (τ₀ : ℍ) {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (inv τ₀) w := by
  unfold inv
  exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div (analyticAt_const.sub analyticAt_id)
    (one_sub_ne_zero hw)

theorem inv_zero' (τ₀ : ℍ) : inv τ₀ 0 = (τ₀ : ℂ) := by simp [inv]

theorem coe_sub_conj_ne_zero (τ₀ : ℍ) : (τ₀ : ℂ) - conj (τ₀ : ℂ) ≠ 0 :=
  sub_conj_ne_zero τ₀ (z := (τ₀ : ℂ)) τ₀.im_pos.le

theorem analyticAt_finsum {ι : Type*} (t : Finset ι) {f : ι → ℂ → ℂ} {c : ℂ}
    (h : ∀ i ∈ t, AnalyticAt ℂ (f i) c) : AnalyticAt ℂ (fun w => ∑ i ∈ t, f i w) c := by
  have hfun : (fun w => ∑ i ∈ t, f i w) = ∑ i ∈ t, f i := by
    ext w
    simp [Finset.sum_apply]
  have key := Finset.analyticAt_sum t h
  first
    | exact key
    | (rw [hfun]; exact key)
    | simpa [Finset.sum_apply] using key

theorem natCast_mul_top {m : ℕ} (hm : m ≠ 0) : (m : ℕ∞) * ⊤ = ⊤ := by
  first
    | exact ENat.mul_top (by exact_mod_cast hm)
    | simp [hm]
    | exact WithTop.mul_top (by exact_mod_cast hm)

theorem analyticOrderAt_inv_sub (τ₀ : ℍ) {w₀ : ℂ} (hw₀ : ‖w₀‖ < 1) :
    analyticOrderAt (fun w => inv τ₀ w - inv τ₀ w₀) w₀ = 1 := by
  have ha : AnalyticAt ℂ (fun w => inv τ₀ w - inv τ₀ w₀) w₀ := (analyticAt_inv τ₀ hw₀).sub analyticAt_const
  rw [← Nat.cast_one, ha.analyticOrderAt_eq_natCast]
  have h1 := one_sub_ne_zero hw₀
  have h2 := coe_sub_conj_ne_zero τ₀
  refine ⟨fun w => ((τ₀ : ℂ) - conj (τ₀ : ℂ)) / ((1 - w) * (1 - w₀)), ?_, ?_, ?_⟩
  · exact analyticAt_const.div ((analyticAt_const.sub analyticAt_id).mul analyticAt_const) (mul_ne_zero h1 h1)
  · exact div_ne_zero h2 (mul_ne_zero h1 h1)
  · have hball : ∀ᶠ w in 𝓝 w₀, ‖w‖ < 1 := by
      have : w₀ ∈ Metric.ball (0 : ℂ) 1 := by simpa using hw₀
      exact (Metric.isOpen_ball.eventually_mem this).mono fun w hw => by simpa using hw
    filter_upwards [hball] with w hw
    have h3 := one_sub_ne_zero hw
    simp only [pow_one, smul_eq_mul, inv]
    field_simp
    ring

theorem analyticOrderAt_pow_sub {w₀ : ℂ} (hw₀ : w₀ ≠ 0) {e : ℕ} (he : 0 < e) :
    analyticOrderAt (fun w => w ^ e - w₀ ^ e) w₀ = 1 := by
  have hid : AnalyticAt ℂ (fun w : ℂ => w) w₀ := analyticAt_id
  have ha : AnalyticAt ℂ (fun w => w ^ e - w₀ ^ e) w₀ := (hid.pow e).sub analyticAt_const
  rw [← Nat.cast_one, ha.analyticOrderAt_eq_natCast]
  refine ⟨fun w => ∑ i ∈ Finset.range e, w ^ i * w₀ ^ (e - 1 - i), ?_, ?_, ?_⟩
  · exact analyticAt_finsum _ fun i _ => ((analyticAt_id (𝕜 := ℂ) (E := ℂ)).pow i).mul analyticAt_const
  · dsimp only
    rw [geom_sum₂_self]
    exact mul_ne_zero (by exact_mod_cast he.ne') (pow_ne_zero _ hw₀)
  · filter_upwards with w
    rw [pow_one, smul_eq_mul, ← geom_sum₂_mul, mul_comm]

theorem analyticOrderAt_pow_zero (e : ℕ) : analyticOrderAt (fun w : ℂ => w ^ e) 0 = e := by
  have ha : AnalyticAt ℂ (fun w : ℂ => w ^ e) 0 := (analyticAt_id (𝕜 := ℂ) (E := ℂ)).pow e
  rw [ha.analyticOrderAt_eq_natCast]
  exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, by simp⟩

theorem analyticOrderAt_comp {f g : ℂ → ℂ} {z₀ : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f (g z₀)) (hg : AnalyticAt ℂ g z₀)
    (hm : analyticOrderAt (fun z => g z - g z₀) z₀ = m) :
    analyticOrderAt (fun z => f (g z)) z₀ = m * analyticOrderAt f (g z₀) := by
  have hga : AnalyticAt ℂ (fun z => g z - g z₀) z₀ := hg.sub analyticAt_const
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h0 := hga.analyticOrderAt_eq_zero
    rw [Nat.cast_zero] at hm
    exact (h0.mp hm) (sub_self _)
  obtain ⟨k, hk, hk0, hgk⟩ := hga.analyticOrderAt_eq_natCast.mp hm
  have hfg : AnalyticAt ℂ (fun z => f (g z)) z₀ := hf.comp hg
  cases h : analyticOrderAt f (g z₀) with
  | top =>
    rw [natCast_mul_top hm0]
    rw [analyticOrderAt_eq_top] at h ⊢
    exact hg.continuousAt.tendsto.eventually h
  | coe n =>
    obtain ⟨h', hh', hh'0, hfh⟩ := hf.analyticOrderAt_eq_natCast.mp h
    have hmn : ((m : ℕ∞) * (n : ℕ∞)) = ((m * n : ℕ) : ℕ∞) := by push_cast; rfl
    rw [hmn, hfg.analyticOrderAt_eq_natCast]
    refine ⟨fun z => k z ^ n * h' (g z), (hk.pow n).mul (hh'.comp hg), ?_, ?_⟩
    · exact mul_ne_zero (pow_ne_zero _ hk0) hh'0
    · filter_upwards [hgk, hg.continuousAt.tendsto.eventually hfh] with z hz hz'
      simp only [smul_eq_mul] at hz hz' ⊢
      rw [hz', hz]
      ring

theorem analyticOrderAt_comp_pow {H : ℂ → ℂ} {e : ℕ} (he : 0 < e) (hH : AnalyticAt ℂ H 0) :
    analyticOrderAt (fun w => H (w ^ e)) 0 = e * analyticOrderAt H 0 := by
  have h0 : (fun w : ℂ => w ^ e) 0 = 0 := zero_pow he.ne'
  have hH' : AnalyticAt ℂ H ((fun w : ℂ => w ^ e) 0) := by rwa [h0]
  have := analyticOrderAt_comp (f := H) (g := fun w : ℂ => w ^ e) (m := e) hH' ((analyticAt_id (𝕜 := ℂ) (E := ℂ)).pow e)
    (by simpa [zero_pow he.ne'] using analyticOrderAt_pow_zero e)
  simpa [zero_pow he.ne'] using this

theorem analyticOrderAt_comp_inv (τ₀ : ℍ) {f : ℂ → ℂ} {w₀ : ℂ} (hw₀ : ‖w₀‖ < 1)
    (hf : AnalyticAt ℂ f (inv τ₀ w₀)) :
    analyticOrderAt (fun w => f (inv τ₀ w)) w₀ = analyticOrderAt f (inv τ₀ w₀) := by
  have := analyticOrderAt_comp (m := 1) hf (analyticAt_inv τ₀ hw₀) (by exact_mod_cast analyticOrderAt_inv_sub τ₀ hw₀)
  simpa using this

theorem analyticOrderAt_comp_pow_of_ne_zero {H : ℂ → ℂ} {w₀ : ℂ} (hw₀ : w₀ ≠ 0) {e : ℕ} (he : 0 < e)
    (hH : AnalyticAt ℂ H (w₀ ^ e)) :
    analyticOrderAt (fun w => H (w ^ e)) w₀ = analyticOrderAt H (w₀ ^ e) := by
  have := analyticOrderAt_comp (f := H) (g := fun w : ℂ => w ^ e) (m := 1) hH ((analyticAt_id (𝕜 := ℂ) (E := ℂ)).pow e)
    (by exact_mod_cast analyticOrderAt_pow_sub hw₀ he)
  simpa using this

namespace ENat

private theorem _root_.Cay.ENat.eq_of_mul_eq_mul_left {e : ℕ} (he : 0 < e) {a b : ℕ∞} (h : (e : ℕ∞) * a = e * b) : a = b := by
  have he' : (e : ℕ∞) ≠ 0 := by exact_mod_cast he.ne'
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe b =>
      rw [natCast_mul_top he.ne'] at h
      exact absurd h.symm (by exact_mod_cast ENat.coe_ne_top (e * b))
  | coe a =>
    induction b using ENat.recTopCoe with
    | top =>
      rw [natCast_mul_top he.ne'] at h
      exact absurd h (by exact_mod_cast ENat.coe_ne_top (e * a))
    | coe b =>
      have : e * a = e * b := by exact_mod_cast h
      exact_mod_cast Nat.eq_of_mul_eq_mul_left he this

end ENat
p2m_export "Cay" "ENat.eq_of_mul_eq_mul_left"

theorem exists_cay_pow_eq (τ₀ : ℍ) {e : ℕ} (he : 0 < e) {u : ℂ} (hu : ‖u‖ < 1) :
    ∃ z : ℂ, 0 < z.im ∧ cay τ₀ z ^ e = u ∧ (u = 0 → z = τ₀) := by
  by_cases hu0 : u = 0
  · exact ⟨τ₀, τ₀.im_pos, by rw [cay_self, zero_pow he.ne', hu0], fun _ => rfl⟩
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq u he
  have hw1 : ‖w‖ < 1 := by
    have : ‖w‖ ^ e < 1 ^ e := by rw [← norm_pow, hw, one_pow]; exact hu
    exact lt_of_pow_lt_pow_left₀ e zero_le_one this
  exact ⟨inv τ₀ w, im_inv_pos τ₀ hw1, by rw [cay_inv τ₀ hw1, hw], fun h => absurd h hu0⟩

end Cay
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace GInj
open Cay

end GInj
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace Rot3

private theorem _root_.Rot3.coe_smul_eq (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) / (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [algebraMap_int_eq, Complex.ofReal_intCast]

p2m_export "Rot3" "coe_smul_eq"
end Rot3
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace ATLINT

open CUSPATLAS (FC phi jB jC phi_jB phi_algebraMap phi_ne_zero)

abbrev FB (N : ℕ) : Type := ↥(modularFunctionFieldBar N)

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem isRational_FC (w : Place ℂ (FC N)) : w.IsRational := by
  haveI : IsCurveOver ℂ (FC N) := ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull ℂ N
  exact (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField w).1
    (IsCurveOver.deg_eq_one_of_isAlgClosed w)

def Φint (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) : ℂ → (Fin r → ℂ) :=
  fun z i => limUnder (𝓝[≠] z) (fun z' : ℂ => realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (ofComplex z'))

structure InteriorInputs (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) : Prop where
  reg : ∀ (τ : ℍ) (i : Fin r), phi N σ (s i) ∈ (D.pt τ).toValuationSubring
  bpf : ∀ τ : ℍ, ∃ i : Fin r, (D.pt τ).ord (phi N σ (s i)) = 0

variable (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)

theorem interior_coord (h : InteriorInputs D σ s) (τ : ℍ) (i : Fin r) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      (fun z : ℂ => realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] g ∧
      g (τ : ℂ) = (D.pt τ).evalAt (phi N σ (s i)) ∧
      Φint σ s (τ : ℂ) i = g (τ : ℂ) := by
  obtain ⟨g, hg, heq, hval⟩ := D.exists_analyticAt_eventuallyEq_realize τ _ (h.reg τ i)
  refine ⟨g, hg, heq, hval, ?_⟩

  have ht : Tendsto (fun z' : ℂ => realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (ofComplex z'))
      (𝓝[≠] (τ : ℂ)) (𝓝 (g (τ : ℂ))) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
  simp only [Φint]
  exact ht.limUnder_eq

theorem interior_ne_zero (hs : IsEmbBasis N s) (h : InteriorInputs D σ s) (τ : ℍ) :
    Φint σ s (τ : ℂ) ≠ 0 := by
  obtain ⟨i, hi⟩ := h.bpf τ
  obtain ⟨g, hg, heq, hval, hΦ⟩ := interior_coord D σ s h τ i
  intro h0
  have hsi : phi N σ (s i) ≠ 0 := (map_ne_zero_iff _ (phi N σ).injective).mpr (hs.1.ne_zero i)
  have hne := (D.pt τ).evalAt_ne_zero (isRational_FC _) hsi hi
  apply hne
  rw [← hval, ← hΦ, h0]
  rfl

theorem jB_notMem : jB N ∉ (cuspInftyBar N).toValuationSubring := by
  unfold cuspInftyBar
  rw [qInftyPlaceBar_toValuationSubring]
  exact notMem_qIntegersBar_of_order_eq_neg_one (order_coeffEmb_jq (AlgebraicClosure ℚ))

set_option synthInstance.maxHeartbeats 800000 in

theorem exists_place_comap (w : Place ℂ (FC N)) (hw : ∃ y : FB N, phi N σ y ∉ w.toValuationSubring) :
    ∃ v : Place (AlgebraicClosure ℚ) (FB N),
      v.toValuationSubring = w.toValuationSubring.comap (phi N σ) := by
  haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jB N} : Set (FB N))) (FB N) :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jB N} : Set (FB N))) (FB N) := by
    first
      | infer_instance
      | exact Algebra.IsSeparable.of_finite _ _
      | exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable (jB N) (phi N σ)
    w.toValuationSubring (fun a => by rw [phi_algebraMap]; exact w.algebraMap_mem' _) hw

theorem ord_eq_zero_of_mem_of_inv_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)
    {x : F} (hx : x ∈ w.toValuationSubring) (hx' : x⁻¹ ∈ w.toValuationSubring) : w.ord x = 0 := by
  have h1 := w.ord_nonneg_of_mem hx
  have h2 := w.ord_nonneg_of_mem hx'
  rw [w.ord_inv] at h2
  omega

theorem interiorInputs_of (hs : IsEmbBasis N s)
    (hjreg : ∀ τ : ℍ, jC N ∈ (D.pt τ).toValuationSubring) : InteriorInputs D σ s := by
  classical
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hsmem : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := fun i => by
    rw [← hs.2]; exact Submodule.subset_span ⟨i, rfl⟩

  have key : ∀ τ : ℍ, (∀ i, phi N σ (s i) ∈ (D.pt τ).toValuationSubring) ∧
      ∃ i, (D.pt τ).ord (phi N σ (s i)) = 0 := by
    intro τ
    have hr : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h
      · exfalso
        subst h0
        have h1 : (1 : FB N) ∈ riemannRochSpace (embDivisor N) := by
          rw [mem_riemannRochSpace_iff]
          intro w
          right
          rw [w.ord_one, neg_nonpos]
          simp only [embDivisor, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
          split_ifs <;> simp
        rw [← hs.2, Set.range_eq_empty s, Submodule.span_empty, Submodule.mem_bot] at h1
        exact one_ne_zero h1
      · exact h
    by_cases hex : ∃ y : FB N, phi N σ y ∉ (D.pt τ).toValuationSubring
    · obtain ⟨v, hv⟩ := exists_place_comap σ (D.pt τ) hex
      have hvinf : v ≠ cuspInftyBar N := by
        intro h0
        apply jB_notMem (N := N)
        rw [← h0, hv, ValuationSubring.mem_comap, phi_jB]
        exact hjreg τ
      have hEv : embDivisor N v = 0 := by
        simp only [embDivisor, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
        rw [if_neg (Ne.symm hvinf), mul_zero]
      have hreg : ∀ i, s i ∈ v.toValuationSubring := fun i => by
        refine v.mem_of_ord_nonneg (hs0 i) ?_
        rcases (mem_riemannRochSpace_iff.mp (hsmem i)) v with h0 | h
        · exact absurd h0 (hs0 i)
        · rw [hEv] at h; simpa using h
      have hregC : ∀ i, phi N σ (s i) ∈ (D.pt τ).toValuationSubring := fun i => by
        have := hreg i
        rw [hv, ValuationSubring.mem_comap] at this
        exact this
      refine ⟨hregC, ?_⟩
      obtain ⟨i, hi⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs v
      rw [hEv, add_zero] at hi
      refine ⟨i, ord_eq_zero_of_mem_of_inv_mem _ (hregC i) ?_⟩
      have hinv : (s i)⁻¹ ∈ v.toValuationSubring :=
        v.mem_of_ord_nonneg (inv_ne_zero (hs0 i)) (by rw [v.ord_inv, hi, neg_zero])
      rw [hv, ValuationSubring.mem_comap, map_inv₀] at hinv
      exact hinv
    · push Not at hex
      refine ⟨fun i => hex _, ⟨⟨0, hr⟩, ?_⟩⟩
      exact ord_eq_zero_of_mem_of_inv_mem _ (hex _) (by rw [← map_inv₀]; exact hex _)
  exact ⟨fun τ i => (key τ).1 i, fun τ => (key τ).2⟩

theorem jC_ne_zero : jC N ≠ 0 := by
  intro h0
  have h1 : ((jC N : FC N) : LaurentSeries ℂ) = 0 := by rw [h0]; rfl
  have h2 := order_coeffEmb_jq ℂ
  change ((jC N : FC N) : LaurentSeries ℂ).order = -1 at h2
  rw [h1, HahnSeries.order_zero] at h2
  exact absurd h2 (by norm_num)

def Jfun : ℍ → ℂ := fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

omit [NeZero N] in
theorem analyticAt_modularForm_ofComplex {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} (f : ModularForm Γ k) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hE : DifferentiableOn ℂ ((⇑f : ℍ → ℂ) ∘ ofComplex) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  exact hE.analyticAt (hopen.mem_nhds τ.2)

omit [NeZero N] in
theorem analyticAt_cuspForm_ofComplex {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ k) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => (f : ℍ → ℂ) (ofComplex z)) (τ : ℂ) := by
  have hE : DifferentiableOn ℂ ((⇑f : ℍ → ℂ) ∘ ofComplex) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  exact hE.analyticAt (hopen.mem_nhds τ.2)

omit [NeZero N] in
theorem analyticAt_J_ofComplex (τ : ℍ) : AnalyticAt ℂ (fun z : ℂ => Jfun (ofComplex z)) (τ : ℂ) := by
  have hE := analyticAt_modularForm_ofComplex ModularForm.E₄ τ
  have hD := analyticAt_cuspForm_ofComplex CuspForm.discriminant τ
  have hD0 : (CuspForm.discriminant : ℍ → ℂ) (ofComplex (τ : ℂ)) ≠ 0 := by
    rw [ofComplex_apply]; exact ModularForm.discriminant_ne_zero τ
  exact (hE.pow 3).div hD hD0

omit [NeZero N] in
set_option maxHeartbeats 4000000 in

theorem hasSum_int_of_powerSeries {f : ℍ → ℂ} (P : PowerSeries ℂ) (τ : ℍ)
    (h : HasSum (fun m : ℕ => PowerSeries.coeff m P • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ)) :
    HasSum (fun m : ℤ => ((P : LaurentSeries ℂ)).coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ) := by
  have hnat : HasSum (fun m : ℕ => ((P : LaurentSeries ℂ)).coeff (m : ℤ) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ (m : ℤ)) (f τ) := by
    refine h.congr_fun fun m => ?_
    rw [PowerSeries.coeff_coe, zpow_natCast, smul_eq_mul, if_neg (by omega), Int.natAbs_natCast]
  have hneg : HasSum (fun m : ℕ => ((P : LaurentSeries ℂ)).coeff (-(m + 1 : ℤ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ (-(m + 1 : ℤ))) 0 := by
    have hz : (fun m : ℕ => ((P : LaurentSeries ℂ)).coeff (-(m + 1 : ℤ)) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ (-(m + 1 : ℤ))) = fun _ => 0 := by
      funext m
      rw [PowerSeries.coeff_coe, if_pos (by omega), zero_mul]
    rw [hz]; exact hasSum_zero
  have := HasSum.of_nat_of_neg_add_one
    (f := fun m : ℤ => ((P : LaurentSeries ℂ)).coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) hnat hneg
  rwa [add_zero] at this

omit [NeZero N] in

theorem hasSum_qExpansion_Gamma0 (N : ℕ) {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    HasSum (fun m : ℕ => PowerSeries.coeff m (qExpansion 1 (f : ℍ → ℂ)) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) ((f : ℍ → ℂ) τ) := by
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  haveI : Fact (IsCusp OnePoint.infty ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ))) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact UpperHalfPlane.hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

theorem jC_mem_pt (τ : ℍ) : jC N ∈ (D.pt τ).toValuationSubring := by
  obtain ⟨k, g, h, hh0, hx, hloc⟩ :=
    ModularCurve.exists_modularForm_realize_eventuallyEq_div N (jC N)

  have hgJ : ∀ t : ℍ, (g : ℍ → ℂ) t = Jfun t * (h : ℍ → ℂ) t := by
    intro t
    have hA : ∀ t : ℍ, HasSum (fun m : ℤ => ((jC N : FC N) : LaurentSeries ℂ).coeff m *
        Function.Periodic.qParam 1 (t : ℂ) ^ m) (Jfun t) := by
      intro t
      refine (ModularCurve.hasSum_jq_qParam t).congr_fun fun m => ?_
      show ((jq.coeff m : ℚ) : ℂ) * _ = (coeffEmb ℂ jq).coeff m * _
      rw [coeffEmb, coeffMap_coeff, eq_ratCast]
    have hB : ∀ t : ℍ, HasSum (fun m : ℤ => (((qExpansion 1 (h : ℍ → ℂ)) : PowerSeries ℂ) : LaurentSeries ℂ).coeff m *
        Function.Periodic.qParam 1 (t : ℂ) ^ m) ((h : ℍ → ℂ) t) :=
      fun t => hasSum_int_of_powerSeries _ t (hasSum_qExpansion_Gamma0 N h t)
    have hAB := ModularCurve.hasSum_qParam_mul_laurent 1 one_pos _ _ _ _ hA hB t
    rw [hx] at hAB
    have hG := hasSum_int_of_powerSeries _ t (hasSum_qExpansion_Gamma0 N g t)
    exact hG.unique hAB
  have hmer := D.meromorphicOrderAt_realize τ (jC N) jC_ne_zero
  have hh_an := analyticAt_modularForm_ofComplex h τ

  have heqJ : (fun z : ℂ => realize N ((jC N : FC N) : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)] fun z => Jfun (ofComplex z) := by
    rcases hh_an.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
    · exfalso
      have h0 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), realize N ((jC N : FC N) : LaurentSeries ℂ) (ofComplex z) = 0 := by
        filter_upwards [hloc τ, hz.filter_mono nhdsWithin_le_nhds] with z h1 h2
        rw [h1, h2, div_zero]
      have htop := meromorphicOrderAt_eq_top_iff.2 h0
      rw [htop] at hmer
      exact WithTop.top_ne_coe hmer
    · filter_upwards [hloc τ, hnz] with z h1 h2
      rw [h1]
      show (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z) = Jfun (ofComplex z)
      rw [hgJ, mul_div_assoc, div_self h2, mul_one]

  rw [meromorphicOrderAt_congr heqJ, (analyticAt_J_ofComplex τ).meromorphicOrderAt_eq] at hmer
  have hnn : 0 ≤ (D.ramification τ : ℤ) * (D.pt τ).ord (jC N) := by
    cases h' : analyticOrderAt (fun z : ℂ => Jfun (ofComplex z)) (τ : ℂ) with
    | top =>
      rw [h', ENat.map_top] at hmer
      exact absurd hmer WithTop.top_ne_coe
    | coe n =>
      rw [h'] at hmer
      have h2 : ((n : ℤ) : WithTop ℤ) = (((D.ramification τ : ℤ) * (D.pt τ).ord (jC N) : ℤ) : WithTop ℤ) := by
        simpa using hmer
      have h3 : (n : ℤ) = (D.ramification τ : ℤ) * (D.pt τ).ord (jC N) := by exact_mod_cast h2
      rw [← h3]; exact Int.natCast_nonneg n
  have he : (0 : ℤ) < D.ramification τ := by exact_mod_cast D.ramification_pos τ
  have hord : 0 ≤ (D.pt τ).ord (jC N) := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg he hneg
    omega
  exact (D.pt τ).mem_of_ord_nonneg jC_ne_zero hord

theorem interiorInputs (hs : IsEmbBasis N s) : InteriorInputs D σ s :=
  interiorInputs_of D σ s hs (jC_mem_pt D)

theorem evalAt_sum_smul' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    {ι : Type*} (t : Finset ι) (a : ι → K) (g : ι → F) (hg : ∀ i ∈ t, g i ∈ v.toValuationSubring) :
    (∑ i ∈ t, a i • g i) ∈ v.toValuationSubring ∧
    v.evalAt (∑ i ∈ t, a i • g i) = ∑ i ∈ t, a i * v.evalAt (g i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_⟩
    simp only [Finset.sum_empty]
    simpa using v.evalAt_algebraMap (0 : K)
  | insert j t hj ih =>
    obtain ⟨hmem, hval⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hgj : g j ∈ v.toValuationSubring := hg j (Finset.mem_insert_self _ _)
    have hsm : a j • g j ∈ v.toValuationSubring := by
      rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' _) hgj
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    refine ⟨add_mem hsm hmem, ?_⟩
    have hadd : v.evalAt (a j • g j + ∑ i ∈ t, a i • g i) = v.evalAt (a j • g j) + v.evalAt (∑ i ∈ t, a i • g i) := by
      apply v.algebraMap_residueField_injective
      rw [map_add, v.algebraMap_evalAt hv (add_mem hsm hmem), v.algebraMap_evalAt hv hsm,
        v.algebraMap_evalAt hv hmem, ← map_add]
      rfl
    rw [hadd, hval, Algebra.smul_def, v.evalAt_mul hv (v.algebraMap_mem' _) hgj, v.evalAt_algebraMap]

private def _root_.ATLINT.ext (x : FC N) : ℂ → ℂ :=
  fun z => limUnder (𝓝[≠] z) (fun w : ℂ => realize N ((x : FC N) : LaurentSeries ℂ) (ofComplex w))

p2m_export "ATLINT" "ext"
omit [NeZero N] in
theorem Φint_eq_ext (i : Fin r) (z : ℂ) : Φint σ s z i = ext (N := N) (phi N σ (s i)) z := rfl

theorem ext_spec (x : FC N) (τ : ℍ) (hx : x ∈ (D.pt τ).toValuationSubring) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      (fun z : ℂ => realize N ((x : FC N) : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] g ∧
      g (τ : ℂ) = (D.pt τ).evalAt x ∧ (∀ᶠ z in 𝓝 (τ : ℂ), ext x z = g z) := by
  obtain ⟨g, hg, heq, hval⟩ := D.exists_analyticAt_eventuallyEq_realize τ _ hx
  refine ⟨g, hg, heq, hval, ?_⟩

  have h1 : ∀ᶠ z in 𝓝 (τ : ℂ), z ≠ (τ : ℂ) → realize N ((x : FC N) : LaurentSeries ℂ) (ofComplex z) = g z :=
    eventually_nhdsWithin_iff.mp heq
  have h2 : ∀ᶠ z in 𝓝 (τ : ℂ), ∀ᶠ w in 𝓝 z, w ≠ (τ : ℂ) → realize N ((x : FC N) : LaurentSeries ℂ) (ofComplex w) = g w :=
    h1.eventually_nhds
  have hgc : ∀ᶠ z in 𝓝 (τ : ℂ), ContinuousAt g z := hg.eventually_analyticAt.mono fun z hz => hz.continuousAt
  filter_upwards [h2, hgc] with z hz hzc

  have ht : Tendsto (fun w : ℂ => realize N ((x : FC N) : LaurentSeries ℂ) (ofComplex w)) (𝓝[≠] z) (𝓝 (g z)) := by
    by_cases hzτ : z = (τ : ℂ)
    · subst hzτ
      exact (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
    · have hne : ∀ᶠ w in 𝓝 z, w ≠ (τ : ℂ) := isOpen_ne.eventually_mem hzτ
      have heq' : ∀ᶠ w in 𝓝[≠] z, g w = realize N ((x : FC N) : LaurentSeries ℂ) (ofComplex w) := by
        refine ((hz.and hne).filter_mono nhdsWithin_le_nhds).mono fun w hw => ?_
        exact (hw.1 hw.2).symm
      exact (hzc.tendsto.mono_left nhdsWithin_le_nhds).congr' heq'
  exact ht.limUnder_eq

theorem ext_analyticAt (x : FC N) (τ : ℍ) (hx : x ∈ (D.pt τ).toValuationSubring) :
    AnalyticAt ℂ (ext x) (τ : ℂ) ∧
      (fun z : ℂ => realize N ((x : FC N) : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] ext x ∧
      ext x (τ : ℂ) = (D.pt τ).evalAt x := by
  obtain ⟨g, hg, heq, hval, hext⟩ := ext_spec D x τ hx
  refine ⟨hg.congr (hext.mono fun z hz => hz.symm), heq.trans ((hext.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.symm), ?_⟩
  rw [hext.self_of_nhds, hval]

theorem analyticOrderAt_ext_ne_top (x : FC N) (hx0 : x ≠ 0) (τ : ℍ) (hx : x ∈ (D.pt τ).toValuationSubring) :
    analyticOrderAt (ext x) (τ : ℂ) ≠ ⊤ := by
  obtain ⟨han, heq, -⟩ := ext_analyticAt D x τ hx
  have hmer := D.meromorphicOrderAt_realize τ x hx0
  rw [meromorphicOrderAt_congr heq, han.meromorphicOrderAt_eq] at hmer
  intro htop
  rw [htop, ENat.map_top] at hmer
  exact WithTop.top_ne_coe hmer

theorem ext_linComb {ι : Type*} (t : Finset ι) (a : ι → ℂ) (x : ι → FC N) (τ : ℍ)
    (hx : ∀ i ∈ t, x i ∈ (D.pt τ).toValuationSubring) :
    ext (∑ i ∈ t, a i • x i) (τ : ℂ) = ∑ i ∈ t, a i * ext (x i) (τ : ℂ) := by
  obtain ⟨hmem, hval⟩ := evalAt_sum_smul' (D.pt τ) (isRational_FC _) t a x hx
  rw [(ext_analyticAt D _ τ hmem).2.2, hval]
  exact Finset.sum_congr rfl fun i hi => by rw [(ext_analyticAt D _ τ (hx i hi)).2.2]

omit [NeZero N] in
theorem im_pos_of_mem_ball (τc : ℍ) {z : ℂ} (hz : z ∈ Metric.ball (τc : ℂ) (τc.im / 2)) : 0 < z.im := by
  have h1 : |z.im - (τc : ℂ).im| ≤ ‖z - (τc : ℂ)‖ := by
    simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - (τc : ℂ))
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h2 := τc.im_pos
  have h3 : (τc : ℂ).im = τc.im := rfl
  rw [h3] at h1
  have := abs_sub_lt_iff.mp (lt_of_le_of_lt h1 hz)
  linarith [this.1, this.2]

theorem interior_chart (hs : IsEmbBasis N s) (τc : ℍ) :
    let R : ℝ := τc.im / 2
    0 < R ∧
    (∀ i, AnalyticOnNhd ℂ (fun z => Φint σ s z i) (Metric.ball (τc : ℂ) R)) ∧
    (∀ z (hz : z ∈ Metric.ball (τc : ℂ) R), ∀ i,
        Φint σ s z i = (D.pt ⟨z, im_pos_of_mem_ball τc hz⟩).evalAt (phi N σ (s i)) ∧
        (fun w : ℂ => realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (ofComplex w)) =ᶠ[𝓝[≠] z]
          fun w => Φint σ s w i) ∧
    (∀ z ∈ Metric.ball (τc : ℂ) R, Φint σ s z ≠ 0) ∧
    (∀ a : Fin r → ℂ, (∑ i, a i • phi N σ (s i)) ≠ 0 →
        ∀ z ∈ Metric.ball (τc : ℂ) R, analyticOrderAt (fun w => ∑ i, a i * Φint σ s w i) z ≠ ⊤) := by
  intro R
  have hR : 0 < R := by positivity
  have hin := interiorInputs D σ s hs
  have key : ∀ z (hz : z ∈ Metric.ball (τc : ℂ) R), ∀ i,
      AnalyticAt ℂ (fun w => Φint σ s w i) z ∧
      Φint σ s z i = (D.pt ⟨z, im_pos_of_mem_ball τc hz⟩).evalAt (phi N σ (s i)) ∧
      (fun w : ℂ => realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (ofComplex w)) =ᶠ[𝓝[≠] z]
          fun w => Φint σ s w i := by
    intro z hz i
    have := ext_analyticAt D (phi N σ (s i)) ⟨z, im_pos_of_mem_ball τc hz⟩ (hin.reg _ i)
    exact ⟨this.1, this.2.2, this.2.1⟩
  refine ⟨hR, fun i z hz => (key z hz i).1, fun z hz i => ⟨(key z hz i).2.1, (key z hz i).2.2⟩, ?_, ?_⟩
  · intro z hz
    have := interior_ne_zero D σ s hs hin ⟨z, im_pos_of_mem_ball τc hz⟩
    exact this
  · intro a ha z hz
    set τ : ℍ := ⟨z, im_pos_of_mem_ball τc hz⟩
    have hreg : ∀ i ∈ Finset.univ, phi N σ (s i) ∈ (D.pt τ).toValuationSubring := fun i _ => hin.reg τ i

    have hmem : (∑ i, a i • phi N σ (s i)) ∈ (D.pt τ).toValuationSubring :=
      (evalAt_sum_smul' (D.pt τ) (isRational_FC _) Finset.univ a _ hreg).1
    have hfin := analyticOrderAt_ext_ne_top D _ ha τ hmem

    have hev : ∀ᶠ w in 𝓝 z, (∑ i, a i * Φint σ s w i) = ext (∑ i, a i • phi N σ (s i)) w := by
      have hball : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball (τc : ℂ) R := Metric.isOpen_ball.eventually_mem hz
      filter_upwards [hball] with w hw
      have hτw : 0 < w.im := im_pos_of_mem_ball τc hw
      have := ext_linComb D Finset.univ a (fun i => phi N σ (s i)) ⟨w, hτw⟩ (fun i _ => hin.reg _ i)
      rw [this]
      rfl
    rwa [analyticOrderAt_congr hev]

omit [NeZero N] in
theorem lipschitzOn_of_analyticOnNhd {f : ℂ → ℂ} {c : ℂ} {R ρ : ℝ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball c R)) (hρ : ρ < R) :
    ∃ L, LipschitzOnWith L f (Metric.closedBall c ρ) := by
  have hsub : Metric.closedBall c ρ ⊆ Metric.ball c R := Metric.closedBall_subset_ball hρ
  have hd : ∀ x ∈ Metric.closedBall c ρ, DifferentiableAt ℂ f x :=
    fun x hx => (hf x (hsub hx)).differentiableAt
  have hcont : ContinuousOn (deriv f) (Metric.closedBall c ρ) := (hf.deriv.continuousOn).mono hsub
  obtain ⟨M, hM⟩ := (isCompact_closedBall c ρ).exists_bound_of_continuousOn hcont
  refine ⟨⟨max M 0, le_max_right _ _⟩, ?_⟩
  refine (convex_closedBall c ρ).lipschitzOnWith_of_nnnorm_deriv_le hd fun x hx => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hM x hx).trans (le_max_left _ _)

include D in

theorem interior_chart_lipschitz (hs : IsEmbBasis N s) (τc : ℍ) {ρ : ℝ} (hρ : ρ < τc.im / 2) (i : Fin r) :
    ∃ L, LipschitzOnWith L (fun z => Φint σ s z i) (Metric.closedBall (τc : ℂ) ρ) :=
  lipschitzOn_of_analyticOnNhd ((interior_chart D σ s hs τc).2.1 i) hρ

theorem ext_smul (γ : CongruenceSubgroup.Gamma0 N) (x : FC N) (τ : ℍ)
    (hx : x ∈ (D.pt τ).toValuationSubring) :
    ext x (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = ext x (τ : ℂ) := by
  have hx' : x ∈ (D.pt ((γ : SL(2, ℤ)) • τ)).toValuationSubring := by rw [D.pt_smul]; exact hx
  rw [(ext_analyticAt D x _ hx').2.2, (ext_analyticAt D x τ hx).2.2, D.pt_smul]

def rot (γ : SL(2, ℤ)) (τ₀ : ℍ) : ℂ :=
  (((γ 1 0 : ℤ) : ℂ) * conj (τ₀ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) / (((γ 1 0 : ℤ) : ℂ) * (τ₀ : ℂ) + ((γ 1 1 : ℤ) : ℂ))

omit [NeZero N] in

theorem cay_smul (γ : SL(2, ℤ)) (τ₀ : ℍ) (h : γ • τ₀ = τ₀) (τ : ℍ) :
    Cay.cay τ₀ ((γ • τ : ℍ) : ℂ) = rot γ τ₀ * Cay.cay τ₀ (τ : ℂ) :=
  UpperHalfPlane.cayley_smul_eq_mul_cayley γ τ₀ h τ

def G (τ₀ : ℍ) : ℂ → (Fin r → ℂ) := fun w => Φint σ s (Cay.inv τ₀ w)

include D in

theorem analyticAt_G (hs : IsEmbBasis N s) (τ₀ : ℍ) {w : ℂ} (hw : ‖w‖ < 1) (i : Fin r) :
    AnalyticAt ℂ (fun w => G σ s τ₀ w i) w := by
  have him := Cay.im_inv_pos τ₀ hw
  have h1 : AnalyticAt ℂ (fun z => Φint σ s z i) (Cay.inv τ₀ w) := by
    have := (ext_analyticAt D (phi N σ (s i)) ⟨Cay.inv τ₀ w, him⟩ ((interiorInputs D σ s hs).reg _ i)).1
    exact this
  exact h1.comp (Cay.analyticAt_inv τ₀ hw)

include D in

theorem G_rot (hs : IsEmbBasis N s) (τ₀ : ℍ) (γ : CongruenceSubgroup.Gamma0 N)
    (hγ : (γ : SL(2, ℤ)) • τ₀ = τ₀) {w : ℂ} (hw : ‖w‖ < 1) :
    G σ s τ₀ (rot (γ : SL(2, ℤ)) τ₀ * w) = G σ s τ₀ w := by
  have him := Cay.im_inv_pos τ₀ hw
  set z : ℍ := ⟨Cay.inv τ₀ w, him⟩ with hz
  have hw' : Cay.cay τ₀ (z : ℂ) = w := Cay.cay_inv τ₀ hw
  have h1 : rot (γ : SL(2, ℤ)) τ₀ * w = Cay.cay τ₀ (((γ : SL(2, ℤ)) • z : ℍ) : ℂ) := by
    rw [cay_smul _ _ hγ, hw']
  funext i
  simp only [G]
  rw [h1, Cay.inv_cay τ₀ ((γ : SL(2, ℤ)) • z).im_pos]
  have := ext_smul D γ (phi N σ (s i)) z ((interiorInputs D σ s hs).reg _ i)
  simp only [Φint_eq_ext]
  convert this using 2

include D in

theorem exists_factor_pow (hs : IsEmbBasis N s) (τ₀ : ℍ) (γ : CongruenceSubgroup.Gamma0 N)
    (hγ : (γ : SL(2, ℤ)) • τ₀ = τ₀) {e : ℕ} (he : 0 < e) (hω : IsPrimitiveRoot (rot (γ : SL(2, ℤ)) τ₀) e) :
    ∃ F : ℂ → (Fin r → ℂ), (∀ i, AnalyticOnNhd ℂ (fun u => F u i) (Metric.ball 0 1)) ∧
      ∀ w ∈ Metric.ball (0 : ℂ) 1, G σ s τ₀ w = F (w ^ e) := by
  have key : ∀ i, ∃ Fi : ℂ → ℂ, AnalyticOnNhd ℂ Fi (Metric.ball 0 ((1 : ℝ) ^ e)) ∧
      ∀ w ∈ Metric.ball (0 : ℂ) 1, G σ s τ₀ w i = Fi (w ^ e) := by
    intro i
    refine Complex.exists_analyticOnNhd_comp_pow_of_forall_mul_eq he hω one_pos (fun w hw => ?_) (fun w hw => ?_)
    · exact analyticAt_G D σ s hs τ₀ (by simpa using hw) i
    · have := congrFun (G_rot D σ s hs τ₀ γ hγ (by simpa using hw)) i
      exact this
  choose Fi hFi using key
  refine ⟨fun u i => Fi i u, fun i => by simpa using (hFi i).1, fun w hw => funext fun i => (hFi i).2 w hw⟩

omit [NeZero N] in
theorem denom_eq (γ : SL(2, ℤ)) (τ₀ : ℍ) :
    UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) (τ₀ : ℂ) = ((γ 1 0 : ℤ) : ℂ) * (τ₀ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
  simp [ModularGroup.denom_apply]

omit [NeZero N] in
theorem rot_eq (γ : SL(2, ℤ)) (τ₀ : ℍ) :
    rot γ τ₀ = conj (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) (τ₀ : ℂ)) / UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) (τ₀ : ℂ) := by
  rw [denom_eq, rot, map_add, map_mul, map_intCast, map_intCast]

omit [NeZero N] in
theorem denom_ne_zero' (γ : SL(2, ℤ)) (τ₀ : ℍ) : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) (τ₀ : ℂ) ≠ 0 :=
  UpperHalfPlane.denom_ne_zero _ _

omit [NeZero N] in
theorem rot_ne_zero (γ : SL(2, ℤ)) (τ₀ : ℍ) : rot γ τ₀ ≠ 0 := by
  rw [rot_eq]
  exact div_ne_zero ((map_ne_zero _).2 (denom_ne_zero' γ τ₀)) (denom_ne_zero' γ τ₀)

omit [NeZero N] in

theorem rot_mul (γ γ' : SL(2, ℤ)) (τ₀ : ℍ) (h' : γ' • τ₀ = τ₀) :
    rot (γ * γ') τ₀ = rot γ τ₀ * rot γ' τ₀ := by
  have hcoc : UpperHalfPlane.denom ((γ * γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) (τ₀ : ℂ)
      = UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) (τ₀ : ℂ) * UpperHalfPlane.denom (γ' : GL (Fin 2) ℝ) (τ₀ : ℂ) := by
    have h1 : ((γ * γ' : SL(2, ℤ)) : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * (γ' : GL (Fin 2) ℝ) := by
      simp [map_mul]
    rw [h1, UpperHalfPlane.denom_cocycle _ _ τ₀.im_ne_zero]
    congr 1
    have h2 : UpperHalfPlane.num (γ' : GL (Fin 2) ℝ) (τ₀ : ℂ) / UpperHalfPlane.denom (γ' : GL (Fin 2) ℝ) (τ₀ : ℂ)
        = ((γ' • τ₀ : ℍ) : ℂ) := by
      rw [UpperHalfPlane.specialLinearGroup_apply]
      first
        | rfl
        | simp [UpperHalfPlane.coe_mk]
    rw [h2, h']
  rw [rot_eq, rot_eq, rot_eq, hcoc, map_mul]
  field_simp

def rotHom (τ₀ : ℍ) : MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ₀ →* ℂˣ where
  toFun γ := Units.mk0 (rot ((γ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) τ₀) (rot_ne_zero _ _)
  map_one' := by
    ext
    simp [rot]
  map_mul' γ γ' := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    have h' : ((γ' : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • τ₀ = τ₀ := γ'.2
    convert rot_mul _ _ τ₀ h' using 2
    all_goals first | rfl | simp [Subgroup.coe_mul]

omit [NeZero N] in
private theorem _root_.ATLINT.coe_smul_eq (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) / (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [algebraMap_int_eq, Complex.ofReal_intCast]

p2m_export "ATLINT" "coe_smul_eq"
omit [NeZero N] in

theorem rot_eq_one_iff (γ : SL(2, ℤ)) (τ₀ : ℍ) (hγ : γ • τ₀ = τ₀) :
    rot γ τ₀ = 1 ↔ γ = 1 ∨ γ = -1 := by
  constructor
  · intro h
    rw [rot_eq, div_eq_one_iff_eq (denom_ne_zero' γ τ₀), Complex.conj_eq_iff_im, denom_eq] at h
    have hc : (γ 1 0 : ℤ) = 0 := by
      have h1 : ((γ 1 0 : ℤ) : ℝ) * τ₀.im = 0 := by
        simpa [Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re] using h
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact_mod_cast h2
      · exact absurd h2 τ₀.im_pos.ne'
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    have had := Int.eq_one_or_neg_one_of_mul_eq_one' hdet

    have hb : (γ 0 1 : ℤ) = 0 := by
      have h3 := congrArg (fun z : ℍ => (z : ℂ)) hγ
      beta_reduce at h3
      rw [coe_smul_eq, hc] at h3
      push_cast at h3
      rw [zero_mul, zero_add] at h3
      rcases had with ⟨ha, hd⟩ | ⟨ha, hd⟩
      · rw [ha, hd] at h3; push_cast at h3
        have : ((γ 0 1 : ℤ) : ℂ) = 0 := by
          rw [div_one, one_mul] at h3
          linear_combination h3
        exact_mod_cast this
      · rw [ha, hd] at h3; push_cast at h3
        have : ((γ 0 1 : ℤ) : ℂ) = 0 := by
          rw [div_eq_iff (by norm_num : (-1 : ℂ) ≠ 0)] at h3
          linear_combination h3
        exact_mod_cast this
    rcases had with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · rintro (rfl | rfl)
    · simp [rot]
    · rw [rot]
      simp

def negOne (τ₀ : ℍ) : MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ₀ :=
  ⟨⟨-1, by rw [CongruenceSubgroup.Gamma0_mem]; simp⟩, by
    show ((-1 : SL(2, ℤ))) • τ₀ = τ₀
    ext1
    rw [coe_smul_eq]
    simp⟩

theorem mem_ker_rotHom_iff (τ₀ : ℍ) (γ : MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ₀) :
    γ ∈ (rotHom (N := N) τ₀).ker ↔ γ = 1 ∨ γ = negOne τ₀ := by
  rw [MonoidHom.mem_ker]
  have hγ : ((γ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • τ₀ = τ₀ := γ.2
  have h1 : rotHom (N := N) τ₀ γ = 1 ↔ rot ((γ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) τ₀ = 1 := by
    rw [← Units.val_eq_one]; rfl
  rw [h1, rot_eq_one_iff _ _ hγ]
  constructor
  · rintro (h | h)
    · left; exact Subtype.ext (Subtype.ext h)
    · right; exact Subtype.ext (Subtype.ext h)
  · rintro (rfl | rfl)
    · left; rfl
    · right; rfl

theorem card_ker_rotHom (τ₀ : ℍ) : Nat.card (rotHom (N := N) τ₀).ker = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, (mem_ker_rotHom_iff τ₀ 1).2 (Or.inl rfl)⟩, ⟨negOne τ₀, (mem_ker_rotHom_iff τ₀ _).2 (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun g : (rotHom (N := N) τ₀).ker => (((g : MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ₀) : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) 0 0) h
    simp [negOne] at h1
  · ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (mem_ker_rotHom_iff τ₀ g.1).1 g.2 with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

include D in

theorem exists_primitive_rot (τ₀ : ℍ) :
    ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ₀ = τ₀ ∧
      IsPrimitiveRoot (rot (γ : SL(2, ℤ)) τ₀) (D.ramification τ₀) := by
  classical
  set S := MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ₀ with hS
  have hcardS : Nat.card S = 2 * D.ramification τ₀ := (D.two_mul_ramification_eq_card_stabilizer τ₀).symm
  have he := D.ramification_pos τ₀
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hcardS]; omega)
  set ρ := rotHom (N := N) τ₀ with hρ
  haveI : Finite ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  haveI : IsCyclic ρ.range := isCyclic_subgroup_units ρ.range

  have hrange : Nat.card ρ.range = D.ramification τ₀ := by
    have h1 := Subgroup.index_ker ρ
    have h2 := ρ.ker.card_mul_index
    rw [card_ker_rotHom, hcardS, h1] at h2
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ρ.range)
  rw [hrange] at hg
  obtain ⟨γ, hγ⟩ := g.2
  refine ⟨(γ : CongruenceSubgroup.Gamma0 N), γ.2, ?_⟩
  have hval : rot ((γ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) τ₀ = ((g : ℂˣ) : ℂ) := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hγ
    simpa [hρ, rotHom] using this
  rw [hval]
  have h3 : orderOf ((g : ℂˣ) : ℂ) = D.ramification τ₀ := by
    rw [orderOf_units, Subgroup.orderOf_coe, hg]
  exact h3 ▸ IsPrimitiveRoot.orderOf _

theorem analyticOrderAt_ext_eq (x : FC N) (hx0 : x ≠ 0) (τ : ℍ) (hx : x ∈ (D.pt τ).toValuationSubring) :
    0 ≤ (D.pt τ).ord x ∧
      analyticOrderAt (ext x) (τ : ℂ) = ((((D.ramification τ : ℤ) * (D.pt τ).ord x).toNat : ℕ) : ℕ∞) := by
  refine ⟨(D.pt τ).ord_nonneg_of_mem hx, ?_⟩
  obtain ⟨han, heq, -⟩ := ext_analyticAt D x τ hx
  have hmer := D.meromorphicOrderAt_realize τ x hx0
  rw [meromorphicOrderAt_congr heq, han.meromorphicOrderAt_eq] at hmer
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_ext_ne_top D x hx0 τ hx)
  rw [← hn] at hmer ⊢
  rw [ENat.map_coe] at hmer
  have h1 : ((n : ℕ) : ℤ) = (D.ramification τ : ℤ) * (D.pt τ).ord x := by exact_mod_cast hmer
  rw [← h1, Int.toNat_natCast]

include D in

theorem linComb_eventuallyEq_ext (hs : IsEmbBasis N s) (b : Fin r → ℂ) {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    (fun w => ∑ i, b i * Φint σ s w i) =ᶠ[𝓝 z₀] ext (∑ i, b i • phi N σ (s i)) := by
  have hopen : ∀ᶠ w in 𝓝 z₀, 0 < w.im := (isOpen_lt continuous_const Complex.continuous_im).eventually_mem hz₀
  filter_upwards [hopen] with w hw
  have := ext_linComb D Finset.univ b (fun i => phi N σ (s i)) ⟨w, hw⟩
    (fun i _ => (interiorInputs D σ s hs).reg _ i)
  rw [this]
  rfl

theorem linComb_mem (hs : IsEmbBasis N s) (b : Fin r → ℂ) (τ : ℍ) :
    (∑ i, b i • phi N σ (s i)) ∈ (D.pt τ).toValuationSubring :=
  (evalAt_sum_smul' (D.pt τ) (isRational_FC _) Finset.univ b _
    (fun i _ => (interiorInputs D σ s hs).reg τ i)).1

include D in

theorem analyticAt_linComb (hs : IsEmbBasis N s) (b : Fin r → ℂ) {z₀ : ℂ} (hz₀ : 0 < z₀.im) :
    AnalyticAt ℂ (fun w => ∑ i, b i * Φint σ s w i) z₀ :=
  (ext_analyticAt D _ ⟨z₀, hz₀⟩ (linComb_mem D σ s hs b ⟨z₀, hz₀⟩)).1.congr
    (linComb_eventuallyEq_ext D σ s hs b hz₀).symm

theorem analyticOrderAt_linComb (hs : IsEmbBasis N s) (b : Fin r → ℂ)
    (hb : (∑ i, b i • phi N σ (s i)) ≠ 0) (τ : ℍ) :
    0 ≤ (D.pt τ).ord (∑ i, b i • phi N σ (s i)) ∧
      analyticOrderAt (fun w => ∑ i, b i * Φint σ s w i) (τ : ℂ)
        = ((((D.ramification τ : ℤ) * (D.pt τ).ord (∑ i, b i • phi N σ (s i))).toNat : ℕ) : ℕ∞) := by
  obtain ⟨h0, h1⟩ := analyticOrderAt_ext_eq D _ hb τ (linComb_mem D σ s hs b τ)
  exact ⟨h0, by rw [analyticOrderAt_congr (linComb_eventuallyEq_ext D σ s hs b τ.im_pos), h1]⟩

omit [NeZero N] in
theorem toNat_natCast_mul {e : ℕ} {k : ℤ} (hk : 0 ≤ k) : ((e : ℤ) * k).toNat = e * k.toNat := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rw [Int.toNat_natCast, ← Nat.cast_mul, Int.toNat_natCast]

include D in

theorem elliptic_chart (hs : IsEmbBasis N s) (τ₀ : ℍ) :
    ∃ F : ℂ → (Fin r → ℂ),
      (∀ i, AnalyticOnNhd ℂ (fun u => F u i) (Metric.ball 0 1)) ∧
      (∀ z : ℂ, 0 < z.im → F (Cay.cay τ₀ z ^ D.ramification τ₀) = Φint σ s z) ∧
      (∀ τ : ℍ, ∀ i, F (Cay.cay τ₀ τ ^ D.ramification τ₀) i = (D.pt τ).evalAt (phi N σ (s i)) ∧
        (fun w : ℂ => realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (ofComplex w)) =ᶠ[𝓝[≠] (τ : ℂ)]
          fun w => F (Cay.cay τ₀ w ^ D.ramification τ₀) i) ∧
      (∀ u ∈ Metric.ball (0 : ℂ) 1, F u ≠ 0) ∧
      (∀ b : Fin r → ℂ, (∑ i, b i • phi N σ (s i)) ≠ 0 →
        analyticOrderAt (fun u => ∑ i, b i * F u i) 0
          = ((((D.pt τ₀).ord (∑ i, b i • phi N σ (s i))).toNat : ℕ) : ℕ∞)) ∧
      (∀ b : Fin r → ℂ, (∑ i, b i • phi N σ (s i)) ≠ 0 → ∀ z : ℂ, ∀ hz : 0 < z.im, Cay.cay τ₀ z ≠ 0 →
        analyticOrderAt (fun u => ∑ i, b i * F u i) (Cay.cay τ₀ z ^ D.ramification τ₀)
          = ((((D.ramification ⟨z, hz⟩ : ℤ) * (D.pt ⟨z, hz⟩).ord (∑ i, b i • phi N σ (s i))).toNat : ℕ) : ℕ∞)) ∧
      (∀ b : Fin r → ℂ, (∑ i, b i • phi N σ (s i)) ≠ 0 →
        ∀ u ∈ Metric.ball (0 : ℂ) 1, analyticOrderAt (fun u => ∑ i, b i * F u i) u ≠ ⊤) := by
  set e := D.ramification τ₀ with he_def
  have he : 0 < e := D.ramification_pos τ₀
  have hin := interiorInputs D σ s hs
  obtain ⟨γ, hγ, hω⟩ := exists_primitive_rot D τ₀
  obtain ⟨F, hFA, hFG⟩ := exists_factor_pow D σ s hs τ₀ γ hγ he hω

  have hV0 : ∀ z : ℂ, 0 < z.im → F (Cay.cay τ₀ z ^ e) = Φint σ s z := by
    intro z hz
    have hw : Cay.cay τ₀ z ∈ Metric.ball (0 : ℂ) 1 := by simpa using Cay.norm_cay_lt_one τ₀ hz
    rw [← hFG _ hw]
    simp only [G]
    rw [Cay.inv_cay τ₀ hz]

  have hHan : ∀ (b : Fin r → ℂ) (u : ℂ), ‖u‖ < 1 → AnalyticAt ℂ (fun u => ∑ i, b i * F u i) u := by
    intro b u hu
    exact Cay.analyticAt_finsum _ fun i _ => analyticAt_const.mul (hFA i u (by simpa using hu))

  have hcomb : ∀ (b : Fin r → ℂ) (w₀ : ℂ), ‖w₀‖ < 1 →
      (fun w => ∑ i, b i * F (w ^ e) i) =ᶠ[𝓝 w₀] fun w => ∑ i, b i * Φint σ s (Cay.inv τ₀ w) i := by
    intro b w₀ hw₀
    have hball : ∀ᶠ w in 𝓝 w₀, w ∈ Metric.ball (0 : ℂ) 1 :=
      Metric.isOpen_ball.eventually_mem (by simpa using hw₀)
    filter_upwards [hball] with w hw
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hFG w hw]
    rfl

  have hORD0 : ∀ b : Fin r → ℂ, (∑ i, b i • phi N σ (s i)) ≠ 0 →
      analyticOrderAt (fun u => ∑ i, b i * F u i) 0
        = ((((D.pt τ₀).ord (∑ i, b i • phi N σ (s i))).toNat : ℕ) : ℕ∞) := by
    intro b hb
    have h1 := Cay.analyticOrderAt_comp_pow (H := fun u => ∑ i, b i * F u i) he (hHan b 0 (by simp))
    have h2 : analyticOrderAt (fun w => ∑ i, b i * Φint σ s (Cay.inv τ₀ w) i) 0
        = analyticOrderAt (fun z => ∑ i, b i * Φint σ s z i) (τ₀ : ℂ) := by
      have := Cay.analyticOrderAt_comp_inv τ₀ (f := fun z => ∑ i, b i * Φint σ s z i) (w₀ := 0) (by simp)
        (by rw [Cay.inv_zero']; exact analyticAt_linComb D σ s hs b τ₀.im_pos)
      rw [Cay.inv_zero'] at this
      exact this
    obtain ⟨h0, h3⟩ := analyticOrderAt_linComb D σ s hs b hb τ₀
    rw [analyticOrderAt_congr (hcomb b 0 (by simp)), h2, h3, toNat_natCast_mul h0, Nat.cast_mul] at h1
    exact (Cay.ENat.eq_of_mul_eq_mul_left he h1).symm

  have hORD : ∀ b : Fin r → ℂ, (∑ i, b i • phi N σ (s i)) ≠ 0 → ∀ z : ℂ, ∀ hz : 0 < z.im, Cay.cay τ₀ z ≠ 0 →
      analyticOrderAt (fun u => ∑ i, b i * F u i) (Cay.cay τ₀ z ^ e)
        = ((((D.ramification ⟨z, hz⟩ : ℤ) * (D.pt ⟨z, hz⟩).ord (∑ i, b i • phi N σ (s i))).toNat : ℕ) : ℕ∞) := by
    intro b hb z hz hcz
    have hw₀ : ‖Cay.cay τ₀ z‖ < 1 := Cay.norm_cay_lt_one τ₀ hz
    have hwe : ‖Cay.cay τ₀ z ^ e‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hw₀ he.ne'
    have h1 := Cay.analyticOrderAt_comp_pow_of_ne_zero (H := fun u => ∑ i, b i * F u i) hcz he (hHan b _ hwe)
    have h2 := Cay.analyticOrderAt_comp_inv τ₀ (f := fun z => ∑ i, b i * Φint σ s z i) hw₀
        (by rw [Cay.inv_cay τ₀ hz]; exact analyticAt_linComb D σ s hs b hz)
    rw [Cay.inv_cay τ₀ hz] at h2
    obtain ⟨-, h3⟩ := analyticOrderAt_linComb D σ s hs b hb ⟨z, hz⟩
    rw [← h1, analyticOrderAt_congr (hcomb b _ hw₀), h2]
    exact h3
  refine ⟨F, hFA, hV0, ?_, ?_, hORD0, hORD, ?_⟩
  ·
    intro τ i
    have hA := ext_analyticAt D (phi N σ (s i)) τ (hin.reg τ i)
    rw [hV0 _ τ.im_pos]
    refine ⟨hA.2.2, hA.2.1.trans ?_⟩
    have hopen : ∀ᶠ w in 𝓝 (τ : ℂ), 0 < w.im :=
      (isOpen_lt continuous_const Complex.continuous_im).eventually_mem τ.im_pos
    refine (hopen.filter_mono nhdsWithin_le_nhds).mono fun w hw => ?_
    dsimp only
    rw [hV0 w hw]
    rfl
  ·
    intro u hu
    obtain ⟨z, hz, hzu, -⟩ := Cay.exists_cay_pow_eq τ₀ he (by simpa using hu)
    rw [← hzu, hV0 z hz]
    exact interior_ne_zero D σ s hs hin ⟨z, hz⟩
  ·
    intro b hb u hu
    obtain ⟨z, hz, hzu, hz0⟩ := Cay.exists_cay_pow_eq τ₀ he (by simpa using hu)
    by_cases hu0 : u = 0
    · subst hu0
      rw [hORD0 b hb]
      exact ENat.coe_ne_top _
    · have hcz : Cay.cay τ₀ z ≠ 0 := by
        intro h
        rw [h, zero_pow he.ne'] at hzu
        exact hu0 hzu.symm
      rw [← hzu, hORD b hb z hz hcz]
      exact ENat.coe_ne_top _

include D in

theorem elliptic_chart_lipschitz {F : ℂ → (Fin r → ℂ)} (hFA : ∀ i, AnalyticOnNhd ℂ (fun u => F u i) (Metric.ball 0 1))
    {ρ : ℝ} (hρ : ρ < 1) (i : Fin r) :
    ∃ L, LipschitzOnWith L (fun u => F u i) (Metric.closedBall (0 : ℂ) ρ) :=
  lipschitzOn_of_analyticOnNhd (hFA i) hρ

end ATLINT
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace GLUE
open CUSPATLAS ATLINT

variable {N : ℕ} [NeZero N] {r : ℕ}
variable (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)

example : (ATLINT.Φint (N := N) σ s) = fun z i => ATLINT.ext (N := N) (phi N σ (s i)) z := rfl

theorem exists_analyticOrderAt_eq_one (hs : IsEmbBasis N s) (τ₀ : ℍ) {F : ℂ → (Fin r → ℂ)}
    (hORD0 : ∀ b : Fin r → ℂ, (∑ i, b i • phi N σ (s i)) ≠ 0 →
      analyticOrderAt (fun u => ∑ i, b i * F u i) 0
        = ((((D.pt τ₀).ord (∑ i, b i • phi N σ (s i))).toNat : ℕ) : ℕ∞)) :
    ∃ b : Fin r → ℂ, (∑ i, b i • phi N σ (s i)) ≠ 0 ∧ analyticOrderAt (fun u => ∑ i, b i * F u i) 0 = 1 := by
  obtain ⟨f, hfspan, hf0, hford⟩ := CUSPATLAS.exists_mem_span_ord_eq_one D σ s hs τ₀ (ATLINT.jC_mem_pt D τ₀)
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hfspan
  have hb' : (∑ i, b i • phi N σ (s i)) = f := by
    rw [← hb]
  refine ⟨b, by rwa [hb'], ?_⟩
  rw [hORD0 b (by rwa [hb']), hb', hford]
  first
    | rfl
    | simp

theorem isCompact_box (B y₀ Y₁ : ℝ) :
    IsCompact {z : ℂ | |z.re| ≤ B ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁} := by
  have : {z : ℂ | |z.re| ≤ B ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁} = (Set.Icc (-B) B) ×ℂ (Set.Icc y₀ Y₁) := by
    ext z
    simp only [Set.mem_setOf_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le]
  rw [this]
  exact isCompact_Icc.reProdIm isCompact_Icc

theorem cover_box_or_cusp [(CongruenceSubgroup.Gamma0 N).FiniteIndex] (Y : ℝ) :
    ∃ (S : Finset SL(2, ℤ)) (B y₀ Y₁ : ℝ), 0 < y₀ ∧ ∀ τ : ℍ, ∃ γ ∈ CongruenceSubgroup.Gamma0 N,
      (|(γ • τ).re| ≤ B ∧ y₀ ≤ (γ • τ).im ∧ (γ • τ).im ≤ Y₁) ∨
      (∃ σ ∈ S, ∃ z ∈ ModularGroup.fd, Y < z.im ∧ γ • τ = σ • z) :=
  ModularGroup.exists_finset_box_or_cusp (CongruenceSubgroup.Gamma0 N) Y

end GLUE
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

namespace L2lin

variable {K : Type*} [Field K] {r : ℕ}

def dot (x a : Fin r → K) : K := ∑ i, x i * a i

theorem dot_add (x a b : Fin r → K) : dot x (a + b) = dot x a + dot x b := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_smul (x a : Fin r → K) (t : K) : dot x (t • a) = t * dot x a := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dot_zero (x : Fin r → K) : dot x 0 = 0 := by simp [dot]

theorem exists_avoid [Infinite K] (xv : Fin r → K) (T : Finset (Fin r → K))
    (hT : ∀ x ∈ T, ∃ e : Fin r → K, dot xv e = 0 ∧ dot x e ≠ 0) :
    ∃ a : Fin r → K, dot xv a = 0 ∧ ∀ x ∈ T, dot x a ≠ 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, dot_zero _, by simp⟩
  | insert x T hx ih =>
    obtain ⟨a, hav, haT⟩ := ih (fun y hy => hT y (Finset.mem_insert_of_mem hy))
    obtain ⟨e, hev, hex⟩ := hT x (Finset.mem_insert_self _ _)
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
      (insert (-(dot x a) / dot x e) (T.image fun y => -(dot y a) / dot y e))
    refine ⟨a + t • e, ?_, ?_⟩
    · rw [dot_add, dot_smul, hav, hev, mul_zero, add_zero]
    · intro y hy
      rw [dot_add, dot_smul]
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · intro h0
        apply ht
        rw [Finset.mem_insert]; left
        rw [eq_div_iff hex]; linear_combination h0
      · intro h0
        by_cases hye : dot y e = 0
        · rw [hye, mul_zero, add_zero] at h0; exact haT y hy h0
        · apply ht
          rw [Finset.mem_insert]; right
          rw [Finset.mem_image]
          exact ⟨y, hy, by rw [div_eq_iff hye]; linear_combination -h0⟩

end L2lin
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace L2

theorem isRational (N : ℕ) [NeZero N] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : w.IsRational :=
  (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField w).1
    (ModularCurve.deg_eq_one_modularFunctionFieldBar N w)

theorem evalAt_add' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

theorem evalAt_zero' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.evalAt (0 : F) = 0 := by
  simpa using v.evalAt_algebraMap (0 : K)

theorem evalAt_sum_smul {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    {ι : Type*} (t : Finset ι) (a : ι → K) (g : ι → F) (hg : ∀ i ∈ t, g i ∈ v.toValuationSubring) :
    (∑ i ∈ t, a i • g i) ∈ v.toValuationSubring ∧
    v.evalAt (∑ i ∈ t, a i • g i) = ∑ i ∈ t, a i * v.evalAt (g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨by simp, by simp [evalAt_zero']⟩
  | insert j t hj ih =>
    obtain ⟨hmem, hval⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hgj : g j ∈ v.toValuationSubring := hg j (Finset.mem_insert_self _ _)
    have hsm : a j • g j ∈ v.toValuationSubring := by
      rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' _) hgj
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    refine ⟨add_mem hsm hmem, ?_⟩
    rw [evalAt_add' v hv hsm hmem, hval, Algebra.smul_def, v.evalAt_mul hv (v.algebraMap_mem' _) hgj,
      v.evalAt_algebraMap]

theorem neg_le_ord_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) {f : F}
    (hf : f ∈ riemannRochSpace D) (hf0 : f ≠ 0) (w : Place K F) : -D w ≤ w.ord f := by
  have hval : w.adicValuation f ≤ WithZero.exp (D w) := hf w
  have hlog := (WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hf0)).2 hval
  simp only [AlgebraicCurve.Place.ord]
  linarith

private theorem _root_.L2.r_pos (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    0 < r := by
  rcases Nat.eq_zero_or_pos r with h0 | h
  · exfalso
    subst h0
    have h1 : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (embDivisor N) := by
      rw [mem_riemannRochSpace_iff]
      intro w
      right
      rw [w.ord_one, neg_nonpos]
      classical
      simp only [embDivisor, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs <;> simp
    rw [← hs.2] at h1
    have : Set.range s = ∅ := Set.range_eq_empty s
    rw [this, Submodule.span_empty, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · exact h

p2m_export "L2" "r_pos"
theorem s_ne_zero (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (i : Fin r) : s i ≠ 0 := hs.1.ne_zero i

theorem s_mem (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (i : Fin r) : s i ∈ riemannRochSpace (embDivisor N) := by
  rw [← hs.2]; exact Submodule.subset_span ⟨i, rfl⟩

theorem ord_pivot (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hr : 0 < r) : w.ord (s (pivotIndex s w hr)) = -embDivisor N w := by
  classical
  have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact Finite.exists_min fun i => w.ord (s i)
  have hpiv : ∀ j, w.ord (s (pivotIndex s w hr)) ≤ w.ord (s j) := by
    unfold pivotIndex
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  obtain ⟨i₀, hi₀⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs w
  refine le_antisymm (by linarith [hpiv i₀]) ?_
  exact neg_le_ord_of_mem _ (s_mem N s hs _) (s_ne_zero N s hs _) w

theorem ratio_mem (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hr : 0 < r) (i : Fin r) :
    s i * (s (pivotIndex s w hr))⁻¹ ∈ w.toValuationSubring ∧
    0 ≤ w.ord (s i * (s (pivotIndex s w hr))⁻¹) ∧
    w.evalAt (s i * (s (pivotIndex s w hr))⁻¹) = evalVec s w i := by
  have hne : s i * (s (pivotIndex s w hr))⁻¹ ≠ 0 :=
    mul_ne_zero (s_ne_zero N s hs i) (inv_ne_zero (s_ne_zero N s hs _))
  have hord : 0 ≤ w.ord (s i * (s (pivotIndex s w hr))⁻¹) := by
    rw [w.ord_mul (s_ne_zero N s hs i) (inv_ne_zero (s_ne_zero N s hs _)), w.ord_inv, ord_pivot N s hs w hr]
    have := neg_le_ord_of_mem _ (s_mem N s hs i) (s_ne_zero N s hs i) w
    linarith
  refine ⟨w.mem_of_ord_nonneg hne hord, hord, ?_⟩
  simp only [evalVec, dif_pos hr]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem hypSec_facts (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hZa : ∀ w, Za w = w.ord (linSec s a) + embDivisor N w) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    0 ≤ Za w ∧ (Za w = 0 ↔ ∑ i, evalVec s w i * a i ≠ 0) := by
  classical
  have hr := r_pos N s hs
  have hv := isRational N w
  obtain ⟨hGmem, hGval⟩ := evalAt_sum_smul w hv Finset.univ a
    (fun i => s i * (s (pivotIndex s w hr))⁻¹) (fun i _ => (ratio_mem N s hs w hr i).1)
  have hGval' : w.evalAt (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) = ∑ i, evalVec s w i * a i := by
    rw [hGval]
    exact Finset.sum_congr rfl fun i _ => by rw [(ratio_mem N s hs w hr i).2.2, mul_comm]
  have hfactor : linSec s a = (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) * s (pivotIndex s w hr) := by
    rw [Finset.sum_mul]
    unfold linSec
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, inv_mul_cancel_right₀ (s_ne_zero N s hs _)]
  have hG0 : (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) ≠ 0 := by
    intro h0; apply ha; rw [hfactor, h0, zero_mul]
  have hZaw : Za w = w.ord (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) := by
    rw [hZa w, hfactor, w.ord_mul hG0 (s_ne_zero N s hs _), ord_pivot N s hs w hr]; ring
  refine ⟨hZaw ▸ w.ord_nonneg_of_mem hGmem, ?_⟩
  rw [hZaw, ← hGval']
  constructor
  · intro h0; exact w.evalAt_ne_zero hv hG0 h0
  · intro hne
    by_contra hne0
    have hpos : 0 < w.ord (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) :=
      lt_of_le_of_ne (w.ord_nonneg_of_mem hGmem) (Ne.symm hne0)
    apply hne
    rw [← evalAt_zero' w]
    exact w.evalAt_congr hGmem (zero_mem _) (Or.inr (by simpa using hpos))

theorem hypSec_nonneg (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hZa : ∀ w, Za w = w.ord (linSec s a) + embDivisor N w) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : 0 ≤ Za w :=
  (hypSec_facts N s hs a ha Za hZa w).1

theorem secVal_ne_zero_iff (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (k : ℕ) (u : modularFunctionFieldBar N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    secVal s w k u ≠ 0 ↔ B w = 0 := by
  classical
  have hr := r_pos N s hs
  have hv := isRational N w
  have hsv : secVal s w k u = w.evalAt (u * ((s (pivotIndex s w hr))⁻¹) ^ k) := by
    simp only [secVal, dif_pos hr]
  have hpk : ((s (pivotIndex s w hr))⁻¹) ^ k ≠ 0 := pow_ne_zero _ (inv_ne_zero (s_ne_zero N s hs _))
  have hne : u * ((s (pivotIndex s w hr))⁻¹) ^ k ≠ 0 := mul_ne_zero hu hpk
  have hord : w.ord (u * ((s (pivotIndex s w hr))⁻¹) ^ k) = B w := by
    rw [w.ord_mul hu hpk, ← zpow_natCast, w.ord_zpow, w.ord_inv, ord_pivot N s hs w hr, hB w]
    simp only [Finsupp.smul_apply, smul_eq_mul, neg_neg]
  have hBw : 0 ≤ B w := by
    rw [hB w]
    have := neg_le_ord_of_mem _ huL hu w
    simp only [Finsupp.smul_apply, smul_eq_mul] at this ⊢
    linarith
  have hmem : u * ((s (pivotIndex s w hr))⁻¹) ^ k ∈ w.toValuationSubring :=
    w.mem_of_ord_nonneg hne (hord ▸ hBw)
  rw [hsv, ← hord]
  constructor
  · intro h
    by_contra hne0
    have hpos : 0 < w.ord (u * ((s (pivotIndex s w hr))⁻¹) ^ k) :=
      lt_of_le_of_ne (w.ord_nonneg_of_mem hmem) (Ne.symm hne0)
    apply h
    rw [← evalAt_zero' w]
    exact w.evalAt_congr hmem (zero_mem _) (Or.inr (by simpa using hpos))
  · intro h0
    exact w.evalAt_ne_zero hv hne h0

end L2
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace PLBALG

set_option maxHeartbeats 6400000 in

theorem exists_mem_riemannRochSpace_ord_add_eq_one (N : ℕ) [NeZero N]
    (w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) :
    ∃ f : modularFunctionFieldBar N, f ≠ 0 ∧ f ∈ riemannRochSpace (embDivisor N) ∧ w.ord f + embDivisor N w = 1 := by
  classical
  set g : ℕ := genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) with hg
  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.essFiniteType_modularFunctionFieldBar N
  haveI hcan : AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  haveI : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  obtain ⟨x, hx⟩ := AlgebraicCurve.exists_D_ne_zero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))
  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.functionFieldRiemannRoch_modularFunctionFieldBar N
  have hgen : (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) = g := by
    exact_mod_cast ModularCurve.genus_eq_genusFF_modularFunctionFieldBar N
  have hK := ModularCurve.degree_canonicalDivisorOf_modularFunctionFieldBar N hx
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), (v.deg : ℤ) = 1 := fun v => by
    exact_mod_cast ModularCurve.deg_eq_one_modularFunctionFieldBar N v
  have hdegE : (embDivisor N).degree = 2 * g + 1 := by
    simp only [embDivisor, embDegree, map_zsmul, Divisor.degree_single, hdeg1, smul_eq_mul, mul_one]
    rw [hg]; push_cast; ring
  set D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := embDivisor N - Finsupp.single w 1 with hD₁
  set D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := embDivisor N - Finsupp.single w 2 with hD₂
  have hdeg₁ : D₁.degree = 2 * g := by rw [hD₁, map_sub, hdegE, Divisor.degree_single, hdeg1]; ring
  have hdeg₂ : D₂.degree = 2 * g - 1 := by rw [hD₂, map_sub, hdegE, Divisor.degree_single, hdeg1]; ring
  have hell₁ : (ell D₁ : ℤ) = g + 1 := by
    have h := hRR hx D₁
    have h0 : ell (AlgebraicCurve.canonicalDivisorOf hx - D₁) = 0 :=
      AlgebraicCurve.ell_eq_zero_of_degree_neg (by rw [map_sub, hK, hdeg₁, hgen]; omega)
    rw [h0, hdeg₁, hgen] at h
    push_cast at h
    linarith
  have hell₂ : (ell D₂ : ℤ) = g := by
    have h := hRR hx D₂
    have h0 : ell (AlgebraicCurve.canonicalDivisorOf hx - D₂) = 0 :=
      AlgebraicCurve.ell_eq_zero_of_degree_neg (by rw [map_sub, hK, hdeg₂, hgen]; omega)
    rw [h0, hdeg₂, hgen] at h
    push_cast at h
    linarith
  have hD₁w : D₁ w = embDivisor N w - 1 := by simp [hD₁]
  have hD₂w : D₂ w = embDivisor N w - 2 := by simp [hD₂]
  have hD₁v : ∀ v, v ≠ w → D₁ v = embDivisor N v := fun v hv => by simp [hD₁, Finsupp.single_apply, Ne.symm hv]
  have hD₂v : ∀ v, v ≠ w → D₂ v = embDivisor N v := fun v hv => by simp [hD₂, Finsupp.single_apply, Ne.symm hv]
  have hle : riemannRochSpace D₂ ≤ riemannRochSpace D₁ := by
    refine AlgebraicCurve.lSpace_mono (fun v => ?_)
    by_cases hv : v = w
    · subst hv; rw [hD₁w, hD₂w]; omega
    · rw [hD₁v v hv, hD₂v v hv]
  have hlt : riemannRochSpace D₂ < riemannRochSpace D₁ := by
    refine Submodule.lt_of_le_of_finrank_lt_finrank hle ?_
    have e1 : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D₁) = ell D₁ := rfl
    have e2 : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace D₂) = ell D₂ := rfl
    rw [e1, e2]
    omega
  obtain ⟨f, hf₁, hf₂⟩ := SetLike.exists_of_lt hlt
  have hf0 : f ≠ 0 := by rintro rfl; exact hf₂ (zero_mem _)
  refine ⟨f, hf0, AlgebraicCurve.lSpace_mono (fun v => ?_) hf₁, ?_⟩
  · by_cases hv : v = w
    · subst hv; rw [hD₁w]; omega
    · rw [hD₁v v hv]
  · rw [mem_riemannRochSpace_iff] at hf₁ hf₂
    push_neg at hf₂
    obtain ⟨v, -, hv⟩ := hf₂
    have h1 := (hf₁ w).resolve_left hf0
    rw [hD₁w] at h1
    by_cases hvw : v = w
    · subst hvw
      rw [hD₂w] at hv
      omega
    · have := (hf₁ v).resolve_left hf0
      rw [hD₁v v hvw] at this
      rw [hD₂v v hvw] at hv
      omega

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem linSec_add (s : Fin r → modularFunctionFieldBar N) (a b : Fin r → AlgebraicClosure ℚ) :
    linSec s (a + b) = linSec s a + linSec s b := by
  unfold linSec
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem linSec_smul (s : Fin r → modularFunctionFieldBar N) (t : AlgebraicClosure ℚ) (a : Fin r → AlgebraicClosure ℚ) :
    linSec s (t • a) = t • linSec s a := by
  unfold linSec
  simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]

theorem ord_algebraMap_eq_zero (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) :
    w.ord (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) = 0 := by
  have h1 := w.ord_nonneg_of_mem (w.algebraMap_mem' c)
  have h2 := w.ord_nonneg_of_mem (w.algebraMap_mem' c⁻¹)
  rw [map_inv₀, w.ord_inv] at h2
  omega

theorem ord_smul_eq (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {t : AlgebraicClosure ℚ} (ht : t ≠ 0) {G : modularFunctionFieldBar N} (hG : G ≠ 0) :
    w.ord (t • G) = w.ord G := by
  rw [Algebra.smul_def, w.ord_mul ((map_ne_zero _).mpr ht) hG, ord_algebraMap_eq_zero w ht, zero_add]

theorem ord_neg_eq (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (G : modularFunctionFieldBar N) :
    w.ord (-G) = w.ord G := by
  rcases eq_or_ne G 0 with rfl | hG
  · simp
  · have : -G = (-1 : AlgebraicClosure ℚ) • G := by simp
    rw [this, ord_smul_eq w (by norm_num) hG]

theorem subsingleton_bad_param (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {F G : modularFunctionFieldBar N} (hF : F ≠ 0) {m : ℤ} (hFm : w.ord F = m)
    (hG : G = 0 ∨ m ≤ w.ord G) :
    Set.Subsingleton {t : AlgebraicClosure ℚ | F + t • G = 0 ∨ m < w.ord (F + t • G)} := by
  intro t₁ h₁ t₂ h₂
  by_contra hne
  simp only [Set.mem_setOf_eq] at h₁ h₂

  have hG0 : G ≠ 0 := by
    rintro rfl
    simp only [smul_zero, add_zero] at h₁
    rcases h₁ with h | h
    · exact hF h
    · omega
  have hGm : m ≤ w.ord G := hG.resolve_left hG0

  have hsub : ∀ {t : AlgebraicClosure ℚ}, t ≠ 0 → w.ord (t • G) = w.ord G := fun ht => ord_smul_eq w ht hG0

  have step : ∀ {t t' : AlgebraicClosure ℚ}, t ≠ t' →
      (F + t • G = 0 ∨ m < w.ord (F + t • G)) → (F + t' • G = 0 ∨ m < w.ord (F + t' • G)) → m < w.ord G := by
    intro t t' htt h h'
    have hD : (F + t • G) - (F + t' • G) = (t - t') • G := by rw [sub_smul]; abel
    have htt' : t - t' ≠ 0 := sub_ne_zero.mpr htt

    have zero_case : ∀ {t t' : AlgebraicClosure ℚ}, t ≠ t' → F + t • G = 0 →
        (F + t' • G = 0 ∨ m < w.ord (F + t' • G)) → m < w.ord G := by
      intro t t' htt hz h'
      have hF' : F = -(t • G) := eq_neg_of_add_eq_zero_left hz
      have ht0 : t ≠ 0 := by
        rintro rfl; apply hF; rw [hF', Algebra.smul_def, map_zero, zero_mul, neg_zero]
      have h3 : F + t' • G = (t' - t) • G := by rw [hF', sub_smul]; abel
      have h4 : w.ord F = w.ord G := by rw [hF', ord_neg_eq, hsub ht0]
      rcases h' with hz' | hpos'
      · rw [h3] at hz'
        exact absurd (smul_eq_zero.mp hz') (not_or.mpr ⟨sub_ne_zero.mpr htt.symm, hG0⟩)
      · rw [h3, hsub (sub_ne_zero.mpr htt.symm)] at hpos'
        linarith
    by_cases hz : F + t • G = 0
    · exact zero_case htt hz h'
    by_cases hz' : F + t' • G = 0
    · exact zero_case htt.symm hz' h
    have hpos : m < w.ord (F + t • G) := h.resolve_left hz
    have hpos' : m < w.ord (F + t' • G) := h'.resolve_left hz'
    have hne3 : (F + t • G) + -(F + t' • G) ≠ 0 := by
      rw [← sub_eq_add_neg, hD]; exact smul_ne_zero htt' hG0
    have key := w.min_ord_le_ord_add hz (neg_ne_zero.mpr hz') hne3
    rw [← sub_eq_add_neg, hD, hsub htt', ord_neg_eq] at key
    have hmin : m < min (w.ord (F + t • G)) (w.ord (F + t' • G)) := lt_min hpos hpos'
    linarith
  have hGgt : m < w.ord G := step hne h₁ h₂

  rcases h₁ with h0 | hpos
  · have hF' : F = -(t₁ • G) := eq_neg_of_add_eq_zero_left h0
    have ht₁ : t₁ ≠ 0 := by
      rintro rfl; apply hF; rw [hF', Algebra.smul_def, map_zero, zero_mul, neg_zero]
    rw [hF', ord_neg_eq, hsub ht₁] at hFm
    linarith
  · by_cases ht₁ : t₁ = 0
    · rw [ht₁, Algebra.smul_def, map_zero, zero_mul, add_zero] at hpos
      linarith
    · have hne1 : F + t₁ • G ≠ 0 := by
        intro h; rw [h, Place.ord_zero] at hpos
        have : F = -(t₁ • G) := eq_neg_of_add_eq_zero_left h
        rw [this, ord_neg_eq, hsub ht₁] at hFm
        linarith
      have hF' : F = (F + t₁ • G) + -(t₁ • G) := by abel
      have key := w.min_ord_le_ord_add hne1 (neg_ne_zero.mpr (smul_ne_zero ht₁ hG0)) (by rw [← hF']; exact hF)
      rw [← hF', ord_neg_eq, hsub ht₁, hFm] at key
      have hmin : m < min (w.ord (F + t₁ • G)) (w.ord G) := lt_min hpos hGgt
      linarith

theorem dot_single (x : Fin r → AlgebraicClosure ℚ) (j : Fin r) (c : AlgebraicClosure ℚ) :
    L2lin.dot x (Pi.single j c) = x j * c := by
  classical
  simp only [L2lin.dot, Pi.single_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

theorem exists_dot_eq_zero_dot_ne (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hvw : v ≠ w) :
    ∃ e : Fin r → AlgebraicClosure ℚ, L2lin.dot (evalVec s v) e = 0 ∧ L2lin.dot (evalVec s w) e ≠ 0 := by
  classical
  have hch := ModularCurve.JZero.chordVec_ne_zero_of_ne N s hs v w hvw
  obtain ⟨p, hp⟩ : ∃ p : Fin r × Fin r, chordVec s v w p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hch (funext h)
  simp only [chordVec] at hp
  refine ⟨Pi.single p.1 (evalVec s v p.2) + Pi.single p.2 (-evalVec s v p.1), ?_, ?_⟩
  · rw [L2lin.dot_add, dot_single, dot_single]
    ring
  · rw [L2lin.dot_add, dot_single, dot_single]
    intro h0
    apply hp
    linear_combination -h0

theorem exists_pinned (s : Fin r → modularFunctionFieldBar N) (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0) :
    ∃ Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∀ w, Za w = w.ord (linSec s a) + embDivisor N w := by
  have hcurve := ModularCurve.isCurveOver_modularFunctionFieldBar N
  obtain ⟨D, hD, -⟩ := hcurve.toHasPrincipalDivisors.exists_divisor _ ha
  exact ⟨D + embDivisor N, fun w => by rw [Finsupp.add_apply, hD]⟩

theorem exists_admissible (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
      (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
      (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) := by
  classical

  obtain ⟨f₁, hf₁0, hf₁E, hf₁ord⟩ := exists_mem_riemannRochSpace_ord_add_eq_one N v
  have hf₁span : f₁ ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by rw [hs.2]; exact hf₁E
  obtain ⟨c₁, hc₁⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hf₁span
  have hF : linSec s c₁ = f₁ := hc₁

  set T' := (T ∪ B.support).filter (· ≠ v) with hT'

  obtain ⟨e, hev, heT⟩ := L2lin.exists_avoid (evalVec s v) (T'.image (evalVec s)) (by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact exists_dot_eq_zero_dot_ne s hs v w (Ne.symm (Finset.mem_filter.mp hw).2))

  set m : ℤ := 1 - embDivisor N v with hm
  have hFm : v.ord (linSec s c₁) = m := by rw [hF, hm]; linarith
  have hGv : linSec s e = 0 ∨ m ≤ v.ord (linSec s e) := by
    by_cases he0 : linSec s e = 0
    · exact Or.inl he0
    · right
      obtain ⟨Ze, hZe⟩ := exists_pinned s e he0
      have hfacts := L2.hypSec_facts N s hs e he0 Ze hZe v
      have hZev : Ze v ≠ 0 := fun h => (hfacts.2.1 h) (by simpa [L2lin.dot, mul_comm] using hev)
      have h0 := hfacts.1
      rw [hZe v] at hZev h0
      have : 0 < v.ord (linSec s e) + embDivisor N v := lt_of_le_of_ne h0 (Ne.symm hZev)
      rw [hm]; linarith
  have hbad₁ := (subsingleton_bad_param v (hF ▸ hf₁0) hFm hGv).finite
  set bad : Finset (AlgebraicClosure ℚ) :=
    hbad₁.toFinset ∪ T'.image (fun w => -(L2lin.dot (evalVec s w) c₁) / L2lin.dot (evalVec s w) e) with hbad
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad

  set a : Fin r → AlgebraicClosure ℚ := c₁ + t • e with ha_def
  have hlin : linSec s a = linSec s c₁ + t • linSec s e := by rw [ha_def, linSec_add, linSec_smul]
  have hgood₁ : ¬ (linSec s c₁ + t • linSec s e = 0 ∨ m < v.ord (linSec s c₁ + t • linSec s e)) := by
    intro h
    apply ht
    rw [hbad, Finset.mem_union]
    left
    exact hbad₁.mem_toFinset.mpr h
  push_neg at hgood₁
  have ha0 : linSec s a ≠ 0 := by rw [hlin]; exact hgood₁.1
  obtain ⟨Za, hZa⟩ := exists_pinned s a ha0
  have Sa := fun w => L2.hypSec_facts N s hs a ha0 Za hZa w

  have hav : ∑ i, evalVec s v i * a i = 0 := by
    have h1 : L2lin.dot (evalVec s v) c₁ = 0 := by

      obtain ⟨Z₁, hZ₁⟩ := exists_pinned s c₁ (hF ▸ hf₁0)
      have h := (L2.hypSec_facts N s hs c₁ (hF ▸ hf₁0) Z₁ hZ₁ v).2
      by_contra hne
      have hZ₁v : Z₁ v = 0 := h.2 (by simpa [L2lin.dot] using hne)
      rw [hZ₁ v, hF] at hZ₁v
      linarith
    have : L2lin.dot (evalVec s v) a = 0 := by rw [ha_def, L2lin.dot_add, L2lin.dot_smul, h1, hev]; ring
    simpa [L2lin.dot] using this

  have hZav : Za v = 1 := by
    rw [hZa v, hlin]
    have hle := hgood₁.2
    have hge : m ≤ v.ord (linSec s c₁ + t • linSec s e) := by
      have h0 := (Sa v).1
      have hZv : Za v ≠ 0 := fun h => ((Sa v).2.1 h) hav
      have h1 : 1 ≤ Za v := by omega
      rw [hZa v, hlin] at h1
      rw [hm]; linarith
    rw [hm] at hle hge
    linarith

  have hmiss : ∀ w ∈ T', Za w = 0 := by
    intro w hw
    apply (Sa w).2.2
    have hwe : L2lin.dot (evalVec s w) e ≠ 0 := heT _ (Finset.mem_image_of_mem _ hw)
    have hne : L2lin.dot (evalVec s w) a ≠ 0 := by
      rw [ha_def, L2lin.dot_add, L2lin.dot_smul]
      intro h0
      apply ht
      rw [hbad, Finset.mem_union]
      right
      refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
      rw [eq_comm, eq_div_iff hwe]
      linear_combination h0
    simpa [L2lin.dot] using hne
  refine ⟨a, Za, ha0, hZa, hav, hZav, fun w hw hwv => hmiss w ?_, fun w hwv => ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hw, hwv⟩
  · by_cases hBw : B w = 0
    · exact Or.inr hBw
    · exact Or.inl (hmiss w (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hBw), hwv⟩))

theorem sum_sub_single (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (f : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ) (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ((Z - Finsupp.single v (1 : ℤ)).sum fun y n => (n : ℝ) * f y) = (Z.sum fun y n => (n : ℝ) * f y) - f v := by
  classical
  rw [Finsupp.sum_sub_index (fun y b₁ b₂ => by push_cast; ring), Finsupp.sum_single_index (by simp)]
  simp

theorem sum_cast_sub_single_eq (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hZa : ∀ w, Za w = w.ord (linSec s a) + embDivisor N w) (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ((Za - Finsupp.single v (1 : ℤ)).sum fun _ n => (n : ℝ)) = (embDegree N : ℝ) - 1 := by
  classical
  have h1 := sum_sub_single Za (fun _ => (1 : ℝ)) v
  simp only [mul_one] at h1
  rw [h1]
  congr 1
  have hd := ModularCurve.JZero.sum_toNat_hyperplaneSection_eq_embDegree N s hs a ha Za hZa
  have hnn := L2.hypSec_nonneg N s hs a ha Za hZa
  rw [← hd]
  simp only [Finsupp.sum]
  push_cast
  exact Finset.sum_congr rfl fun w _ => by rw [← Int.cast_natCast, Int.toNat_of_nonneg (hnn w)]

theorem exists_eq_algebraMap_of_mem (u : modularFunctionFieldBar N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace (((0 : ℕ) : ℤ) • embDivisor N)) :
    ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ u = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c := by
  classical
  have hcurve := ModularCurve.isCurveOver_modularFunctionFieldBar N
  have hreg : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ w.ord u := by
    intro w
    have := L2.neg_le_ord_of_mem _ huL hu w
    simpa using this
  set v₀ := cuspInftyBar N with hv₀
  set cst : AlgebraicClosure ℚ := v₀.evalAt u with hcst
  set g : modularFunctionFieldBar N := u - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) cst with hg
  by_cases hg0 : g = 0
  · have hu' : u = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) cst := sub_eq_zero.mp hg0
    refine ⟨cst, ?_, hu'⟩
    rintro h0
    apply hu
    rw [hu', h0, map_zero]
  · exfalso
    have hgreg : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), g ∈ w.toValuationSubring :=
      fun w => sub_mem (w.mem_of_ord_nonneg hu (hreg w)) (w.algebraMap_mem' cst)
    have hrat := L2.isRational N v₀
    have hval : v₀.evalAt g = 0 := by
      have h1 : v₀.evalAt u = v₀.evalAt (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) cst + g) := by
        congr 1
        rw [hg]
        ring
      rw [L2.evalAt_add' v₀ hrat (v₀.algebraMap_mem' cst) (hgreg v₀), v₀.evalAt_algebraMap, ← hcst] at h1
      have h2 : cst + v₀.evalAt g = cst + 0 := by rw [add_zero]; exact h1.symm
      exact add_left_cancel h2
    have hgv₀ : 0 < v₀.ord g := by
      rcases eq_or_lt_of_le (v₀.ord_nonneg_of_mem (hgreg v₀)) with h0 | hpos
      · exact absurd hval (v₀.evalAt_ne_zero hrat hg0 h0.symm)
      · exact hpos
    obtain ⟨D, hD, hdeg⟩ := hcurve.toHasPrincipalDivisors.exists_divisor g hg0
    have hDnn : ∀ w, 0 ≤ D w := fun w => by rw [hD w]; exact w.ord_nonneg_of_mem (hgreg w)
    have hdeg' : Divisor.degree D = D.sum fun w n => n := by
      rw [Divisor.degree, Finsupp.liftAddHom_apply]
      refine Finsupp.sum_congr fun w _ => ?_
      simp [ModularCurve.deg_eq_one_modularFunctionFieldBar N w]
    have hmem : v₀ ∈ D.support := by
      rw [Finsupp.mem_support_iff, hD]
      exact hgv₀.ne'
    have hle : D v₀ ≤ D.sum fun w n => n := by
      simp only [Finsupp.sum]
      exact Finset.single_le_sum (fun w _ => hDnn w) hmem
    rw [← hdeg', hdeg, hD] at hle
    exact absurd hle (not_le.mpr hgv₀)

theorem secVal_zero_algebraMap (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (c : AlgebraicClosure ℚ) :
    secVal s y 0 (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) = c := by
  classical
  simp only [secVal, dif_pos (L2.r_pos N s hs), pow_zero, mul_one]
  exact y.evalAt_algebraMap c

theorem body_k0 (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (σ : AlgebraicClosure ℚ →+* ℂ)
    (c₀ : ℝ) (u : modularFunctionFieldBar N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((((0 : ℕ) : ℤ)) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (v y₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
      (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
      (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
      ((embDegree N : ℝ) - 1) * (Real.log ‖σ (secVal s y₀ 0 u)‖ - ((0 : ℕ) : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y₀ i)‖))
          - c₀ * ((0 : ℕ) : ℝ)
        ≤ (Za - Finsupp.single v (1 : ℤ)).sum
            (fun y n => (n : ℝ) * (Real.log ‖σ (secVal s y 0 u)‖ - ((0 : ℕ) : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖))) := by
  classical
  obtain ⟨a, Za, ha, hZa, hav, hZav, hT, hB⟩ := exists_admissible s hs B T v
  obtain ⟨cu, hcu0, hu_eq⟩ := exists_eq_algebraMap_of_mem u hu huL
  refine ⟨a, Za, ha, hZa, hav, hZav, hT, hB, ?_⟩
  have hconst : ∀ y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (Real.log ‖σ (secVal s y 0 u)‖ - ((0 : ℕ) : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖)) = Real.log ‖σ cu‖ := by
    intro y
    rw [hu_eq, secVal_zero_algebraMap s hs]
    simp
  simp only [hconst]
  rw [show ((Za - Finsupp.single v (1 : ℤ)).sum fun y n => (n : ℝ) * Real.log ‖σ cu‖)
      = ((Za - Finsupp.single v (1 : ℤ)).sum fun _ n => (n : ℝ)) * Real.log ‖σ cu‖ by
    simp only [Finsupp.sum, Finset.sum_mul]]
  rw [sum_cast_sub_single_eq s hs a ha Za hZa v]
  simp

end PLBALG
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

section PUREANA
open MeasureTheory Metric Set

namespace PLBANA

variable {W : Set ℂ} {F : ℂ → ℂ} {G : ℂ → ℝ} {k S : ℝ}

def psi (F : ℂ → ℂ) (G : ℂ → ℝ) (k : ℝ) (z : ℂ) : ℝ := Real.log ‖F z‖ - k * G z

def psiC (F : ℂ → ℂ) (G : ℂ → ℝ) (k S : ℝ) (z : ℂ) : ℝ := min (psi F G k z - S) 0

theorem psiC_le_zero (z : ℂ) : psiC F G k S z ≤ 0 := min_le_right _ _

theorem psiC_le (z : ℂ) : psiC F G k S z ≤ psi F G k z - S := min_le_left _ _

theorem psiC_eq_of_le {z : ℂ} (h : psi F G k z ≤ S) : psiC F G k S z = psi F G k z - S :=
  min_eq_left (by linarith)

structure Setup (W : Set ℂ) (F : ℂ → ℂ) (G : ℂ → ℝ) (k S : ℝ) : Prop where
  isOpen : IsOpen W
  preconn : IsPreconnected W
  anal : AnalyticOnNhd ℂ F W
  cont : ContinuousOn G W
  hk : 0 ≤ k
  le_S : ∀ z ∈ W, F z ≠ 0 → psi F G k z ≤ S
  nontriv : ∃ z ∈ W, F z ≠ 0

namespace Setup

theorem volume_zero_set (h : Setup W F G k S) : volume (W ∩ {z | F z = 0}) = 0 := by
  obtain ⟨x, hxW, hx⟩ := h.nontriv
  have hconn : IsConnected W := ⟨⟨x, hxW⟩, h.preconn⟩
  have hcod : F ⁻¹' {0}ᶜ ∈ Filter.codiscreteWithin W :=
    h.anal.preimage_zero_mem_codiscreteWithin hx hxW hconn
  have hae : ∀ᵐ w ∂(volume.restrict W), F w ≠ 0 :=
    ae_restrict_le_codiscreteWithin h.isOpen.measurableSet hcod
  have h1 : volume.restrict W {w | F w = 0} = 0 := by
    have := ae_iff.1 hae
    simpa only [ne_eq, not_not] using this
  rw [Measure.restrict_apply' h.isOpen.measurableSet] at h1
  rwa [Set.inter_comm] at h1

theorem volume_inter_zero_set (h : Setup W F G k S) {T : Set ℂ} (hT : T ⊆ W) :
    volume (T ∩ {z | F z = 0}) = 0 :=
  measure_mono_null (Set.inter_subset_inter_left _ hT) h.volume_zero_set

theorem psiC_ae_eq (h : Setup W F G k S) {T : Set ℂ} (hT : T ⊆ W) (hTm : MeasurableSet T) :
    (fun z => psiC F G k S z) =ᵐ[volume.restrict T] fun z => psi F G k z - S := by
  have h0 : volume.restrict T {z | F z = 0} = 0 := by
    rw [Measure.restrict_apply' hTm, Set.inter_comm]
    exact h.volume_inter_zero_set hT
  have hae : ∀ᵐ z ∂(volume.restrict T), F z ≠ 0 := by
    rw [ae_iff]; simpa only [ne_eq, not_not] using h0
  have hT' : ∀ᵐ z ∂(volume.restrict T), z ∈ T := ae_restrict_mem hTm
  filter_upwards [hae, hT'] with z hz hzT
  exact psiC_eq_of_le (h.le_S z (hT hzT) hz)

theorem volume_inter_ne_zero_ge (h : Setup W F G k S) {T : Set ℂ} (hT : T ⊆ W) :
    volume T ≤ volume (T ∩ {z | F z ≠ 0}) := by
  have hsplit : T ⊆ (T ∩ {z | F z ≠ 0}) ∪ (T ∩ {z | F z = 0}) := by
    intro z hz
    by_cases h0 : F z = 0
    · exact Or.inr ⟨hz, h0⟩
    · exact Or.inl ⟨hz, h0⟩
  calc volume T ≤ volume (T ∩ {z | F z ≠ 0}) + volume (T ∩ {z | F z = 0}) :=
        (measure_mono hsplit).trans (measure_union_le _ _)
    _ = volume (T ∩ {z | F z ≠ 0}) := by rw [h.volume_inter_zero_set hT, add_zero]

theorem integrableOn_ball (h : Setup W F G k S) {p : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall p ρ ⊆ W) (hp : F p ≠ 0) :
    IntegrableOn (psi F G k) (ball p ρ) ∧ IntegrableOn (psiC F G k S) (ball p ρ) := by
  have hF : AnalyticOnNhd ℂ F (closedBall p ρ) := h.anal.mono hsub
  have hlog : IntegrableOn (fun z => Real.log ‖F z‖) (ball p ρ) :=
    AnalyticOnNhd.integrableOn_log_norm_ball hF hp
  have hGc : ContinuousOn G (closedBall p ρ) := h.cont.mono hsub
  have hG : IntegrableOn G (ball p ρ) :=
    (hGc.integrableOn_compact (isCompact_closedBall p ρ)).mono_set ball_subset_closedBall
  have hpsi : IntegrableOn (psi F G k) (ball p ρ) := hlog.sub (hG.const_mul k)
  refine ⟨hpsi, ?_⟩
  have hfin : volume (ball p ρ) < ⊤ := measure_ball_lt_top
  have h1 : IntegrableOn (fun z => psi F G k z - S) (ball p ρ) := hpsi.sub (integrableOn_const hfin.ne)
  have h2 : IntegrableOn (fun _ : ℂ => (0 : ℝ)) (ball p ρ) := integrableOn_const hfin.ne
  have h3 := Integrable.inf h1 h2
  refine h3.congr ?_
  exact Filter.Eventually.of_forall fun z => rfl

theorem volumeReal_ball (p : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) : volume.real (ball p ρ) = Real.pi * ρ ^ 2 := by
  rw [measureReal_def, Complex.volume_ball, ENNReal.toReal_mul, ← ENNReal.ofReal_pow hρ, ENNReal.toReal_ofReal (by positivity)]
  simp [mul_comm]

theorem volumeReal_ball_pos (p : ℂ) {ρ : ℝ} (hρ : 0 < ρ) : 0 < volume.real (ball p ρ) := by
  rw [volumeReal_ball p hρ.le]; positivity

theorem smv_integral (h : Setup W F G k S) {p : ℂ} {ρ m_lo m_hi : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall p ρ ⊆ W) (hp : F p ≠ 0)
    (hlo : ∀ z ∈ closedBall p ρ, m_lo ≤ G z) (hhi : ∀ z ∈ closedBall p ρ, G z ≤ m_hi) :
    (psi F G k p - S - k * (m_hi - m_lo)) * volume.real (ball p ρ)
      ≤ ∫ z in ball p ρ, psiC F G k S z := by
  have hF : AnalyticOnNhd ℂ F (closedBall p ρ) := h.anal.mono hsub
  have hGc : ContinuousOn G (closedBall p ρ) := h.cont.mono hsub
  have hJ := AnalyticOnNhd.log_norm_sub_mul_le_setAverage_ball (k := k) (M := m_hi) hF hp hρ hGc hhi h.hk

  have hV := volumeReal_ball_pos p hρ
  obtain ⟨hpsi, hpsiC⟩ := h.integrableOn_ball hρ hsub hp
  rw [setAverage_eq, smul_eq_mul] at hJ
  have hJ' : (Real.log ‖F p‖ - k * m_hi) * volume.real (ball p ρ) ≤ ∫ z in ball p ρ, psi F G k z := by
    have h2 := (le_inv_mul_iff₀ hV).mp hJ
    rw [mul_comm]
    exact h2

  have hIC : ∫ z in ball p ρ, psiC F G k S z = (∫ z in ball p ρ, psi F G k z) - S * volume.real (ball p ρ) := by
    rw [integral_congr_ae (h.psiC_ae_eq (ball_subset_closedBall.trans hsub) measurableSet_ball),
      integral_sub hpsi (integrableOn_const measure_ball_lt_top.ne), setIntegral_const, smul_eq_mul, mul_comm]
  rw [hIC]
  have hGp : m_lo ≤ G p := hlo p (mem_closedBall_self hρ.le)
  have hk := h.hk
  have h1 : psi F G k p - k * (m_hi - m_lo) ≤ Real.log ‖F p‖ - k * m_hi := by
    unfold psi; nlinarith
  nlinarith

theorem smv_average (h : Setup W F G k S) {p : ℂ} {ρ m_lo m_hi : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall p ρ ⊆ W) (hp : F p ≠ 0)
    (hlo : ∀ z ∈ closedBall p ρ, m_lo ≤ G z) (hhi : ∀ z ∈ closedBall p ρ, G z ≤ m_hi) :
    psiC F G k S p - k * (m_hi - m_lo) ≤ ⨍ z in ball p ρ, psiC F G k S z := by
  have hV := volumeReal_ball_pos p hρ
  have hI := h.smv_integral hρ hsub hp hlo hhi
  rw [setAverage_eq, smul_eq_mul]
  rw [le_inv_mul_iff₀ hV]
  have hle : psiC F G k S p ≤ psi F G k p - S := psiC_le p
  nlinarith

theorem volume_bad_le (h : Setup W F G k S) {T : Set ℂ} (hT : T ⊆ W) (hTm : MeasurableSet T)
    (hTfin : volume T ≠ ⊤) (hint : IntegrableOn (psiC F G k S) T) {I : ℝ}
    (hI : I ≤ ∫ z in T, psiC F G k S z) {lam : ℝ} (hlam : 0 < lam) :
    volume (T ∩ {z | ‖F z‖ ≤ Real.exp (S - lam + k * G z)}) ≤ ENNReal.ofReal ((-I) / lam) := by
  set μ : Measure ℂ := volume.restrict T with hμ
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hTfin.lt_top⟩
  set f : ℂ → ℝ := fun z => - psiC F G k S z with hf
  have hf0 : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun z => by
    show (0 : ℝ) ≤ - psiC F G k S z
    have := psiC_le_zero (F := F) (G := G) (k := k) (S := S) z
    linarith
  have hfint : Integrable f μ := hint.neg
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hf0 hfint lam
  have hintf : ∫ z, f z ∂μ = - ∫ z in T, psiC F G k S z := by
    rw [hf, integral_neg]
  have hreal : μ.real {z | lam ≤ f z} ≤ (-I) / lam := by
    rw [le_div_iff₀ hlam, mul_comm]
    linarith
  have hsplit : T ∩ {z | ‖F z‖ ≤ Real.exp (S - lam + k * G z)} ⊆ ({z | lam ≤ f z} ∩ T) ∪ (T ∩ {z | F z = 0}) := by
    rintro z ⟨hzT, hz⟩
    by_cases h0 : F z = 0
    · exact Or.inr ⟨hzT, h0⟩
    · refine Or.inl ⟨?_, hzT⟩
      have hpos : 0 < ‖F z‖ := norm_pos_iff.2 h0
      have hlog : Real.log ‖F z‖ ≤ S - lam + k * G z := by
        have := Real.log_le_log hpos hz
        rwa [Real.log_exp] at this
      have hψ : psi F G k z - S ≤ -lam := by unfold psi; linarith
      have hC : psiC F G k S z = psi F G k z - S := psiC_eq_of_le (by linarith)
      show lam ≤ - psiC F G k S z
      rw [hC]; linarith
  calc volume (T ∩ {z | ‖F z‖ ≤ Real.exp (S - lam + k * G z)})
      ≤ volume ({z | lam ≤ f z} ∩ T) + volume (T ∩ {z | F z = 0}) :=
        (measure_mono hsplit).trans (measure_union_le _ _)
    _ = μ {z | lam ≤ f z} := by rw [h.volume_inter_zero_set hT, add_zero, hμ, Measure.restrict_apply' hTm]
    _ = ENNReal.ofReal (μ.real {z | lam ≤ f z}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    _ ≤ ENNReal.ofReal ((-I) / lam) := ENNReal.ofReal_le_ofReal hreal

theorem volume_bad_ball_le (h : Setup W F G k S) {p : ℂ} {ρ m_lo m_hi A : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall p ρ ⊆ W) (hp : F p ≠ 0)
    (hlo : ∀ z ∈ closedBall p ρ, m_lo ≤ G z) (hhi : ∀ z ∈ closedBall p ρ, G z ≤ m_hi)
    (hA : S - A ≤ psi F G k p) {lam : ℝ} (hlam : 0 < lam) :
    volume (ball p ρ ∩ {z | ‖F z‖ ≤ Real.exp (S - lam + k * G z)})
      ≤ ENNReal.ofReal (volume.real (ball p ρ) * (A + k * (m_hi - m_lo)) / lam) := by
  have hI := h.smv_integral hρ hsub hp hlo hhi
  obtain ⟨-, hpsiC⟩ := h.integrableOn_ball hρ hsub hp
  have hb := h.volume_bad_le (ball_subset_closedBall.trans hsub) measurableSet_ball measure_ball_lt_top.ne hpsiC hI hlam
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  refine div_le_div_of_nonneg_right ?_ hlam.le
  have hV := (volumeReal_ball_pos p hρ).le
  nlinarith

theorem chain (h : Setup W F G k S) {δ m_lo m_hi A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (hosc : m_lo ≤ m_hi)
    (c : ℕ → ℂ) (L : ℕ)
    (hcW : ∀ l ≤ L, closedBall (c l) (4 * δ) ⊆ W)
    (hlo : ∀ l ≤ L, ∀ z ∈ closedBall (c l) (4 * δ), m_lo ≤ G z)
    (hhi : ∀ l ≤ L, ∀ z ∈ closedBall (c l) (4 * δ), G z ≤ m_hi)
    (hstep : ∀ l < L, dist (c l) (c (l + 1)) ≤ δ)
    {p₀ : ℂ} (hp₀ : dist p₀ (c 0) < δ) (hF₀ : F p₀ ≠ 0) (hψ₀ : S - A ≤ psi F G k p₀) :
    ∀ l ≤ L, ∃ p, dist p (c l) < δ ∧ F p ≠ 0 ∧
      S - (A + l * (k * (m_hi - m_lo))) * 9 ^ l ≤ psi F G k p := by
  set κ : ℝ := k * (m_hi - m_lo) with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg h.hk (by linarith)
  set Gl : ℕ → Set ℂ := fun l => ball (c l) δ ∩ {z | F z ≠ 0} with hGl
  set B : ℕ → ℂ → Set ℂ := fun _ p => ball p (3 * δ) with hB

  have hgeo1 : ∀ l ≤ L, ∀ p, dist p (c l) < δ → closedBall p (3 * δ) ⊆ closedBall (c l) (4 * δ) := by
    intro l hl p hp z hz
    rw [mem_closedBall] at hz ⊢
    calc dist z (c l) ≤ dist z p + dist p (c l) := dist_triangle _ _ _
      _ ≤ 3 * δ + δ := add_le_add hz hp.le
      _ = 4 * δ := by ring
  have hgeo2 : ∀ l < L, ∀ p, dist p (c l) < δ → ball (c (l + 1)) δ ⊆ ball p (3 * δ) := by
    intro l hl p hp z hz
    rw [mem_ball] at hz ⊢
    calc dist z p ≤ dist z (c (l + 1)) + dist (c (l + 1)) (c l) + dist (c l) p := dist_triangle4 _ _ _ _
      _ < δ + δ + δ := by
          have := hstep l hl
          rw [dist_comm] at this
          rw [dist_comm (c l) p]
          linarith
      _ = 3 * δ := by ring
  have hmain := MeasureTheory.exists_mem_le_of_setAverage_chain (μ := volume) (ψ := psiC F G k S) (G := Gl) (B := B)
    (L := L) (A₀ := A) (κ := κ) (θ := (1 / 9 : ℝ)) (by norm_num) (by norm_num) hκ0
    (fun l _ p _ => measurableSet_ball)
    (fun l _ p _ => (measure_ball_pos volume p (by linarith)).ne')
    (fun l _ p _ => measure_ball_lt_top.ne)
    (fun l _ p _ x _ => psiC_le_zero x)
    (fun l hl p hp => (h.integrableOn_ball (by linarith) ((hgeo1 l hl.le p (mem_ball.mp hp.1)).trans (hcW l hl.le)) hp.2).2)
    (fun l hl p hp => h.smv_average (by linarith) ((hgeo1 l hl.le p (mem_ball.mp hp.1)).trans (hcW l hl.le)) hp.2
      (fun z hz => hlo l hl.le z (hgeo1 l hl.le p (mem_ball.mp hp.1) hz))
      (fun z hz => hhi l hl.le z (hgeo1 l hl.le p (mem_ball.mp hp.1) hz)))
    ?_ (p₀ := p₀) ⟨mem_ball.mpr hp₀, hF₀⟩ ?_
  · intro l hl
    obtain ⟨p, hp, hbound⟩ := hmain l hl
    refine ⟨p, mem_ball.mp hp.1, hp.2, ?_⟩
    have h1 : psiC F G k S p ≤ psi F G k p - S := psiC_le p
    have h2 : -((A + l * κ) / (1 / 9 : ℝ) ^ l) = -((A + l * κ) * 9 ^ l) := by
      rw [one_div, inv_pow, div_inv_eq_mul]
    rw [h2] at hbound
    linarith
  ·
    intro l hl p hp
    have hpδ : dist p (c l) < δ := mem_ball.mp hp.1
    have hsubW : ball (c (l + 1)) δ ⊆ W :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans (hcW (l + 1) hl)
    have hincl : ball (c (l + 1)) δ ∩ {z | F z ≠ 0} ⊆ ball p (3 * δ) ∩ Gl (l + 1) := by
      rintro z ⟨hz, hFz⟩
      exact ⟨hgeo2 l hl p hpδ hz, hz, hFz⟩
    have hvol : volume (ball (c (l + 1)) δ) ≤ volume (ball p (3 * δ) ∩ Gl (l + 1)) :=
      (h.volume_inter_ne_zero_ge hsubW).trans (measure_mono hincl)
    have hfin : volume (ball p (3 * δ) ∩ Gl (l + 1)) ≠ ⊤ :=
      (measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top |>.ne
    have hreal : volume.real (ball (c (l + 1)) δ) ≤ volume.real (ball p (3 * δ) ∩ Gl (l + 1)) := by
      rw [measureReal_def, measureReal_def]
      exact (ENNReal.toReal_le_toReal measure_ball_lt_top.ne hfin).mpr hvol
    have hv1 := volumeReal_ball (c (l + 1)) hδ.le
    have hv3 := volumeReal_ball p (ρ := 3 * δ) (by linarith)
    show (1 / 9 : ℝ) * volume.real (ball p (3 * δ)) ≤ volume.real (ball p (3 * δ) ∩ Gl (l + 1))
    rw [hv3]
    rw [hv1] at hreal
    nlinarith
  ·
    have h1 : psiC F G k S p₀ = psi F G k p₀ - S := by
      by_cases hW : p₀ ∈ W
      · exact psiC_eq_of_le (h.le_S p₀ hW hF₀)
      · exfalso; exact hW ((hcW 0 (Nat.zero_le _)) (mem_closedBall.mpr (by linarith [hp₀.le])))
    rw [h1]; linarith

end Setup
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

end PLBANA
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

end PUREANA
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

section PURECUSP
open Complex Metric Set
open scoped Pointwise

namespace PLBCUSP

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) / (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ))

private theorem _root_.PLBCUSP.coe_smul_eq (γ : SL(2, ℤ)) (z : ℍ) : ((γ • z : ℍ) : ℂ) = mob γ z := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, algebraMap_int_eq, Complex.ofReal_intCast]

p2m_export "PLBCUSP" "coe_smul_eq"
theorem denom_ne (γ : SL(2, ℤ)) (z : ℍ) : ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← ModularGroup.denom_apply]; exact UpperHalfPlane.denom_ne_zero _ _

theorem differentiableAt_mob (γ : SL(2, ℤ)) (z : ℍ) : DifferentiableAt ℂ (mob γ) (z : ℂ) := by
  unfold mob
  refine DifferentiableAt.div ?_ ?_ (denom_ne γ z)
  · exact ((differentiableAt_const _).mul differentiableAt_id).add (differentiableAt_const _)
  · exact ((differentiableAt_const _).mul differentiableAt_id).add (differentiableAt_const _)

theorem coe_smul_ofComplex_eventuallyEq (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    (fun w : ℂ => ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) =ᶠ[𝓝 z] mob γ := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with w hw
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw, coe_smul_eq]

variable {U : ℂ → ℂ}

theorem differentiableAt_comp_smul (γ : SL(2, ℤ)) (hU : ∀ τ : ℍ, DifferentiableAt ℂ U (τ : ℂ)) {z : ℂ}
    (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun w : ℂ => U ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) z := by
  have h1 : (fun w : ℂ => U ((γ • UpperHalfPlane.ofComplex w : ℍ) : ℂ)) =ᶠ[𝓝 z] (U ∘ mob γ) :=
    (coe_smul_ofComplex_eventuallyEq γ hz).mono fun w hw => by
      show U _ = U (mob γ w)
      rw [← hw]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ h1
  refine DifferentiableAt.comp z ?_ (differentiableAt_mob γ ⟨z, hz⟩)
  have : mob γ z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := (coe_smul_eq γ ⟨z, hz⟩).symm
  rw [this]
  exact hU _

theorem qParam_add_nat (n : ℕ) (hn : 0 < n) (z : ℂ) :
    Function.Periodic.qParam n (z + n) = Function.Periodic.qParam n z := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Function.Periodic.qParam, Complex.ofReal_natCast]
  have e : 2 * (Real.pi : ℂ) * Complex.I * (z + n) / n = 2 * (Real.pi : ℂ) * Complex.I * z / n + 2 * Real.pi * Complex.I := by
    field_simp
  rw [e, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem periodic_qParam_zpow (n : ℕ) (hn : 0 < n) (m : ℤ) :
    Function.Periodic (fun z : ℂ => Function.Periodic.qParam n z ^ m) n := fun z => by
  show Function.Periodic.qParam n (z + n) ^ m = _
  rw [qParam_add_nat n hn z]

theorem differentiableAt_qParam_zpow (n : ℕ) (m : ℤ) (z : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => Function.Periodic.qParam n z ^ m) z := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => Function.Periodic.qParam n z) z := by
    simp only [Function.Periodic.qParam]
    exact (((differentiableAt_const _).mul differentiableAt_id).div_const _).cexp
  exact h1.zpow (Or.inl (by simp only [Function.Periodic.qParam]; exact Complex.exp_ne_zero _))

theorem im_invQParam_pos {h : ℝ} (hh : 0 < h) {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    0 < (Function.Periodic.invQParam h q).im := by
  rw [Function.Periodic.im_invQParam]
  have hlog : Real.log ‖q‖ < 0 := Real.log_neg (norm_pos_iff.mpr hq0) hq
  have h1 : -h / (2 * Real.pi) < 0 := by
    apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  exact mul_pos_of_neg_of_neg h1 hlog

theorem analyticOnNhd_cuspFunction {Γ : Subgroup SL(2, ℤ)}
    (hUinv : ∀ g ∈ Γ, ∀ τ : ℍ, U ((g • τ : ℍ) : ℂ) = U (τ : ℂ))
    (hU : ∀ τ : ℍ, DifferentiableAt ℂ U (τ : ℂ)) {γ : SL(2, ℤ)} {n : ℕ} (hn : 0 < n)
    (hconj : γ * ModularGroup.T ^ n * γ⁻¹ ∈ Γ) (m : ℤ)
    (hbdd : ∃ C A : ℝ, ∀ z : ℂ, A ≤ z.im →
      ‖U ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ) * Function.Periodic.qParam n z ^ (-m)‖ ≤ C) :
    AnalyticOnNhd ℂ (Function.Periodic.cuspFunction n
        (fun z : ℂ => U ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ) * Function.Periodic.qParam n z ^ (-m)))
      (Metric.ball 0 1) ∧
    ∀ q ∈ Metric.ball (0 : ℂ) 1, q ≠ 0 →
      Function.Periodic.cuspFunction n
          (fun z : ℂ => U ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ) * Function.Periodic.qParam n z ^ (-m)) q
        = U ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam n q) : ℍ) : ℂ) * q ^ (-m) := by
  set f : ℂ → ℂ := fun z => U ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ) * Function.Periodic.qParam n z ^ (-m)
    with hf
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn

  have hper1 : Function.Periodic (fun z : ℂ => U ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) n :=
    UpperHalfPlane.periodic_comp_smul_of_conj_T_pow_mem (F := fun τ : ℍ => U (τ : ℂ)) hUinv hconj
  have hper : Function.Periodic f n := by
    have := hper1.mul (periodic_qParam_zpow n hn (-m))
    exact this

  have hdiff : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ f z := fun z hz =>
    (differentiableAt_comp_smul γ hU hz).mul (differentiableAt_qParam_zpow n (-m) z)
  have hev : ∀ᶠ z : ℂ in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ f z := by
    have : {z : ℂ | 0 < z.im} ∈ Filter.comap Complex.im Filter.atTop :=
      Filter.preimage_mem_comap (Filter.Ioi_mem_atTop 0)
    exact Filter.mem_of_superset this fun z hz => hdiff z hz

  have hbd : (Filter.comap Complex.im Filter.atTop).BoundedAtFilter f := by
    obtain ⟨C, A, hCA⟩ := hbdd
    rw [Filter.BoundedAtFilter]
    refine Asymptotics.IsBigO.of_bound C ?_
    have : {z : ℂ | A ≤ z.im} ∈ Filter.comap Complex.im Filter.atTop :=
      Filter.preimage_mem_comap (Filter.Ici_mem_atTop A)
    filter_upwards [this] with z hz
    simp only [Pi.one_apply, norm_one, mul_one]
    exact hCA z hz
  have hdo : DifferentiableOn ℂ (Function.Periodic.cuspFunction n f) (Metric.ball 0 1) := by
    intro q hq
    rw [Metric.mem_ball, dist_zero_right] at hq
    by_cases hq0 : q = 0
    · subst hq0
      exact (Function.Periodic.differentiableAt_cuspFunction_zero hnpos hper hev hbd).differentiableWithinAt
    · have hz := im_invQParam_pos hnpos hq hq0
      have := Function.Periodic.differentiableAt_cuspFunction hn' hper (hdiff _ hz)
      rw [Function.Periodic.qParam_right_inv hn' hq0] at this
      exact this.differentiableWithinAt
  refine ⟨hdo.analyticOnNhd Metric.isOpen_ball, fun q hq hq0 => ?_⟩
  rw [Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  show U _ * Function.Periodic.qParam n _ ^ (-m) = _
  rw [Function.Periodic.qParam_right_inv hn' hq0]

theorem cuspFunction_zero_of_tendsto {h : ℝ} {f : ℂ → ℂ} {c : ℂ}
    (hc : Filter.Tendsto (Function.Periodic.cuspFunction h f) (𝓝[≠] 0) (𝓝 c)) :
    Function.Periodic.cuspFunction h f 0 = c := by
  rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]; exact hc.limUnder_eq

theorem exists_nat_of_mem_strictPeriods (N : ℕ) (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w)
    (hΓ : w ∈ (ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ •
      (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) = w ∧ γ * ModularGroup.T ^ n * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  rw [Subgroup.mem_strictPeriods_iff] at hΓ
  set Uw := Matrix.GeneralLinearGroup.upperRightHom w with hUw
  have h1 : (ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹)⁻¹ • Uw ∈
      (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hΓ
  rw [← map_inv, inv_inv, ConjAct.toConjAct_smul] at h1
  obtain ⟨δ, hδ, hδeq⟩ := Subgroup.mem_map.mp h1

  have hc : (γ : GL (Fin 2) ℝ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := rfl
  set t : SL(2, ℤ) := γ⁻¹ * δ * γ with ht
  have htU : Matrix.SpecialLinearGroup.mapGL ℝ t = Uw := by
    rw [ht, map_mul, map_mul, map_inv, hδeq, hc]
    group

  have hent : ∀ i j : Fin 2, ((t i j : ℤ) : ℝ) = (Uw : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    have := congrArg (fun M : GL (Fin 2) ℝ => (M : Matrix (Fin 2) (Fin 2) ℝ) i j) htU
    simpa [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.map_apply_coe] using this
  have h00 : ((t 0 0 : ℤ) : ℝ) = 1 := by rw [hent]; simp [hUw, Matrix.GeneralLinearGroup.upperRightHom_apply]
  have h01 : ((t 0 1 : ℤ) : ℝ) = w := by rw [hent]; simp [hUw, Matrix.GeneralLinearGroup.upperRightHom_apply]
  have h10 : ((t 1 0 : ℤ) : ℝ) = 0 := by rw [hent]; simp [hUw, Matrix.GeneralLinearGroup.upperRightHom_apply]
  have h11 : ((t 1 1 : ℤ) : ℝ) = 1 := by rw [hent]; simp [hUw, Matrix.GeneralLinearGroup.upperRightHom_apply]
  have hpos : 0 < t 0 1 := by
    have : (0 : ℝ) < ((t 0 1 : ℤ) : ℝ) := by rw [h01]; exact hw
    exact_mod_cast this
  refine ⟨(t 0 1).toNat, by omega, ?_, ?_⟩
  · rw [← h01]
    have : ((t 0 1).toNat : ℤ) = t 0 1 := Int.toNat_of_nonneg hpos.le
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
  · have hT : ModularGroup.T ^ (t 0 1).toNat = t := by
      rw [← zpow_natCast]
      apply Subtype.ext
      rw [ModularGroup.coe_T_zpow]
      have e : ((t 0 1).toNat : ℤ) = t 0 1 := Int.toNat_of_nonneg hpos.le
      ext i j
      fin_cases i <;> fin_cases j
      · simp; exact_mod_cast h00.symm
      · simp [e]
      · simp; exact_mod_cast h10.symm
      · simp; exact_mod_cast h11.symm
    rw [hT, ht]
    have : γ * (γ⁻¹ * δ * γ) * γ⁻¹ = δ := by group
    rw [this]
    exact hδ

end PLBCUSP
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

end PURECUSP
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace PLB
open CUSPATLAS ATLINT GLUE

variable {N : ℕ} [NeZero N] {r : ℕ}

def phiU (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) (k : ℕ) (u : FB N)
    (y : Place (AlgebraicClosure ℚ) (FB N)) : ℝ :=
  Real.log ‖σ (secVal s y k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖)

def Body (s : Fin r → FB N) (σ : AlgebraicClosure ℚ →+* ℂ) (c₀ : ℝ) : Prop :=
  ∀ (k : ℕ) (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
    ∀ B : Divisor (AlgebraicClosure ℚ) (FB N), (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
    ∀ (T : Finset (Place (AlgebraicClosure ℚ) (FB N))) (v y₀ : Place (AlgebraicClosure ℚ) (FB N)),
      B v = 0 → B y₀ = 0 →
    ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (FB N)),
      linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
      (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
      (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
      ((embDegree N : ℝ) - 1) * phiU σ s k u y₀ - c₀ * k
        ≤ (Za - Finsupp.single v (1 : ℤ)).sum (fun y n => (n : ℝ) * phiU σ s k u y)

omit [NeZero N] in
theorem Body.mono {s : Fin r → FB N} {σ : AlgebraicClosure ℚ →+* ℂ} {c c' : ℝ} [NeZero N]
    (h : Body s σ c) (hle : c ≤ c') : Body s σ c' := by
  intro k u hu huL B hB T v y₀ hBv hBy₀
  obtain ⟨a, Za, h1, h2, h3, h4, h5, h6, h7⟩ := h k u hu huL B hB T v y₀ hBv hBy₀
  refine ⟨a, Za, h1, h2, h3, h4, h5, h6, ?_⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have := mul_le_mul_of_nonneg_right hle hk
  linarith

section DICT
variable (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)

theorem evalAt_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (hw : w.IsRational)
    {f : F} (hf : f ∈ w.toValuationSubring) (n : ℕ) : w.evalAt (f ^ n) = w.evalAt f ^ n := by
  induction n with
  | zero => simpa using w.evalAt_algebraMap (1 : K)
  | succ n ih => rw [pow_succ, w.evalAt_mul hw (pow_mem hf n) hf, ih, pow_succ]

theorem embDivisor_eq_zero_of_comap (y : Place (AlgebraicClosure ℚ) (FB N)) (τ : ℍ)
    (hy : y.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ)) : embDivisor N y = 0 := by
  classical
  have hyinf : y ≠ cuspInftyBar N := by
    intro h
    apply ATLINT.jB_notMem (N := N)
    rw [← h, hy, ValuationSubring.mem_comap, phi_jB]
    exact ATLINT.jC_mem_pt D τ
  simp [embDivisor, Finsupp.single_apply, Ne.symm hyinf]

theorem dict_values (hs : IsEmbBasis N s) (k : ℕ) (u : FB N)
    (y : Place (AlgebraicClosure ℚ) (FB N)) (τ : ℍ)
    (hy : y.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ))
    (hu : u ∈ y.toValuationSubring) :
    ∃ P : ℂ, P ≠ 0 ∧
      σ (secVal s y k u) = (D.pt τ).evalAt (phi N σ u) * P⁻¹ ^ k ∧
      (∀ i, σ (evalVec s y i) = Φint σ s τ i * P⁻¹) := by
  classical
  have hr := L2.r_pos N s hs
  set π := pivotIndex s y hr with hπ
  have hE0 := embDivisor_eq_zero_of_comap D σ y τ hy
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hordπ : y.ord (s π) = 0 := by rw [L2.ord_pivot N s hs y hr, hE0, neg_zero]
  have hrat := CUSPATLAS.isRational_FB (N := N) y
  have hratC := ATLINT.isRational_FC (D.pt τ)

  have hπmem : s π ∈ y.toValuationSubring := y.mem_of_ord_nonneg (hs0 π) (le_of_eq hordπ.symm)
  have hπinv : (s π)⁻¹ ∈ y.toValuationSubring :=
    y.mem_of_ord_nonneg (inv_ne_zero (hs0 π)) (by rw [y.ord_inv, hordπ, neg_zero])
  set P : ℂ := (D.pt τ).evalAt (phi N σ (s π)) with hP
  have hPσ : σ (y.evalAt (s π)) = P := CUSPATLAS.evalAt_transport σ y (D.pt τ) hy hπmem
  have hP0 : P ≠ 0 := by
    rw [← hPσ, map_ne_zero]
    exact y.evalAt_ne_zero hrat (hs0 π) hordπ
  have hinvσ : σ (y.evalAt (s π)⁻¹) = P⁻¹ := by
    rw [y.evalAt_inv hrat (hs0 π) hordπ, map_inv₀, hPσ]
  refine ⟨P, hP0, ?_, fun i => ?_⟩
  · have hmem : u * ((s π)⁻¹) ^ k ∈ y.toValuationSubring := mul_mem hu (pow_mem hπinv k)
    have h1 : secVal s y k u = y.evalAt (u * ((s π)⁻¹) ^ k) := by
      simp only [secVal, dif_pos hr, hπ]
    rw [h1, y.evalAt_mul hrat hu (pow_mem hπinv k), evalAt_pow' y hrat hπinv k, map_mul, map_pow,
      CUSPATLAS.evalAt_transport σ y (D.pt τ) hy hu, hinvσ]
  · have hsi : s i ∈ y.toValuationSubring := by
      refine y.mem_of_ord_nonneg (hs0 i) ?_
      have := L2.neg_le_ord_of_mem _ (L2.s_mem N s hs i) (hs0 i) y
      rw [hE0] at this
      simpa using this
    have hreg := (ATLINT.interiorInputs D σ s hs).reg τ i
    calc σ (evalVec s y i) = σ (y.evalAt (s i * (s π)⁻¹)) := by simp only [evalVec, dif_pos hr, hπ]
      _ = σ (y.evalAt (s i)) * σ (y.evalAt (s π)⁻¹) := by rw [y.evalAt_mul hrat hsi hπinv, map_mul]
      _ = (D.pt τ).evalAt (phi N σ (s i)) * P⁻¹ := by rw [CUSPATLAS.evalAt_transport σ y (D.pt τ) hy hsi, hinvσ]
      _ = Φint σ s τ i * P⁻¹ := by
          congr 1
          exact ((ATLINT.ext_analyticAt D (phi N σ (s i)) τ hreg).2.2).symm

theorem phiU_eq (hs : IsEmbBasis N s) (k : ℕ) (u : FB N)
    (y : Place (AlgebraicClosure ℚ) (FB N)) (τ : ℍ)
    (hy : y.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ))
    (hu : u ∈ y.toValuationSubring) (hne : secVal s y k u ≠ 0) :
    phiU σ s k u y = Real.log ‖(D.pt τ).evalAt (phi N σ u)‖ - (k : ℝ) * Real.log (⨆ i, ‖Φint σ s τ i‖) := by
  classical
  obtain ⟨P, hP0, hsec, hvec⟩ := dict_values D σ s hs k u y τ hy hu
  have hr := L2.r_pos N s hs
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hU0 : (D.pt τ).evalAt (phi N σ u) ≠ 0 := by
    intro h0
    apply hne
    have : σ (secVal s y k u) = 0 := by rw [hsec, h0, zero_mul]
    exact (map_eq_zero σ).mp this
  have hsup : (⨆ i, ‖σ (evalVec s y i)‖) = (⨆ i, ‖Φint σ s τ i‖) * ‖P⁻¹‖ := by
    simp_rw [hvec, norm_mul]
    exact (Real.iSup_mul_of_nonneg (norm_nonneg P⁻¹) _).symm
  have hΦpos : 0 < ⨆ i, ‖Φint σ s τ i‖ := by
    have hne0 := ATLINT.interior_ne_zero D σ s hs (ATLINT.interiorInputs D σ s hs) τ
    obtain ⟨i, hi⟩ : ∃ i, Φint σ s τ i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne0 (funext h)
    exact lt_of_lt_of_le (norm_pos_iff.mpr hi)
      (le_ciSup (f := fun i => ‖Φint σ s τ i‖) (Set.finite_range _).bddAbove i)
  have hPi : ‖P⁻¹‖ ≠ 0 := norm_ne_zero_iff.mpr (inv_ne_zero hP0)
  unfold phiU
  rw [hsec, hsup, norm_mul, norm_pow, Real.log_mul (norm_ne_zero_iff.mpr hU0) (pow_ne_zero _ hPi),
    Real.log_pow, Real.log_mul hΦpos.ne' hPi]
  ring

end DICT
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

theorem le_sum_mul_of_le (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hZ : ∀ w, 0 ≤ Z w)
    (f : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ) (S : ℝ) (hf : ∀ y, Z y ≠ 0 → S ≤ f y) :
    S * (Z.sum fun _ n => (n : ℝ)) ≤ Z.sum fun y n => (n : ℝ) * f y := by
  classical
  simp only [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  rw [mul_comm S]
  exact mul_le_mul_of_nonneg_left (hf y (Finsupp.mem_support_iff.mp hy)) (by exact_mod_cast hZ y)

section IFACE
variable (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)

def psiU (k : ℕ) (u : FB N) (τ : ℍ) : ℝ :=
  Real.log ‖(D.pt τ).evalAt (phi N σ u)‖ - (k : ℝ) * Real.log (⨆ i, ‖Φint σ s τ i‖)

def Gen (u : FB N) : Set ℍ := {τ | (D.pt τ).evalAt (phi N σ u) ≠ 0}

def supPsi (k : ℕ) (u : FB N) : ℝ := ⨆ τ : Gen D σ u, psiU D σ s k u τ

end IFACE
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

section ANAH
open PLBANA

variable (D : ComplexPlaceDictionary N)

def UH : Set ℂ := {z | 0 < z.im}

omit [NeZero N] in
theorem isOpen_UH : IsOpen (UH : Set ℂ) := isOpen_lt continuous_const Complex.continuous_im

omit [NeZero N] in
theorem isPreconnected_UH : IsPreconnected (UH : Set ℂ) := (convex_halfSpace_im_gt 0).isPreconnected

omit [NeZero N] in
theorem coe_mem_UH (τ : ℍ) : (τ : ℂ) ∈ UH := by
  show 0 < (τ : ℂ).im
  rw [UpperHalfPlane.coe_im]; exact τ.im_pos

def psiX (x : Fin r → FC N) (k : ℕ) (w : FC N) (τ : ℍ) : ℝ :=
  Real.log ‖(D.pt τ).evalAt w‖ - (k : ℝ) * Real.log (⨆ i, ‖ATLINT.ext (N := N) (x i) τ‖)

def GenX (w : FC N) : Set ℍ := {τ | (D.pt τ).evalAt w ≠ 0}

def supPsiX (x : Fin r → FC N) (k : ℕ) (w : FC N) : ℝ := ⨆ τ : GenX D w, psiX D x k w τ

def vecX (x : Fin r → FC N) (z : ℂ) : Fin r → ℂ := fun i => ATLINT.ext (N := N) (x i) z

def GX (x : Fin r → FC N) (z : ℂ) : ℝ := Real.log ‖vecX (N := N) x z‖

structure XData (x : Fin r → FC N) : Prop where
  reg : ∀ (τ : ℍ) (i : Fin r), x i ∈ (D.pt τ).toValuationSubring
  ne_zero : ∀ τ : ℍ, vecX (N := N) x (τ : ℂ) ≠ 0
  x_ne : ∀ i, x i ≠ 0
  r_pos : 0 < r

structure WData0 (x : Fin r → FC N) (k : ℕ) (w : FC N) : Prop where
  ne : w ≠ 0
  reg : ∀ τ : ℍ, w ∈ (D.pt τ).toValuationSubring
  cusp : ∀ (γ : SL(2, ℤ)) (h : ℝ) (hh : 0 < h) (hΓ : h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods),
    ∃ i₀ : Fin r, (∀ i, (CUSPATLAS.cuspExpHomW γ hh hΓ (x i₀)).order ≤ (CUSPATLAS.cuspExpHomW γ hh hΓ (x i)).order) ∧
      (k : ℤ) * (CUSPATLAS.cuspExpHomW γ hh hΓ (x i₀)).order ≤ (CUSPATLAS.cuspExpHomW γ hh hΓ w).order

structure WData (x : Fin r → FC N) (k : ℕ) (w : FC N) : Prop extends WData0 D x k w where
  bdd : BddAbove (Set.range fun τ : GenX D w => psiX D x k w τ)

variable {D}

omit [NeZero N] in

theorem pi_norm_eq_ciSup' (v : Fin r → ℂ) : ‖v‖ = ⨆ i, ‖v i‖ := by
  rcases isEmpty_or_nonempty (Fin r) with h | h
  · rw [Real.iSup_of_isEmpty, Pi.norm_def]
    simp
  · apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg fun i => norm_nonneg _)).2 fun i => ?_
      exact le_ciSup (Finite.bddAbove_range fun i => ‖v i‖) i
    · exact ciSup_le fun i => norm_le_pi_norm v i

theorem ext_eq_evalAt {w : FC N} (hw : ∀ τ : ℍ, w ∈ (D.pt τ).toValuationSubring) (τ : ℍ) :
    ATLINT.ext (N := N) w τ = (D.pt τ).evalAt w := (ATLINT.ext_analyticAt D w τ (hw τ)).2.2

theorem analyticAt_ext {w : FC N} (hw : ∀ τ : ℍ, w ∈ (D.pt τ).toValuationSubring) (τ : ℍ) :
    AnalyticAt ℂ (ATLINT.ext (N := N) w) τ := (ATLINT.ext_analyticAt D w τ (hw τ)).1

theorem analyticOnNhd_ext {w : FC N} (hw : ∀ τ : ℍ, w ∈ (D.pt τ).toValuationSubring) :
    AnalyticOnNhd ℂ (ATLINT.ext (N := N) w) UH := fun z hz => analyticAt_ext (D := D) hw ⟨z, hz⟩

theorem ext_smul' {w : FC N} (hw : ∀ τ : ℍ, w ∈ (D.pt τ).toValuationSubring)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    ATLINT.ext (N := N) w ((g • τ : ℍ) : ℂ) = ATLINT.ext (N := N) w (τ : ℂ) :=
  ATLINT.ext_smul D ⟨g, hg⟩ w τ (hw τ)

theorem GX_eq {x : Fin r → FC N} (z : ℂ) : GX (N := N) x z = Real.log (⨆ i, ‖ATLINT.ext (N := N) (x i) z‖) := by
  rw [GX, pi_norm_eq_ciSup']; rfl

theorem psiX_eq_psi {x : Fin r → FC N} {k : ℕ} {w : FC N} (hw : ∀ τ : ℍ, w ∈ (D.pt τ).toValuationSubring) (τ : ℍ) :
    psiX D x k w τ = PLBANA.psi (ATLINT.ext (N := N) w) (GX (N := N) x) k τ := by
  rw [psiX, PLBANA.psi, ext_eq_evalAt hw, GX_eq]

theorem continuousAt_vecX {x : Fin r → FC N} (hx : XData D x) (τ : ℍ) :
    ContinuousAt (vecX (N := N) x) τ :=
  continuousAt_pi.2 fun i => (analyticAt_ext (D := D) (fun τ => hx.reg τ i) τ).continuousAt

theorem norm_vecX_pos {x : Fin r → FC N} (hx : XData D x) (τ : ℍ) : 0 < ‖vecX (N := N) x τ‖ :=
  norm_pos_iff.mpr (hx.ne_zero τ)

theorem continuousAt_GX {x : Fin r → FC N} (hx : XData D x) (τ : ℍ) : ContinuousAt (GX (N := N) x) τ :=
  ((continuousAt_vecX hx τ).norm).log (norm_vecX_pos hx τ).ne'

theorem continuousOn_GX {x : Fin r → FC N} (hx : XData D x) : ContinuousOn (GX (N := N) x) UH :=
  fun z hz => (continuousAt_GX hx ⟨z, hz⟩).continuousWithinAt

theorem mem_GenX_iff {w : FC N} (hw : ∀ τ : ℍ, w ∈ (D.pt τ).toValuationSubring) (τ : ℍ) :
    τ ∈ GenX D w ↔ ATLINT.ext (N := N) w τ ≠ 0 := by
  rw [GenX, Set.mem_setOf_eq, ext_eq_evalAt hw]

theorem psiX_le_supPsiX {x : Fin r → FC N} {k : ℕ} {w : FC N} (hw : WData D x k w) (τ : ℍ) (hτ : τ ∈ GenX D w) :
    psiX D x k w τ ≤ supPsiX D x k w :=
  le_ciSup hw.bdd ⟨τ, hτ⟩

theorem exists_ext_ne_zero {w : FC N} (hw0 : w ≠ 0) (hw : ∀ τ : ℍ, w ∈ (D.pt τ).toValuationSubring) :
    ∃ z ∈ UH, ATLINT.ext (N := N) w z ≠ 0 := by
  let τ₀ : ℍ := ⟨Complex.I, by simp⟩
  have hne := ATLINT.analyticOrderAt_ext_ne_top D w hw0 τ₀ (hw τ₀)
  rw [Ne, analyticOrderAt_eq_top] at hne
  have hfr : ∃ᶠ z in 𝓝 (τ₀ : ℂ), ATLINT.ext (N := N) w z ≠ 0 := by
    simpa [Filter.not_eventually] using hne
  have hev : ∀ᶠ z in 𝓝 (τ₀ : ℂ), z ∈ UH := isOpen_UH.eventually_mem (coe_mem_UH τ₀)
  obtain ⟨z, hz, hzU⟩ := (hfr.and_eventually hev).exists
  exact ⟨z, hzU, hz⟩

theorem genX_nonempty {w : FC N} (hw0 : w ≠ 0) (hw : ∀ τ : ℍ, w ∈ (D.pt τ).toValuationSubring) :
    Nonempty (GenX D w) := by
  obtain ⟨z, hz, hne⟩ := exists_ext_ne_zero (D := D) hw0 hw
  exact ⟨⟨⟨z, hz⟩, (mem_GenX_iff hw ⟨z, hz⟩).mpr hne⟩⟩

theorem setupH {x : Fin r → FC N} {k : ℕ} {w : FC N} (hx : XData D x) (hw : WData D x k w) :
    PLBANA.Setup UH (ATLINT.ext (N := N) w) (GX (N := N) x) k (supPsiX D x k w) where
  isOpen := isOpen_UH
  preconn := isPreconnected_UH
  anal := analyticOnNhd_ext hw.reg
  cont := continuousOn_GX hx
  hk := Nat.cast_nonneg k
  le_S := fun z hz hFz => by
    have hgen : (⟨z, hz⟩ : ℍ) ∈ GenX D w := (mem_GenX_iff hw.reg ⟨z, hz⟩).mpr hFz
    have := psiX_le_supPsiX hw ⟨z, hz⟩ hgen
    rwa [psiX_eq_psi hw.reg] at this
  nontriv := exists_ext_ne_zero hw.ne hw.reg

theorem exists_near_sup {x : Fin r → FC N} {k : ℕ} {w : FC N} (hw : WData D x k w) :
    ∃ τ : ℍ, τ ∈ GenX D w ∧ supPsiX D x k w - 1 ≤ psiX D x k w τ := by
  haveI := genX_nonempty (D := D) hw.ne hw.reg
  have hlt : supPsiX D x k w - 1 < supPsiX D x k w := by linarith
  obtain ⟨⟨τ, hτ⟩, h⟩ := exists_lt_of_lt_ciSup hlt
  exact ⟨τ, hτ, h.le⟩

theorem xData_of (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) (hs : IsEmbBasis N s) :
    XData D (fun i => phi N σ (s i)) where
  reg := (ATLINT.interiorInputs D σ s hs).reg
  ne_zero := fun τ h0 => ATLINT.interior_ne_zero D σ s hs (ATLINT.interiorInputs D σ s hs) τ
    (funext fun i => congrFun h0 i)
  x_ne := fun i => CUSPATLAS.phi_ne_zero σ (hs.1.ne_zero i)
  r_pos := L2.r_pos N s hs

theorem ureg (σ : AlgebraicClosure ℚ →+* ℂ) (k : ℕ) (u : FB N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (τ : ℍ) :
    phi N σ u ∈ (D.pt τ).toValuationSubring := by
  rcases CUSPATLAS.forall_mem_or_exists_comap σ (D.pt τ) with hall | ⟨v, hv⟩
  · exact hall u
  · have hE0 := embDivisor_eq_zero_of_comap D σ v τ hv
    have hureg : u ∈ v.toValuationSubring := by
      refine v.mem_of_ord_nonneg hu ?_
      have := L2.neg_le_ord_of_mem _ huL hu v
      simp only [Finsupp.smul_apply, smul_eq_mul, hE0, mul_zero, neg_zero] at this
      exact this
    rw [hv, ValuationSubring.mem_comap] at hureg
    exact hureg

theorem wData0_of (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) (hs : IsEmbBasis N s) (k : ℕ) (u : FB N)
    (hu : u ≠ 0) (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) :
    WData0 D (fun i => phi N σ (s i)) k (phi N σ u) where
  ne := CUSPATLAS.phi_ne_zero σ hu
  reg := ureg σ k u hu huL
  cusp := fun γ h hh hΓ => CUSPATLAS.exists_pivot_order_leW γ hh hΓ σ s hs k u hu huL

theorem wData_of (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) (hs : IsEmbBasis N s) (k : ℕ) (u : FB N)
    (hu : u ≠ 0) (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (hbdd : BddAbove (Set.range fun τ : Gen D σ u => psiU D σ s k u τ)) :
    WData D (fun i => phi N σ (s i)) k (phi N σ u) where
  ne := CUSPATLAS.phi_ne_zero σ hu
  reg := ureg σ k u hu huL
  bdd := hbdd
  cusp := fun γ h hh hΓ => CUSPATLAS.exists_pivot_order_leW γ hh hΓ σ s hs k u hu huL

theorem exists_bounds_GX {x : Fin r → FC N} (hx : XData D x) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ UH) :
    ∃ m_lo m_hi : ℝ, m_lo ≤ m_hi ∧ ∀ z ∈ K, m_lo ≤ GX (N := N) x z ∧ GX (N := N) x z ≤ m_hi := by
  have hc : ContinuousOn (GX (N := N) x) K := (continuousOn_GX hx).mono hKU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨-|C| - 0, |C|, by linarith [abs_nonneg C], fun z hz => ?_⟩
  have h := hC z hz
  rw [Real.norm_eq_abs] at h
  constructor
  · linarith [neg_abs_le (GX (N := N) x z), abs_nonneg C, le_abs_self C]
  · linarith [le_abs_self (GX (N := N) x z), le_abs_self C]

theorem closedBall_subset_box {Bx yl yu t : ℝ} (ht : 0 ≤ t) {c : ℂ} (hc : |c.re| ≤ Bx ∧ yl ≤ c.im ∧ c.im ≤ yu)
    {ρ : ℝ} (hρ : ρ ≤ t) :
    Metric.closedBall c ρ ⊆ {z : ℂ | |z.re| ≤ Bx + t ∧ yl - t ≤ z.im ∧ z.im ≤ yu + t} := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 : |z.re - c.re| ≤ t := by
    have := Complex.abs_re_le_norm (z - c); rw [Complex.sub_re] at this; linarith
  have h2 : |z.im - c.im| ≤ t := by
    have := Complex.abs_im_le_norm (z - c); rw [Complex.sub_im] at this; linarith
  obtain ⟨hc1, hc2, hc3⟩ := hc
  rw [abs_le] at h1 h2 hc1
  simp only [Set.mem_setOf_eq, abs_le]
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, by linarith [h2.1], by linarith [h2.2]⟩

theorem box_subset_UH {Bx yl yu : ℝ} (hyl : 0 < yl) : {z : ℂ | |z.re| ≤ Bx ∧ yl ≤ z.im ∧ z.im ≤ yu} ⊆ UH :=
  fun z hz => hyl.trans_le hz.2.1

end ANAH
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

section CUSPH
open PLBANA

variable {D : ComplexPlaceDictionary N}

theorem ext_cusp_expansion' {y : FC N} (hy : y ≠ 0)
    (γ : SL(2, ℤ)) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods) :
    ∃ (Φ : ℂ → ℂ) (A : ℝ), 0 < A ∧ AnalyticAt ℂ Φ 0 ∧ Φ 0 ≠ 0 ∧
      ContinuousOn Φ (Metric.closedBall 0 (Real.exp (-2 * Real.pi * A / h))) ∧
      (∀ q ∈ Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * A / h)), Φ q ≠ 0) ∧
      ∀ τ : ℍ, A ≤ τ.im → y ∈ (D.pt (γ • τ)).toValuationSubring →
        ATLINT.ext (N := N) y ((γ • τ : ℍ) : ℂ) =
          Function.Periodic.qParam h (τ : ℂ) ^ (CUSPATLAS.cuspExpHomW γ hh hΓ y).order *
            Φ (Function.Periodic.qParam h (τ : ℂ)) ∧
        realize N ((y : FC N) : LaurentSeries ℂ) (γ • τ) =
          Function.Periodic.qParam h (τ : ℂ) ^ (CUSPATLAS.cuspExpHomW γ hh hΓ y).order *
            Φ (Function.Periodic.qParam h (τ : ℂ)) := by
  obtain ⟨hθ0, Φ, hΦan, hΦ0, hev⟩ := CUSPATLAS.slash_chart_cuspExpW y hy γ hh hΓ
  set e : ℤ := (CUSPATLAS.cuspExpHomW γ hh hΓ y).order with he
  have hΦne : Φ 0 ≠ 0 := by
    rw [hΦ0]; exact fun h0 => hθ0 (HahnSeries.coeff_order_eq_zero.mp h0)
  obtain ⟨A₁, hA₁⟩ := (UpperHalfPlane.atImInfty_mem _).mp hev

  obtain ⟨ρ, hρ, hΦc, hΦnz⟩ : ∃ ρ > 0, ContinuousOn Φ (Metric.ball 0 ρ) ∧ ∀ q ∈ Metric.ball (0 : ℂ) ρ, Φ q ≠ 0 := by
    obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.isOpen_iff.mp (isOpen_analyticAt ℂ Φ) 0 hΦan
    obtain ⟨ρ₂, hρ₂, hnz⟩ := Metric.eventually_nhds_iff_ball.mp (hΦan.continuousAt.eventually_ne hΦne)
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun q hq => (hball (Metric.ball_subset_ball (min_le_left _ _) hq)).continuousAt.continuousWithinAt,
      fun q hq => hnz q (Metric.ball_subset_ball (min_le_right _ _) hq)⟩

  set A : ℝ := max (max A₁ 1) (h * (-Real.log (ρ / 2)) / (2 * Real.pi)) + 1 with hA
  have hA1 : A₁ < A := by rw [hA]; linarith [le_max_left (max A₁ 1) (h * (-Real.log (ρ / 2)) / (2 * Real.pi)), le_max_left A₁ 1]
  have hApos : 0 < A := by rw [hA]; linarith [le_max_left (max A₁ 1) (h * (-Real.log (ρ / 2)) / (2 * Real.pi)), le_max_right A₁ 1]

  have hqsmall : ∀ z : ℂ, A ≤ z.im → ‖Function.Periodic.qParam h z‖ < ρ := by
    intro z hz
    rw [Function.Periodic.norm_qParam]
    have h2 : h * (-Real.log (ρ / 2)) / (2 * Real.pi) < z.im := by
      have := le_max_right (max A₁ 1) (h * (-Real.log (ρ / 2)) / (2 * Real.pi))
      rw [hA] at hz; linarith
    have h3 : -2 * Real.pi * z.im / h < Real.log (ρ / 2) := by
      rw [div_lt_iff₀ hh]
      have hπ : 0 < 2 * Real.pi := by positivity
      rw [div_lt_iff₀ hπ] at h2
      nlinarith
    calc Real.exp (-2 * Real.pi * z.im / h) < Real.exp (Real.log (ρ / 2)) := Real.exp_lt_exp.mpr h3
      _ = ρ / 2 := Real.exp_log (by positivity)
      _ < ρ := by linarith
  have hexpA : Real.exp (-2 * Real.pi * A / h) < ρ := by
    have := hqsmall (Complex.I * A) (by simp)
    rwa [Function.Periodic.norm_qParam, show (Complex.I * A).im = A by simp] at this
  refine ⟨Φ, A, hApos, hΦan, hΦne, hΦc.mono (Metric.closedBall_subset_ball hexpA),
    fun q hq => hΦnz q (Metric.closedBall_subset_ball hexpA hq), fun τ hτ hreg => ?_⟩
  have hrealize : realize N ((y : FC N) : LaurentSeries ℂ) (γ • τ) =
      Function.Periodic.qParam h (τ : ℂ) ^ e * Φ (Function.Periodic.qParam h (τ : ℂ)) := hA₁ τ (by linarith [hA1])
  refine ⟨?_, hrealize⟩

  set z₀ : ℂ := ((γ • τ : ℍ) : ℂ) with hz₀
  set g : ℂ → ℂ := fun v => Function.Periodic.qParam h v ^ e * Φ (Function.Periodic.qParam h v) with hg

  obtain ⟨han, heq, -⟩ := ATLINT.ext_analyticAt D y (γ • τ) hreg
  have T1 : Filter.Tendsto (fun z : ℂ => realize N ((y : FC N) : LaurentSeries ℂ) (UpperHalfPlane.ofComplex z)) (𝓝[≠] z₀)
      (𝓝 (ATLINT.ext (N := N) y z₀)) :=
    (han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

  have hz₀im : 0 < z₀.im := by rw [hz₀, UpperHalfPlane.coe_im]; exact (γ • τ).im_pos
  have hmob0 : PLBCUSP.mob γ⁻¹ z₀ = (τ : ℂ) := by
    rw [hz₀, ← PLBCUSP.coe_smul_eq, inv_smul_smul]
  have hmobc : ContinuousAt (PLBCUSP.mob γ⁻¹) z₀ := (PLBCUSP.differentiableAt_mob γ⁻¹ (γ • τ)).continuousAt
  have hτA₁ : A₁ < (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; linarith
  have hnear : ∀ᶠ z in 𝓝 z₀, 0 < z.im ∧ A₁ < (PLBCUSP.mob γ⁻¹ z).im := by
    have h1 : ∀ᶠ z in 𝓝 z₀, 0 < z.im := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀im
    have h2 : ∀ᶠ v in 𝓝 (PLBCUSP.mob γ⁻¹ z₀), A₁ < v.im := by
      rw [hmob0]; exact (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτA₁
    exact h1.and (hmobc.eventually h2)
  have hreal : ∀ᶠ z in 𝓝 z₀, realize N ((y : FC N) : LaurentSeries ℂ) (UpperHalfPlane.ofComplex z) = g (PLBCUSP.mob γ⁻¹ z) := by
    filter_upwards [hnear] with z ⟨hz, hzA⟩
    set τ' : ℍ := γ⁻¹ • UpperHalfPlane.ofComplex z with hτ'
    have h1 : UpperHalfPlane.ofComplex z = γ • τ' := by rw [hτ', smul_inv_smul]
    have h2 : (τ' : ℂ) = PLBCUSP.mob γ⁻¹ z := by
      rw [hτ', PLBCUSP.coe_smul_eq, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have h3 : A₁ ≤ τ'.im := by
      have : (τ' : ℂ).im = τ'.im := UpperHalfPlane.coe_im τ'
      rw [← this, h2]; exact hzA.le
    have h4 := hA₁ τ' h3
    rw [h1]
    show realize N ((y : FC N) : LaurentSeries ℂ) (γ • τ') = g (PLBCUSP.mob γ⁻¹ z)
    rw [← h2]
    exact h4

  have hqτ : ‖Function.Periodic.qParam h (τ : ℂ)‖ < ρ := hqsmall _ (by rw [UpperHalfPlane.coe_im]; exact hτ)
  have hgc : ContinuousAt g (τ : ℂ) := by
    have hq : ContinuousAt (fun v : ℂ => Function.Periodic.qParam h v) (τ : ℂ) := by
      simp only [Function.Periodic.qParam]
      exact ((continuousAt_const.mul continuousAt_id).div_const _).cexp
    have hq0 : Function.Periodic.qParam h (τ : ℂ) ≠ 0 := by
      simp only [Function.Periodic.qParam]; exact Complex.exp_ne_zero _
    show ContinuousAt (fun v : ℂ => Function.Periodic.qParam h v ^ e * Φ (Function.Periodic.qParam h v)) (τ : ℂ)
    refine (hq.zpow₀ e (Or.inl hq0)).mul ?_
    have hmem : Function.Periodic.qParam h (τ : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
      rwa [Metric.mem_ball, dist_zero_right]
    exact (hΦc.continuousAt (Metric.isOpen_ball.mem_nhds hmem)).comp hq
  have T2 : Filter.Tendsto (fun z : ℂ => realize N ((y : FC N) : LaurentSeries ℂ) (UpperHalfPlane.ofComplex z)) (𝓝[≠] z₀)
      (𝓝 (g (τ : ℂ))) := by
    have hgc' : ContinuousAt g (PLBCUSP.mob γ⁻¹ z₀) := by rw [hmob0]; exact hgc
    have hc2 : ContinuousAt (fun z => g (PLBCUSP.mob γ⁻¹ z)) z₀ := ContinuousAt.comp hgc' hmobc
    have : Filter.Tendsto (fun z => g (PLBCUSP.mob γ⁻¹ z)) (𝓝 z₀) (𝓝 (g (τ : ℂ))) := by
      have t2 := hc2.tendsto
      simp only [hmob0] at t2
      exact t2
    exact (this.mono_left nhdsWithin_le_nhds).congr' ((hreal.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.symm)
  have := tendsto_nhds_unique T1 T2
  rw [this]

theorem ext_cusp_expansion {y : FC N} (hy : y ≠ 0) (hyreg : ∀ τ : ℍ, y ∈ (D.pt τ).toValuationSubring)
    (γ : SL(2, ℤ)) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods) :
    ∃ (Φ : ℂ → ℂ) (A : ℝ), 0 < A ∧ AnalyticAt ℂ Φ 0 ∧ Φ 0 ≠ 0 ∧ ContinuousOn Φ (Metric.closedBall 0 (Real.exp (-2 * Real.pi * A / h))) ∧
      ∀ τ : ℍ, A ≤ τ.im →
        ATLINT.ext (N := N) y ((γ • τ : ℍ) : ℂ) =
          Function.Periodic.qParam h (τ : ℂ) ^ (CUSPATLAS.cuspExpHomW γ hh hΓ y).order *
            Φ (Function.Periodic.qParam h (τ : ℂ)) := by
  obtain ⟨Φ, A, hA, han, h0, hc, -, hexp⟩ := ext_cusp_expansion' (D := D) hy γ hh hΓ
  exact ⟨Φ, A, hA, han, h0, hc, fun τ hτ => (hexp τ hτ (hyreg _)).1⟩

theorem cusp_bdd {y : FC N} (hy : y ≠ 0) (hyreg : ∀ τ : ℍ, y ∈ (D.pt τ).toValuationSubring)
    (γ : SL(2, ℤ)) {h : ℝ} (hh : 0 < h) (hΓ : h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods)
    (m : ℤ) (hm : m ≤ (CUSPATLAS.cuspExpHomW γ hh hΓ y).order) :
    ∃ C A : ℝ, ∀ z : ℂ, A ≤ z.im →
      ‖ATLINT.ext (N := N) y ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ) * Function.Periodic.qParam h z ^ (-m)‖ ≤ C := by
  obtain ⟨Φ, A, hA, -, -, hΦc, hexp⟩ := ext_cusp_expansion (D := D) hy hyreg γ hh hΓ
  set e : ℤ := (CUSPATLAS.cuspExpHomW γ hh hΓ y).order with he
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * A / h))).exists_bound_of_continuousOn hΦc
  refine ⟨C, A, fun z hz => ?_⟩
  have hzim : 0 < z.im := hA.trans_le hz
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzim]
  have hτ : A ≤ (⟨z, hzim⟩ : ℍ).im := hz
  rw [hexp ⟨z, hzim⟩ hτ]
  set q := Function.Periodic.qParam h z with hq
  have hq0 : q ≠ 0 := by rw [hq]; simp only [Function.Periodic.qParam]; exact Complex.exp_ne_zero _
  have hqn : ‖q‖ ≤ 1 := by
    rw [hq, Function.Periodic.norm_qParam]
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ hh.le
    nlinarith [Real.pi_pos, hzim]
  have hqA : q ∈ Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * A / h)) := by
    rw [Metric.mem_closedBall, dist_zero_right, hq, Function.Periodic.norm_qParam]
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff_of_pos_right hh]
    nlinarith [Real.pi_pos]
  show ‖q ^ e * Φ q * q ^ (-m)‖ ≤ C
  have hrew : q ^ e * Φ q * q ^ (-m) = q ^ (e - m) * Φ q := by
    rw [mul_comm (q ^ e), mul_assoc, ← zpow_add₀ hq0, mul_comm, sub_eq_add_neg]
  rw [hrew, norm_mul, norm_zpow]
  have h1 : ‖q‖ ^ (e - m) ≤ 1 := by
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = e - m := ⟨(e - m).toNat, Int.toNat_of_nonneg (by omega)⟩
    rw [← hd, zpow_natCast]
    exact pow_le_one₀ (norm_nonneg _) hqn
  have h2 : ‖Φ q‖ ≤ C := hC q hqA
  have h3 : 0 ≤ ‖Φ q‖ := norm_nonneg _
  calc ‖q‖ ^ (e - m) * ‖Φ q‖ ≤ 1 * C := mul_le_mul h1 h2 h3 zero_le_one
    _ = C := one_mul C

theorem chart_pullback {y : FC N} (hyreg : ∀ τ : ℍ, y ∈ (D.pt τ).toValuationSubring)
    (γ : SL(2, ℤ)) {n : ℕ} (hn : 0 < n) (hconj : γ * ModularGroup.T ^ n * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    let q := Function.Periodic.qParam n ((γ⁻¹ • τ : ℍ) : ℂ)
    q ∈ Metric.ball (0 : ℂ) 1 ∧ q ≠ 0 ∧
      ATLINT.ext (N := N) y ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam n q) : ℍ) : ℂ) = ATLINT.ext (N := N) y τ := by
  intro q
  have hn' : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set v : ℂ := ((γ⁻¹ • τ : ℍ) : ℂ) with hv
  have hvim : 0 < v.im := by rw [hv, UpperHalfPlane.coe_im]; exact (γ⁻¹ • τ).im_pos
  refine ⟨?_, ?_, ?_⟩
  · show Function.Periodic.qParam n v ∈ Metric.ball (0 : ℂ) 1
    rw [Metric.mem_ball, dist_zero_right, Function.Periodic.norm_qParam, ← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    apply div_neg_of_neg_of_pos _ (by exact_mod_cast hn)
    nlinarith [Real.pi_pos, hvim]
  · show Function.Periodic.qParam n v ≠ 0
    simp only [Function.Periodic.qParam]; exact Complex.exp_ne_zero _
  · obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period (h := ((n : ℕ) : ℝ)) hn' v
    rw [Complex.ofReal_natCast] at hm
    have hper : Function.Periodic (fun z : ℂ => ATLINT.ext (N := N) y ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) n :=
      UpperHalfPlane.periodic_comp_smul_of_conj_T_pow_mem (F := fun τ : ℍ => ATLINT.ext (N := N) y (τ : ℂ))
        (fun g hg τ' => ext_smul' hyreg g hg τ') hconj
    show ATLINT.ext (N := N) y
        ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam n (Function.Periodic.qParam n v)) : ℍ) : ℂ) = _
    rw [hm]
    have h2 := hper.int_mul m v
    beta_reduce at h2
    rw [h2, hv, UpperHalfPlane.ofComplex_apply, smul_inv_smul]

end CUSPH
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

section CUSPH2
open PLBANA

variable {D : ComplexPlaceDictionary N}

def liftC (γ : SL(2, ℤ)) (n : ℕ) (q : ℂ) : ℍ := γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam n q)

def e0 (x : Fin r → FC N) (hr : 0 < r) (γ : SL(2, ℤ)) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods) : ℤ :=
  Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩) fun i => (CUSPATLAS.cuspExpHomW γ hh hΓ (x i)).order

theorem e0_le (x : Fin r → FC N) (hr : 0 < r) (γ : SL(2, ℤ)) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods) (i : Fin r) :
    e0 x hr γ hh hΓ ≤ (CUSPATLAS.cuspExpHomW γ hh hΓ (x i)).order :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem exists_e0_eq (x : Fin r → FC N) (hr : 0 < r) (γ : SL(2, ℤ)) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods) :
    ∃ i₀, e0 x hr γ hh hΓ = (CUSPATLAS.cuspExpHomW γ hh hΓ (x i₀)).order := by
  obtain ⟨i, -, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩)
    (fun i => (CUSPATLAS.cuspExpHomW γ hh hΓ (x i)).order)
  exact ⟨i, h⟩

theorem k_e0_le {x : Fin r → FC N} {k : ℕ} {w : FC N} (hw : WData0 D x k w) (hr : 0 < r) (γ : SL(2, ℤ))
    {h : ℝ} (hh : 0 < h) (hΓ : h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods) :
    (k : ℤ) * e0 x hr γ hh hΓ ≤ (CUSPATLAS.cuspExpHomW γ hh hΓ w).order := by
  obtain ⟨i₀, hmin, hk⟩ := hw.cusp γ h hh hΓ
  obtain ⟨j, hj⟩ := exists_e0_eq x hr γ hh hΓ
  have : e0 x hr γ hh hΓ = (CUSPATLAS.cuspExpHomW γ hh hΓ (x i₀)).order :=
    le_antisymm (e0_le x hr γ hh hΓ i₀) (by rw [hj]; exact hmin j)
  rw [this]; exact hk

def PhiC (x : Fin r → FC N) (γ : SL(2, ℤ)) (n : ℕ) (e : ℤ) : ℂ → (Fin r → ℂ) := fun q i =>
  Function.Periodic.cuspFunction n
    (fun z : ℂ => ATLINT.ext (N := N) (x i) ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ) * Function.Periodic.qParam n z ^ (-e)) q

def FCw (w : FC N) (γ : SL(2, ℤ)) (n : ℕ) (m : ℤ) : ℂ → ℂ :=
  Function.Periodic.cuspFunction n
    (fun z : ℂ => ATLINT.ext (N := N) w ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ) * Function.Periodic.qParam n z ^ (-m))

theorem PhiC_spec {x : Fin r → FC N} (hx : XData D x)
    (γ : SL(2, ℤ)) {n : ℕ} (hn : 0 < n) (hconj : γ * ModularGroup.T ^ n * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N)
    (hnR : (0 : ℝ) < (n : ℕ)) (hΓ : ((n : ℕ) : ℝ) ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods) :
    (∀ i, AnalyticOnNhd ℂ (fun q => PhiC (N := N) x γ n (e0 x hx.r_pos γ hnR hΓ) q i) (Metric.ball 0 1)) ∧
    (∀ q ∈ Metric.ball (0 : ℂ) 1, q ≠ 0 → ∀ i,
        PhiC (N := N) x γ n (e0 x hx.r_pos γ hnR hΓ) q i
          = ATLINT.ext (N := N) (x i) ((liftC γ n q : ℍ) : ℂ) * q ^ (-(e0 x hx.r_pos γ hnR hΓ))) ∧
    (∀ q ∈ Metric.ball (0 : ℂ) 1, PhiC (N := N) x γ n (e0 x hx.r_pos γ hnR hΓ) q ≠ 0) := by
  set e₀ : ℤ := e0 x hx.r_pos γ hnR hΓ with he₀
  have hXinv : ∀ i, ∀ g ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ,
      ATLINT.ext (N := N) (x i) ((g • τ : ℍ) : ℂ) = ATLINT.ext (N := N) (x i) (τ : ℂ) :=
    fun i g hg τ => ext_smul' (fun τ => hx.reg τ i) g hg τ
  have hX : ∀ i, ∀ τ : ℍ, DifferentiableAt ℂ (ATLINT.ext (N := N) (x i)) (τ : ℂ) :=
    fun i τ => (analyticAt_ext (fun τ => hx.reg τ i) τ).differentiableAt
  have hΦ := fun i => PLBCUSP.analyticOnNhd_cuspFunction (Γ := CongruenceSubgroup.Gamma0 N) (hXinv i) (hX i) hn hconj
    e₀ (cusp_bdd (hx.x_ne i) (fun τ => hx.reg τ i) γ hnR hΓ _ (e0_le x hx.r_pos γ hnR hΓ i))
  refine ⟨fun i => ?_, fun q hq hq0 i => (hΦ i).2 q hq hq0, ?_⟩
  · show AnalyticOnNhd ℂ (Function.Periodic.cuspFunction n
      (fun z : ℂ => ATLINT.ext (N := N) (x i) ((γ • UpperHalfPlane.ofComplex z : ℍ) : ℂ) * Function.Periodic.qParam n z ^ (-e₀)))
      (Metric.ball 0 1)
    exact (hΦ i).1
  intro q hq
  by_cases hq0 : q = 0
  ·
    subst hq0
    obtain ⟨i₀, hi₀⟩ := exists_e0_eq x hx.r_pos γ hnR hΓ
    obtain ⟨Φ, A, hA, hΦan, hΦne, -, hexp⟩ := ext_cusp_expansion (D := D) (hx.x_ne i₀) (fun τ => hx.reg τ i₀) γ hnR hΓ
    have hn' : ((n : ℕ) : ℝ) ≠ 0 := hnR.ne'
    have hsmallA : ∀ᶠ q in 𝓝[≠] (0 : ℂ), q ∈ Metric.ball (0 : ℂ) 1 ∧ q ≠ 0 ∧ A ≤ (Function.Periodic.invQParam n q).im := by
      have h1 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), q ≠ 0 := self_mem_nhdsWithin
      have h2 : ∀ᶠ q in 𝓝 (0 : ℂ), ‖q‖ < min 1 (Real.exp (-2 * Real.pi * A / n)) := by
        have : (0 : ℝ) < min 1 (Real.exp (-2 * Real.pi * A / n)) := lt_min one_pos (Real.exp_pos _)
        have := Metric.ball_mem_nhds (0 : ℂ) this
        filter_upwards [this] with q hq
        simpa [dist_zero_right] using hq
      filter_upwards [h1, h2.filter_mono nhdsWithin_le_nhds] with q hq0 hqn
      have hq1 : ‖q‖ < 1 := hqn.trans_le (min_le_left _ _)
      refine ⟨by rwa [Metric.mem_ball, dist_zero_right], hq0, ?_⟩
      rw [Function.Periodic.im_invQParam]
      have hqA : ‖q‖ < Real.exp (-2 * Real.pi * A / n) := hqn.trans_le (min_le_right _ _)
      have hlog : Real.log ‖q‖ < -2 * Real.pi * A / n := by
        rw [← Real.exp_lt_exp, Real.exp_log (norm_pos_iff.mpr hq0)]; exact hqA
      have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [lt_div_iff₀ hnR] at hlog
      have : -(n : ℝ) / (2 * Real.pi) * Real.log ‖q‖ = (-(Real.log ‖q‖ * n)) / (2 * Real.pi) := by ring
      rw [this, le_div_iff₀ hπ]
      nlinarith
    have heq : ∀ᶠ q in 𝓝[≠] (0 : ℂ), PhiC (N := N) x γ n e₀ q i₀ = Φ q := by
      filter_upwards [hsmallA] with q ⟨hq, hq0, hqA⟩
      have hv1 : PhiC (N := N) x γ n e₀ q i₀
          = ATLINT.ext (N := N) (x i₀) ((liftC γ n q : ℍ) : ℂ) * q ^ (-e₀) := (hΦ i₀).2 q hq hq0
      rw [hv1]
      have hvim : 0 < (Function.Periodic.invQParam n q).im := hA.trans_le hqA
      have h1 : ((liftC γ n q : ℍ) : ℂ) = ((γ • (⟨Function.Periodic.invQParam n q, hvim⟩ : ℍ) : ℍ) : ℂ) := by
        show ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam n q) : ℍ) : ℂ) = _
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hvim]
      rw [h1, (hexp ⟨Function.Periodic.invQParam n q, hvim⟩ hqA)]
      have h2 : Function.Periodic.qParam n ((⟨Function.Periodic.invQParam n q, hvim⟩ : ℍ) : ℂ) = q := by
        show Function.Periodic.qParam n (Function.Periodic.invQParam n q) = q
        rw [Function.Periodic.qParam_right_inv hn' hq0]
      rw [h2, ← hi₀, mul_comm (q ^ e₀), mul_assoc, ← zpow_add₀ hq0, add_neg_cancel, zpow_zero, mul_one]
    have hT : Filter.Tendsto (fun q => PhiC (N := N) x γ n e₀ q i₀) (𝓝[≠] 0) (𝓝 (Φ 0)) :=
      (hΦan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (heq.mono fun q h => h.symm)
    have h0 : PhiC (N := N) x γ n e₀ 0 i₀ = Φ 0 := PLBCUSP.cuspFunction_zero_of_tendsto (h := n) hT
    intro hzero
    have := congrFun hzero i₀
    rw [h0] at this
    exact hΦne this
  · intro hzero
    apply hx.ne_zero (liftC γ n q)
    funext i
    have h1 : PhiC (N := N) x γ n e₀ q i
        = ATLINT.ext (N := N) (x i) ((liftC γ n q : ℍ) : ℂ) * q ^ (-e₀) := (hΦ i).2 q hq hq0
    have h2 : PhiC (N := N) x γ n e₀ q i = 0 := by rw [hzero]; rfl
    rw [h2] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (zpow_ne_zero _ hq0)

theorem FCw_spec {x : Fin r → FC N} {k : ℕ} {w : FC N} (hx : XData D x) (hw : WData0 D x k w)
    (γ : SL(2, ℤ)) {n : ℕ} (hn : 0 < n) (hconj : γ * ModularGroup.T ^ n * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N)
    (hnR : (0 : ℝ) < (n : ℕ)) (hΓ : ((n : ℕ) : ℝ) ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods) :
    AnalyticOnNhd ℂ (FCw (N := N) w γ n ((k : ℤ) * e0 x hx.r_pos γ hnR hΓ)) (Metric.ball 0 1) ∧
    ∀ q ∈ Metric.ball (0 : ℂ) 1, q ≠ 0 →
      FCw (N := N) w γ n ((k : ℤ) * e0 x hx.r_pos γ hnR hΓ) q
        = ATLINT.ext (N := N) w ((liftC γ n q : ℍ) : ℂ) * q ^ (-((k : ℤ) * e0 x hx.r_pos γ hnR hΓ)) := by
  have hUinv : ∀ g ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ,
      ATLINT.ext (N := N) w ((g • τ : ℍ) : ℂ) = ATLINT.ext (N := N) w (τ : ℂ) := fun g hg τ => ext_smul' hw.reg g hg τ
  have hU : ∀ τ : ℍ, DifferentiableAt ℂ (ATLINT.ext (N := N) w) (τ : ℂ) := fun τ => (analyticAt_ext hw.reg τ).differentiableAt
  exact PLBCUSP.analyticOnNhd_cuspFunction (Γ := CongruenceSubgroup.Gamma0 N) hUinv hU hn hconj _
    (cusp_bdd hw.ne hw.reg γ hnR hΓ _ (k_e0_le hw hx.r_pos γ hnR hΓ))

def GC (Φc : ℂ → (Fin r → ℂ)) (q : ℂ) : ℝ := Real.log ‖Φc q‖

omit [NeZero N] in
theorem continuousOn_GC {Φc : ℂ → (Fin r → ℂ)} (han : ∀ i, AnalyticOnNhd ℂ (fun q => Φc q i) (Metric.ball 0 1))
    (hne : ∀ q ∈ Metric.ball (0 : ℂ) 1, Φc q ≠ 0) : ContinuousOn (GC Φc) (Metric.ball 0 1) := by
  intro q hq
  have hc : ContinuousAt Φc q := continuousAt_pi.2 fun i => (han i q hq).continuousAt
  exact ((hc.norm).log (norm_ne_zero_iff.mpr (hne q hq))).continuousWithinAt

theorem psi_cusp_eq {x : Fin r → FC N} {k : ℕ} {w : FC N} (hx : XData D x) (hw : WData0 D x k w)
    {γ : SL(2, ℤ)} {n : ℕ} {e₀ : ℤ} {F : ℂ → ℂ} {Φc : ℂ → (Fin r → ℂ)} {q : ℂ} (hq0 : q ≠ 0)
    (hF : F q = ATLINT.ext (N := N) w ((liftC γ n q : ℍ) : ℂ) * q ^ (-((k : ℤ) * e₀)))
    (hΦ : ∀ i, Φc q i = ATLINT.ext (N := N) (x i) ((liftC γ n q : ℍ) : ℂ) * q ^ (-e₀))
    (hgen : ATLINT.ext (N := N) w ((liftC γ n q : ℍ) : ℂ) ≠ 0) :
    PLBANA.psi F (GC Φc) k q = psiX D x k w (liftC γ n q) := by
  rw [psiX_eq_psi hw.reg, PLBANA.psi, PLBANA.psi, GC, GX, hF]
  have hvec : Φc q = (q ^ (-e₀)) • vecX (N := N) x ((liftC γ n q : ℍ) : ℂ) := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul, hΦ i, vecX]; ring
  rw [hvec, norm_smul, norm_mul, norm_zpow, norm_zpow]
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hU : 0 < ‖ATLINT.ext (N := N) w ((liftC γ n q : ℍ) : ℂ)‖ := norm_pos_iff.mpr hgen
  have hV : 0 < ‖vecX (N := N) x ((liftC γ n q : ℍ) : ℂ)‖ := norm_vecX_pos hx _
  rw [Real.log_mul hU.ne' (zpow_ne_zero _ hqpos.ne'), Real.log_mul (zpow_ne_zero _ hqpos.ne') hV.ne',
    Real.log_zpow, Real.log_zpow]
  push_cast
  ring

theorem cusp_chart_pullback {x : Fin r → FC N} {k : ℕ} {w : FC N} (hx : XData D x) (hw : WData0 D x k w)
    {γ : SL(2, ℤ)} {n : ℕ} (hn : 0 < n) (hconj : γ * ModularGroup.T ^ n * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N)
    {e₀ : ℤ} {F : ℂ → ℂ} {Φc : ℂ → (Fin r → ℂ)}
    (hval : ∀ q ∈ Metric.ball (0 : ℂ) 1, q ≠ 0 →
        F q = ATLINT.ext (N := N) w ((liftC γ n q : ℍ) : ℂ) * q ^ (-((k : ℤ) * e₀)) ∧
        ∀ i, Φc q i = ATLINT.ext (N := N) (x i) ((liftC γ n q : ℍ) : ℂ) * q ^ (-e₀))
    (τ : ℍ) :
    let q := Function.Periodic.qParam n ((γ⁻¹ • τ : ℍ) : ℂ)
    q ∈ Metric.ball (0 : ℂ) 1 ∧ q ≠ 0 ∧
      F q = ATLINT.ext (N := N) w τ * q ^ (-((k : ℤ) * e₀)) ∧
      (∀ i, Φc q i = ATLINT.ext (N := N) (x i) τ * q ^ (-e₀)) ∧
      (τ ∈ GenX D w → PLBANA.psi F (GC Φc) k q = psiX D x k w τ) := by
  intro q
  obtain ⟨hq, hq0, hw'⟩ := chart_pullback (D := D) hw.reg γ hn hconj τ
  have hx' := fun i => (chart_pullback (D := D) (fun τ => hx.reg τ i) γ hn hconj τ).2.2
  obtain ⟨hF, hΦ⟩ := hval q hq hq0
  have hlift : ∀ y : FC N, (∀ τ : ℍ, y ∈ (D.pt τ).toValuationSubring) →
      ATLINT.ext (N := N) y ((liftC γ n q : ℍ) : ℂ) = ATLINT.ext (N := N) y τ := fun y hy =>
    (chart_pullback (D := D) hy γ hn hconj τ).2.2
  refine ⟨hq, hq0, by rw [hF, hlift w hw.reg], fun i => by rw [hΦ i, hlift (x i) (fun τ => hx.reg τ i)], fun hτ => ?_⟩
  have hgen : ATLINT.ext (N := N) w ((liftC γ n q : ℍ) : ℂ) ≠ 0 := by
    rw [hlift w hw.reg]; exact (mem_GenX_iff hw.reg τ).mp hτ
  rw [psi_cusp_eq hx hw hq0 hF hΦ hgen, psiX_eq_psi hw.reg, psiX_eq_psi hw.reg, PLBANA.psi, PLBANA.psi, GX, GX,
    hlift w hw.reg]
  have hv : vecX (N := N) x ((liftC γ n q : ℍ) : ℂ) = vecX (N := N) x τ :=
    funext fun i => hlift (x i) (fun τ => hx.reg τ i)
  rw [hv]

theorem setupC {x : Fin r → FC N} {k : ℕ} {w : FC N} (hx : XData D x) (hw : WData D x k w)
    {γ : SL(2, ℤ)} {n : ℕ} (hn : 0 < n) (hconj : γ * ModularGroup.T ^ n * γ⁻¹ ∈ CongruenceSubgroup.Gamma0 N)
    {e₀ : ℤ} {F : ℂ → ℂ} {Φc : ℂ → (Fin r → ℂ)}
    (hFan : AnalyticOnNhd ℂ F (Metric.ball 0 1)) (hΦan : ∀ i, AnalyticOnNhd ℂ (fun q => Φc q i) (Metric.ball 0 1))
    (hval : ∀ q ∈ Metric.ball (0 : ℂ) 1, q ≠ 0 →
        F q = ATLINT.ext (N := N) w ((liftC γ n q : ℍ) : ℂ) * q ^ (-((k : ℤ) * e₀)) ∧
        ∀ i, Φc q i = ATLINT.ext (N := N) (x i) ((liftC γ n q : ℍ) : ℂ) * q ^ (-e₀))
    (hne : ∀ q ∈ Metric.ball (0 : ℂ) 1, Φc q ≠ 0) :
    PLBANA.Setup (Metric.ball 0 1) F (GC Φc) k (supPsiX D x k w) where
  isOpen := Metric.isOpen_ball
  preconn := (convex_ball (0 : ℂ) 1).isPreconnected
  anal := hFan
  cont := continuousOn_GC hΦan hne
  hk := Nat.cast_nonneg k
  le_S := by

    have hoff : ∀ q ∈ Metric.ball (0 : ℂ) 1, q ≠ 0 → F q ≠ 0 → PLBANA.psi F (GC Φc) k q ≤ supPsiX D x k w := by
      intro q hq hq0 hFq
      obtain ⟨hF, hΦ⟩ := hval q hq hq0
      have hgen : ATLINT.ext (N := N) w ((liftC γ n q : ℍ) : ℂ) ≠ 0 := by
        intro h0; apply hFq; rw [hF, h0, zero_mul]
      rw [psi_cusp_eq hx hw.toWData0 hq0 hF hΦ hgen]
      exact psiX_le_supPsiX hw _ ((mem_GenX_iff hw.reg _).mpr hgen)
    intro q hq hFq
    by_cases hq0 : q = 0
    · subst hq0

      have hFc : ContinuousAt F 0 := (hFan 0 hq).continuousAt
      have hGc : ContinuousAt (GC Φc) 0 := (continuousOn_GC hΦan hne).continuousAt (Metric.isOpen_ball.mem_nhds hq)
      have hpc : ContinuousAt (PLBANA.psi F (GC Φc) k) 0 := by
        unfold PLBANA.psi
        exact ((hFc.norm).log (norm_ne_zero_iff.mpr hFq)).sub (continuousAt_const.mul hGc)
      have hev : ∀ᶠ q in 𝓝[≠] (0 : ℂ), PLBANA.psi F (GC Φc) k q ≤ supPsiX D x k w := by
        have h1 : ∀ᶠ q in 𝓝 (0 : ℂ), F q ≠ 0 := hFc.eventually_ne hFq
        have h2 : ∀ᶠ q in 𝓝 (0 : ℂ), q ∈ Metric.ball (0 : ℂ) 1 := Metric.isOpen_ball.eventually_mem hq
        have h3 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), q ≠ 0 := self_mem_nhdsWithin
        filter_upwards [h1.filter_mono nhdsWithin_le_nhds, h2.filter_mono nhdsWithin_le_nhds, h3] with q hF1 hq2 hq3
        exact hoff q hq2 hq3 hF1
      exact le_of_tendsto (hpc.tendsto.mono_left nhdsWithin_le_nhds) hev
    · exact hoff q hq hq0 hFq
  nontriv := by
    obtain ⟨τ, hτ, -⟩ := exists_near_sup (D := D) hw
    obtain ⟨hq, hq0, hF, -, -⟩ := cusp_chart_pullback hx hw.toWData0 hn hconj hval τ
    refine ⟨_, hq, ?_⟩
    rw [hF]
    exact mul_ne_zero ((mem_GenX_iff hw.reg τ).mp hτ) (zpow_ne_zero _ hq0)

end CUSPH2
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

section GOODH
open PLBANA

variable {D : ComplexPlaceDictionary N}

theorem exists_box_of_isCompact {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ UH) :
    ∃ Ba ya Ya : ℝ, 0 < ya ∧ ∀ z ∈ K, |z.re| ≤ Ba ∧ ya ≤ z.im ∧ z.im ≤ Ya := by
  by_cases hKe : K = ∅
  · exact ⟨0, 1, 1, one_pos, by simp [hKe]⟩
  have hne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKe
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℂ => z) continuousOn_id
  obtain ⟨zm, hzm, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  refine ⟨C, zm.im, C, hKU hzm, fun z hz => ⟨?_, hmin hz, ?_⟩⟩
  · exact (Complex.abs_re_le_norm z).trans (hC z hz)
  · exact (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans (hC z hz))

theorem isCompact_liftC_image (γ : SL(2, ℤ)) {n : ℕ} (hn : 0 < n) {K : Set ℂ} (hK : IsCompact K)
    (hK1 : ∀ q ∈ K, ‖q‖ < 1) (hKre : ∀ q ∈ K, 0 < q.re) :
    IsCompact ((fun q : ℂ => ((liftC γ n q : ℍ) : ℂ)) '' K) ∧
    (fun q : ℂ => ((liftC γ n q : ℍ) : ℂ)) '' K ⊆ UH := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have him : ∀ q ∈ K, 0 < (Function.Periodic.invQParam n q).im := fun q hq =>
    PLBCUSP.im_invQParam_pos hnR (hK1 q hq) (fun h0 => by have := hKre q hq; rw [h0] at this; simp at this)
  have hcont : ContinuousOn (fun q : ℂ => ((liftC γ n q : ℍ) : ℂ)) K := by
    intro q hq
    have hq0 : q ≠ 0 := fun h0 => by have := hKre q hq; rw [h0] at this; simp at this
    have hslit : q ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (hKre q hq))
    have h1 : ContinuousAt (fun q : ℂ => Function.Periodic.invQParam n q) q := by
      simp only [Function.Periodic.invQParam]
      exact continuousAt_const.mul (continuousAt_clog hslit)
    have heq : (fun q' : ℂ => ((liftC γ n q' : ℍ) : ℂ)) =ᶠ[𝓝 q]
        fun q' => PLBCUSP.mob γ (Function.Periodic.invQParam n q') := by
      have hopen : ∀ᶠ q' in 𝓝 q, 0 < (Function.Periodic.invQParam n q').im :=
        h1.eventually ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds (him q hq))
      filter_upwards [hopen] with q' hq'
      show ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam n q') : ℍ) : ℂ) = _
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hq', PLBCUSP.coe_smul_eq]
    refine (ContinuousAt.congr ?_ heq.symm).continuousWithinAt
    have h2 : ContinuousAt (PLBCUSP.mob γ) (Function.Periodic.invQParam n q) := by
      have := PLBCUSP.differentiableAt_mob γ ⟨_, him q hq⟩
      exact this.continuousAt
    exact h2.comp h1
  refine ⟨hK.image_of_continuousOn hcont, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact coe_mem_UH _

theorem anchor {x : Fin r → FC N} (hx : XData D x) [(CongruenceSubgroup.Gamma0 N).FiniteIndex] :
    ∃ (Ba ya Ya Ca : ℝ), 0 < ya ∧ 0 ≤ Ca ∧ ∀ (k : ℕ) (w : FC N), WData D x k w →
      ∃ p : ℂ, (|p.re| ≤ Ba ∧ ya ≤ p.im ∧ p.im ≤ Ya) ∧ ATLINT.ext (N := N) w p ≠ 0 ∧
        supPsiX D x k w - Ca * (k + 1) ≤ PLBANA.psi (ATLINT.ext (N := N) w) (GX (N := N) x) k p := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < (N : ℕ) := by exact_mod_cast hN
  obtain ⟨Sc, B, y₀, Y₁, hy₀, hcov⟩ := GLUE.cover_box_or_cusp (N := N) (N : ℝ)

  have hconj : ∀ σc : SL(2, ℤ), σc * ModularGroup.T ^ N * σc⁻¹ ∈ CongruenceSubgroup.Gamma0 N := fun σc => by
    have := CUSPATLAS.conj_T_zpow_mem_Gamma0 N σc
    rwa [zpow_natCast] at this
  have hΓ : ∀ σc : SL(2, ℤ), ((N : ℕ) : ℝ) ∈ (CUSPATLAS.conjGamma0 N σc).strictPeriods :=
    fun σc => CUSPATLAS.natCast_mem_strictPeriods_conjGamma0 N σc

  set D₂ : Set ℂ := Metric.closedBall ((1 / 2 : ℝ) : ℂ) (1 / 10) with hD₂
  have hD₂1 : ∀ q ∈ D₂, ‖q‖ < 1 := by
    intro q hq
    rw [hD₂, Metric.mem_closedBall] at hq
    calc ‖q‖ = dist q 0 := (dist_zero_right q).symm
      _ ≤ dist q ((1 / 2 : ℝ) : ℂ) + dist (((1 / 2 : ℝ) : ℂ)) 0 := dist_triangle _ _ _
      _ ≤ 1 / 10 + 1 / 2 := by
          apply add_le_add hq
          rw [dist_zero_right, Complex.norm_real]; norm_num
      _ < 1 := by norm_num
  have hD₂re : ∀ q ∈ D₂, 0 < q.re := by
    intro q hq
    rw [hD₂, Metric.mem_closedBall, dist_eq_norm] at hq
    have := Complex.abs_re_le_norm (q - ((1 / 2 : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at this
    have h2 := (abs_le.mp (this.trans hq)).1
    linarith
  set Kc : SL(2, ℤ) → Set ℂ := fun σc => (fun q : ℂ => ((liftC σc N q : ℍ) : ℂ)) '' D₂ with hKc
  have hKc : ∀ σc, IsCompact (Kc σc) ∧ Kc σc ⊆ UH := fun σc =>
    isCompact_liftC_image σc hN (isCompact_closedBall _ _) hD₂1 hD₂re
  set Kbox : Set ℂ := {z : ℂ | |z.re| ≤ B ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁} with hKbox
  set Kanc : Set ℂ := Kbox ∪ ⋃ σc ∈ Sc, Kc σc with hKanc
  have hKanc_c : IsCompact Kanc :=
    (GLUE.isCompact_box B y₀ Y₁).union (Sc.isCompact_biUnion fun σc _ => (hKc σc).1)
  have hKanc_U : Kanc ⊆ UH := by
    rintro z (hz | hz)
    · exact box_subset_UH hy₀ hz
    · obtain ⟨σc, hσ, hz'⟩ := Set.mem_iUnion₂.mp hz
      exact (hKc σc).2 hz'
  obtain ⟨Ba, ya, Ya, hya, hbox⟩ := exists_box_of_isCompact hKanc_c hKanc_U

  have hcst : ∀ σc : SL(2, ℤ), ∃ m_lo m_hi : ℝ, m_lo ≤ m_hi ∧ ∀ q ∈ Metric.closedBall (0 : ℂ) (9 / 10),
      m_lo ≤ GC (PhiC (N := N) x σc N (e0 x hx.r_pos σc hNR (hΓ σc))) q ∧
      GC (PhiC (N := N) x σc N (e0 x hx.r_pos σc hNR (hΓ σc))) q ≤ m_hi := by
    intro σc
    obtain ⟨hΦan, -, hΦne⟩ := PhiC_spec hx σc hN (hconj σc) hNR (hΓ σc)
    have hsub : Metric.closedBall (0 : ℂ) (9 / 10) ⊆ Metric.ball 0 1 := Metric.closedBall_subset_ball (by norm_num)
    have hc : ContinuousOn (GC (PhiC (N := N) x σc N (e0 x hx.r_pos σc hNR (hΓ σc)))) (Metric.closedBall 0 (9 / 10)) :=
      (continuousOn_GC hΦan hΦne).mono hsub
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (9 / 10)).exists_bound_of_continuousOn hc
    refine ⟨-|C|, |C|, by linarith [abs_nonneg C], fun q hq => ?_⟩
    have h := hC q hq
    rw [Real.norm_eq_abs] at h
    exact ⟨by linarith [neg_abs_le (GC (PhiC (N := N) x σc N (e0 x hx.r_pos σc hNR (hΓ σc))) q), abs_nonneg C, le_abs_self C],
      by linarith [le_abs_self (GC (PhiC (N := N) x σc N (e0 x hx.r_pos σc hNR (hΓ σc))) q), le_abs_self C]⟩
  choose m_lo m_hi hosc hbnd using hcst
  set Ca : ℝ := 9 ^ 6 * (1 + 6 * ∑ σc ∈ Sc, (m_hi σc - m_lo σc)) with hCa
  have hsum_nn : 0 ≤ ∑ σc ∈ Sc, (m_hi σc - m_lo σc) := Finset.sum_nonneg fun σc _ => by linarith [hosc σc]
  have hCa0 : 0 ≤ Ca := by rw [hCa]; positivity
  have hCa1 : 1 ≤ Ca := by
    rw [hCa]
    have : (1 : ℝ) ≤ 9 ^ 6 := by norm_num
    nlinarith
  refine ⟨Ba, ya, Ya, Ca, hya, hCa0, fun k w hw => ?_⟩

  obtain ⟨τs, hτs, hnear⟩ := exists_near_sup (D := D) hw
  obtain ⟨g, hg, hcase⟩ := hcov τs
  have hginv : psiX D x k w (g • τs) = psiX D x k w τs := by
    rw [psiX_eq_psi hw.reg, psiX_eq_psi hw.reg, PLBANA.psi, PLBANA.psi, GX, GX, ext_smul' hw.reg g hg]
    have : vecX (N := N) x ((g • τs : ℍ) : ℂ) = vecX (N := N) x τs := funext fun i => ext_smul' (fun τ => hx.reg τ i) g hg τs
    rw [this]
  have hggen : ATLINT.ext (N := N) w ((g • τs : ℍ) : ℂ) ≠ 0 := by
    rw [ext_smul' hw.reg g hg]; exact (mem_GenX_iff hw.reg τs).mp hτs
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases hcase with hb | ⟨σc, hσc, z, hz, hzY, hgz⟩
  ·
    refine ⟨((g • τs : ℍ) : ℂ), hbox _ (Or.inl ?_), hggen, ?_⟩
    · simp only [hKbox, Set.mem_setOf_eq, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; exact hb
    · rw [← psiX_eq_psi hw.reg, hginv]
      have h1 : (1 : ℝ) ≤ Ca * (k + 1) := by nlinarith
      linarith
  ·
    have hΓσ := hΓ σc
    set e₀ := e0 x hx.r_pos σc hNR hΓσ with he₀
    obtain ⟨hΦan, hΦval, hΦne⟩ := PhiC_spec hx σc hN (hconj σc) hNR hΓσ
    obtain ⟨hFan, hFval⟩ := FCw_spec hx hw.toWData0 σc hN (hconj σc) hNR hΓσ
    set F := FCw (N := N) w σc N ((k : ℤ) * e₀) with hF
    set Φc := PhiC (N := N) x σc N e₀ with hΦc
    have hval : ∀ q ∈ Metric.ball (0 : ℂ) 1, q ≠ 0 →
        F q = ATLINT.ext (N := N) w ((liftC σc N q : ℍ) : ℂ) * q ^ (-((k : ℤ) * e₀)) ∧
        ∀ i, Φc q i = ATLINT.ext (N := N) (x i) ((liftC σc N q : ℍ) : ℂ) * q ^ (-e₀) :=
      fun q hq hq0 => ⟨hFval q hq hq0, hΦval q hq hq0⟩
    have hS := setupC hx hw hN (hconj σc) hFan hΦan hval hΦne

    obtain ⟨hq1, hq10, hFq1, -, hpsi1⟩ := cusp_chart_pullback hx hw.toWData0 hN (hconj σc) hval (g • τs)
    set q₁ := Function.Periodic.qParam N ((σc⁻¹ • (g • τs) : ℍ) : ℂ) with hq₁
    have hz_eq : σc⁻¹ • (g • τs) = z := by rw [hgz, inv_smul_smul]
    have hq1small : ‖q₁‖ ≤ 1 / 10 := by
      rw [hq₁, hz_eq, Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
      have hz' : (N : ℝ) < z.im := hzY
      have h1 : -2 * Real.pi * z.im / N ≤ -3 := by
        rw [div_le_iff₀ hNR]
        nlinarith [mul_le_mul_of_nonneg_left hz'.le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Real.pi_gt_three, hNR]
      have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 : (10 : ℝ) ≤ Real.exp 1 ^ 3 := by
        have h4 := Real.exp_one_gt_d9
        have h5 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h4.le 3
        nlinarith
      calc Real.exp (-2 * Real.pi * z.im / N) ≤ Real.exp (-3) := Real.exp_le_exp.mpr h1
        _ = (Real.exp 1 ^ 3)⁻¹ := by rw [Real.exp_neg, h2]
        _ ≤ 1 / 10 := by
            rw [one_div, inv_le_inv₀ (by positivity) (by norm_num)]
            exact h3
    have hgen1 : (g • τs) ∈ GenX D w := (mem_GenX_iff hw.reg _).mpr hggen
    have hF1 : F q₁ ≠ 0 := by
      rw [hFq1]; exact mul_ne_zero hggen (zpow_ne_zero _ hq10)
    have hψ1 : supPsiX D x k w - 1 ≤ PLBANA.psi F (GC Φc) k q₁ := by
      rw [hpsi1 hgen1, hginv]; exact hnear

    set c : ℕ → ℂ := fun l => (1 - (l : ℝ) / 6) • q₁ + ((l : ℝ) / 6) • (((1 / 2 : ℝ)) : ℂ) with hc
    have hc0 : c 0 = q₁ := by simp [hc]
    have hc6 : c 6 = ((1 / 2 : ℝ) : ℂ) := by simp [hc]
    have hhalf : ‖(((1 / 2 : ℝ)) : ℂ)‖ = 1 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    have hdist_total : dist q₁ (((1 / 2 : ℝ) : ℂ)) ≤ 6 / 10 := by
      calc dist q₁ (((1 / 2 : ℝ) : ℂ)) ≤ dist q₁ 0 + dist 0 (((1 / 2 : ℝ) : ℂ)) := dist_triangle _ _ _
        _ ≤ 1 / 10 + 1 / 2 := by
            rw [dist_zero_right, dist_zero_left, hhalf]
            linarith
        _ = 6 / 10 := by norm_num
    have hstep : ∀ l < 6, dist (c l) (c (l + 1)) ≤ 1 / 10 := by
      intro l hl
      rw [dist_eq_norm]
      have : c l - c (l + 1) = ((1 / 6 : ℝ)) • (q₁ - (((1 / 2 : ℝ)) : ℂ)) := by
        simp only [hc, Complex.real_smul]; push_cast; ring
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6), ← dist_eq_norm]
      linarith
    have hcnorm : ∀ l ≤ 6, ‖c l‖ ≤ 1 / 2 := by
      intro l hl
      have hl' : (l : ℝ) / 6 ≤ 1 := by rw [div_le_one (by norm_num)]; exact_mod_cast hl
      have hl0 : 0 ≤ (l : ℝ) / 6 := by positivity
      calc ‖c l‖ ≤ ‖(1 - (l : ℝ) / 6) • q₁‖ + ‖((l : ℝ) / 6) • (((1 / 2 : ℝ)) : ℂ)‖ := norm_add_le _ _
        _ = |1 - (l : ℝ) / 6| * ‖q₁‖ + |(l : ℝ) / 6| * (1 / 2) := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hhalf]
        _ = (1 - (l : ℝ) / 6) * ‖q₁‖ + (l : ℝ) / 6 * (1 / 2) := by
            rw [abs_of_nonneg (by linarith), abs_of_nonneg hl0]
        _ ≤ (1 - (l : ℝ) / 6) * (1 / 10) + (l : ℝ) / 6 * (1 / 2) := by nlinarith [norm_nonneg q₁]
        _ ≤ 1 / 2 := by nlinarith
    have hcW : ∀ l ≤ 6, Metric.closedBall (c l) (4 * (1 / 10)) ⊆ Metric.ball (0 : ℂ) 1 := by
      intro l hl q hq
      rw [Metric.mem_closedBall] at hq
      rw [Metric.mem_ball, dist_zero_right]
      calc ‖q‖ = dist q 0 := (dist_zero_right q).symm
        _ ≤ dist q (c l) + dist (c l) 0 := dist_triangle _ _ _
        _ ≤ 4 * (1 / 10) + 1 / 2 := add_le_add hq (by rw [dist_zero_right]; exact hcnorm l hl)
        _ < 1 := by norm_num
    have hcW' : ∀ l ≤ 6, Metric.closedBall (c l) (4 * (1 / 10)) ⊆ Metric.closedBall (0 : ℂ) (9 / 10) := by
      intro l hl q hq
      rw [Metric.mem_closedBall] at hq ⊢
      rw [dist_zero_right]
      calc ‖q‖ = dist q 0 := (dist_zero_right q).symm
        _ ≤ dist q (c l) + dist (c l) 0 := dist_triangle _ _ _
        _ ≤ 4 * (1 / 10) + 1 / 2 := add_le_add hq (by rw [dist_zero_right]; exact hcnorm l hl)
        _ = 9 / 10 := by norm_num
    have hchain := hS.chain (δ := 1 / 10) (A := 1) (by norm_num) zero_le_one (hosc σc) c 6 hcW
      (fun l hl q hq => (hbnd σc q (hcW' l hl hq)).1) (fun l hl q hq => (hbnd σc q (hcW' l hl hq)).2)
      (fun l hl => hstep l hl) (p₀ := q₁) (by rw [hc0, dist_self]; norm_num) hF1 hψ1 6 le_rfl
    obtain ⟨q₂, hq2d, hFq2, hψ2⟩ := hchain
    rw [hc6] at hq2d
    have hq2D : q₂ ∈ D₂ := by rw [hD₂, Metric.mem_closedBall]; exact hq2d.le
    have hq2b : q₂ ∈ Metric.ball (0 : ℂ) 1 := by rw [Metric.mem_ball, dist_zero_right]; exact hD₂1 q₂ hq2D
    have hq20 : q₂ ≠ 0 := fun h0 => by have := hD₂re q₂ hq2D; rw [h0] at this; simp at this

    obtain ⟨hF2, hΦ2⟩ := hval q₂ hq2b hq20
    have hgen2 : ATLINT.ext (N := N) w ((liftC σc N q₂ : ℍ) : ℂ) ≠ 0 := by
      intro h0; apply hFq2; rw [hF2, h0, zero_mul]
    refine ⟨((liftC σc N q₂ : ℍ) : ℂ), hbox _ (Or.inr (Set.mem_iUnion₂.mpr ⟨σc, hσc, ⟨q₂, hq2D, rfl⟩⟩)), hgen2, ?_⟩
    rw [← psiX_eq_psi hw.reg, ← psi_cusp_eq hx hw.toWData0 hq20 hF2 hΦ2 hgen2]
    have hosc' : m_hi σc - m_lo σc ≤ ∑ σ' ∈ Sc, (m_hi σ' - m_lo σ') :=
      Finset.single_le_sum (f := fun σ' => m_hi σ' - m_lo σ') (fun σ' _ => by linarith [hosc σ']) hσc
    have hk9 : (1 + (6 : ℕ) * (k * (m_hi σc - m_lo σc))) * 9 ^ (6 : ℕ) ≤ Ca * (k + 1) := by
      rw [hCa]
      have h1 : 0 ≤ m_hi σc - m_lo σc := by linarith [hosc σc]
      push_cast
      nlinarith [hsum_nn, hosc', hkR, mul_nonneg hkR h1, mul_nonneg hkR hsum_nn]
    push_cast at hψ2 hk9 ⊢
    linarith

end GOODH
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

section GOODH2
open PLBANA

variable {D : ComplexPlaceDictionary N}

omit [NeZero N] in
theorem mem_box_iff_reProdIm {B y Y : ℝ} (z : ℂ) :
    (|z.re| ≤ B ∧ y ≤ z.im ∧ z.im ≤ Y) ↔ z ∈ (Set.Icc (-B) B ×ℂ Set.Icc y Y) := by
  rw [Complex.mem_reProdIm, Set.mem_Icc, Set.mem_Icc, abs_le]

theorem good_box {x : Fin r → FC N} (hx : XData D x) [(CongruenceSubgroup.Gamma0 N).FiniteIndex]
    (Bx yl yu δ : ℝ) (hyl : 0 < yl) (hδ : 0 < δ) (hδy : 4 * δ < yl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (w : FC N), WData D x k w →
      ∀ c : ℂ, (|c.re| ≤ Bx ∧ yl ≤ c.im ∧ c.im ≤ yu) →
        ∃ p : ℂ, dist p c < δ ∧ ATLINT.ext (N := N) w p ≠ 0 ∧
          supPsiX D x k w - C * (k + 1) ≤ PLBANA.psi (ATLINT.ext (N := N) w) (GX (N := N) x) k p := by
  classical
  obtain ⟨Ba, ya, Ya, Ca, hya, hCa, hanc⟩ := anchor (D := D) hx

  set B' : ℝ := max (max Bx Ba) 0 with hB'
  set y' : ℝ := min yl ya with hy'
  set Y' : ℝ := max (max yu Ya) y' with hY'
  set δ' : ℝ := min (δ / 2) (y' / 5) with hδ'
  have hy'pos : 0 < y' := lt_min hyl hya
  have hδ'pos : 0 < δ' := lt_min (by linarith) (by linarith)
  have hδ'δ : 2 * δ' ≤ δ := by have := min_le_left (δ / 2) (y' / 5); rw [← hδ'] at this; linarith
  have hδ'y : 4 * δ' < y' := by have := min_le_right (δ / 2) (y' / 5); rw [← hδ'] at this; linarith
  obtain ⟨m, n, cg, hcg_mem, hcg_cov, hcg_path⟩ :=
    Complex.exists_grid_reProdIm (a₁ := -B') (a₂ := B') (b₁ := y') (b₂ := Y') (δ := δ')
      (by rw [hB']; linarith [le_max_right (max Bx Ba) 0]) (le_max_right _ _) hδ'pos

  set Kt : Set ℂ := {z : ℂ | |z.re| ≤ B' + 4 * δ' ∧ y' - 4 * δ' ≤ z.im ∧ z.im ≤ Y' + 4 * δ'} with hKt
  have hKtU : Kt ⊆ UH := box_subset_UH (by linarith)
  obtain ⟨m_lo, m_hi, hosc, hbnd⟩ := exists_bounds_GX hx (GLUE.isCompact_box (B' + 4 * δ') (y' - 4 * δ') (Y' + 4 * δ')) hKtU
  set C : ℝ := (Ca + (m + n) * (m_hi - m_lo)) * 9 ^ (m + n) with hC
  have hosc0' : 0 ≤ m_hi - m_lo := by linarith
  have hC0 : 0 ≤ C := by
    rw [hC]; exact mul_nonneg (add_nonneg hCa (mul_nonneg (by positivity) hosc0')) (by positivity)
  refine ⟨C, hC0, fun k w hw c hc => ?_⟩
  have hS := setupH hx hw
  obtain ⟨pa, hpa_box, hpa_gen, hpa_psi⟩ := hanc k w hw

  have hbig : ∀ z : ℂ, (|z.re| ≤ Bx ∧ yl ≤ z.im ∧ z.im ≤ yu) ∨ (|z.re| ≤ Ba ∧ ya ≤ z.im ∧ z.im ≤ Ya) →
      z ∈ (Set.Icc (-B') B' ×ℂ Set.Icc y' Y') := by
    intro z hz
    rw [← mem_box_iff_reProdIm]
    rcases hz with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · refine ⟨h1.trans ?_, (min_le_left _ _).trans h2, h3.trans ?_⟩
      · rw [hB']; exact (le_max_left _ _).trans (le_max_left _ _)
      · rw [hY']; exact (le_max_left _ _).trans (le_max_left _ _)
    · refine ⟨h1.trans ?_, (min_le_right _ _).trans h2, h3.trans ?_⟩
      · rw [hB']; exact (le_max_right _ _).trans (le_max_left _ _)
      · rw [hY']; exact (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨i₀, hi₀⟩ := hcg_cov pa (hbig pa (Or.inr hpa_box))
  obtain ⟨j, hj⟩ := hcg_cov c (hbig c (Or.inl hc))
  obtain ⟨L, π, hL, hπ0, hπL, hπstep⟩ := hcg_path i₀ j

  have hcgbox : ∀ i, |(cg i).re| ≤ B' ∧ y' ≤ (cg i).im ∧ (cg i).im ≤ Y' := fun i =>
    (mem_box_iff_reProdIm (cg i)).mpr (hcg_mem i)
  have hcW : ∀ l ≤ L, Metric.closedBall (cg (π l)) (4 * δ') ⊆ UH := fun l _ =>
    (closedBall_subset_box (by linarith) (hcgbox (π l)) le_rfl).trans hKtU
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hA : 0 ≤ Ca * (k + 1) := by positivity
  have hchain := hS.chain hδ'pos hA hosc (fun l => cg (π l)) L hcW
    (fun l _ z hz => (hbnd z (closedBall_subset_box (by linarith) (hcgbox (π l)) le_rfl hz)).1)
    (fun l _ z hz => (hbnd z (closedBall_subset_box (by linarith) (hcgbox (π l)) le_rfl hz)).2)
    (fun l hl => hπstep l hl) (p₀ := pa) (by show dist pa (cg (π 0)) < δ'; rw [hπ0]; exact hi₀) hpa_gen (by linarith) L le_rfl
  obtain ⟨p, hpd, hpgen, hpψ⟩ := hchain
  have hpd' : dist p (cg (π L)) < δ' := hpd
  rw [hπL] at hpd'
  refine ⟨p, ?_, hpgen, ?_⟩
  · calc dist p c ≤ dist p (cg j) + dist (cg j) c := dist_triangle _ _ _
      _ < δ' + δ' := add_lt_add hpd' (by rw [dist_comm]; exact hj)
      _ ≤ δ := by linarith
  ·
    have hLR : (L : ℝ) ≤ (m + n : ℕ) := by exact_mod_cast hL
    have h9 : (9 : ℝ) ^ L ≤ 9 ^ (m + n) := pow_le_pow_right₀ (by norm_num) hL
    have hosc0 : 0 ≤ m_hi - m_lo := by linarith
    have h1 : (Ca * (k + 1) + L * (k * (m_hi - m_lo))) * 9 ^ L ≤ C * (k + 1) := by
      rw [hC]
      have h2 : Ca * (k + 1) + L * (k * (m_hi - m_lo)) ≤ (Ca + (m + n : ℕ) * (m_hi - m_lo)) * (k + 1) := by
        have hL' : (L : ℝ) ≤ (m : ℝ) + n := by exact_mod_cast hL
        have hko : (k : ℝ) * (m_hi - m_lo) ≤ (m_hi - m_lo) * (k + 1) := by nlinarith [hosc0, hkR]
        have h3 : (L : ℝ) * (k * (m_hi - m_lo)) ≤ ((m : ℝ) + n) * ((m_hi - m_lo) * (k + 1)) :=
          mul_le_mul hL' hko (mul_nonneg hkR hosc0) (by positivity)
        push_cast
        nlinarith [h3]
      have h3 : 0 ≤ Ca * (k + 1) + L * (k * (m_hi - m_lo)) := by positivity
      have h4 : 0 ≤ (Ca + (m + n : ℕ) * (m_hi - m_lo)) * (k + 1) := by positivity
      calc (Ca * (k + 1) + L * (k * (m_hi - m_lo))) * 9 ^ L
          ≤ ((Ca + (m + n : ℕ) * (m_hi - m_lo)) * (k + 1)) * 9 ^ (m + n) := mul_le_mul h2 h9 (by positivity) h4
        _ = (Ca + (m + n) * (m_hi - m_lo)) * 9 ^ (m + n) * (k + 1) := by push_cast; ring
    linarith

theorem bad_imp {x : Fin r → FC N} (hx : XData D x) {w : FC N} {k : ℕ} {S lam : ℝ} {z : ℂ} (hz : z ∈ UH)
    (h : ‖ATLINT.ext (N := N) w z‖ ≤ Real.exp (S - lam) * (⨆ i, ‖ATLINT.ext (N := N) (x i) z‖) ^ k) :
    ‖ATLINT.ext (N := N) w z‖ ≤ Real.exp (S - lam + k * GX (N := N) x z) := by
  rw [← pi_norm_eq_ciSup'] at h
  have hpos : 0 < ‖vecX (N := N) x z‖ := norm_vecX_pos hx ⟨z, hz⟩
  rw [Real.exp_add, Real.exp_nat_mul, GX, Real.exp_log hpos]
  exact h

theorem bad_volume_box_X {x : Fin r → FC N} (hx : XData D x) [(CongruenceSubgroup.Gamma0 N).FiniteIndex]
    (Bx yl yu : ℝ) (hyl : 0 < yl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (w : FC N), WData D x k w → ∀ lam : ℝ, 0 < lam →
      MeasureTheory.volume {z : ℂ | |z.re| ≤ Bx ∧ yl ≤ z.im ∧ z.im ≤ yu ∧
          ‖ATLINT.ext (N := N) w z‖ ≤ Real.exp (supPsiX D x k w - lam) * (⨆ i, ‖ATLINT.ext (N := N) (x i) z‖) ^ k}
        ≤ ENNReal.ofReal (C * (k + 1) / lam) := by
  classical
  set δ : ℝ := yl / 5 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ4 : 4 * δ < yl := by rw [hδ]; linarith
  set B' : ℝ := max Bx 0 with hB'
  set Y' : ℝ := max yu yl with hY'
  obtain ⟨C₁, hC₁, hgood⟩ := good_box (D := D) hx B' yl Y' δ hyl hδ0 hδ4
  obtain ⟨m, n, cg, hcg_mem, hcg_cov, -⟩ :=
    Complex.exists_grid_reProdIm (a₁ := -B') (a₂ := B') (b₁ := yl) (b₂ := Y') (δ := δ)
      (by rw [hB']; linarith [le_max_right Bx 0]) (le_max_right _ _) hδ0
  set Kt : Set ℂ := {z : ℂ | |z.re| ≤ B' + 3 * δ ∧ yl - 3 * δ ≤ z.im ∧ z.im ≤ Y' + 3 * δ} with hKt
  have hKtU : Kt ⊆ UH := box_subset_UH (by linarith)
  obtain ⟨m_lo, m_hi, hosc, hbnd⟩ := exists_bounds_GX hx (GLUE.isCompact_box (B' + 3 * δ) (yl - 3 * δ) (Y' + 3 * δ)) hKtU
  set M : ℕ := Fintype.card (Fin (m + 1) × Fin (n + 1)) with hM
  set C : ℝ := M * (Real.pi * (2 * δ) ^ 2) * (C₁ + (m_hi - m_lo)) with hC
  have hosc0 : 0 ≤ m_hi - m_lo := by linarith
  have hC0 : 0 ≤ C := by rw [hC]; exact mul_nonneg (by positivity) (add_nonneg hC₁ hosc0)
  refine ⟨C, hC0, fun k w hw lam hlam => ?_⟩
  have hS := setupH hx hw
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcgbox : ∀ i, |(cg i).re| ≤ B' ∧ yl ≤ (cg i).im ∧ (cg i).im ≤ Y' := fun i =>
    (mem_box_iff_reProdIm (cg i)).mpr (hcg_mem i)
  choose p hpd hpgen hpψ using fun i => hgood k w hw (cg i) (hcgbox i)

  have hsub : ∀ i, Metric.closedBall (p i) (2 * δ) ⊆ UH := by
    intro i z hz
    apply hKtU
    apply closedBall_subset_box (t := 3 * δ) (by linarith) (hcgbox i) le_rfl
    rw [Metric.mem_closedBall] at hz ⊢
    calc dist z (cg i) ≤ dist z (p i) + dist (p i) (cg i) := dist_triangle _ _ _
      _ ≤ 2 * δ + δ := add_le_add hz (hpd i).le
      _ = 3 * δ := by ring
  have hsubK : ∀ i, Metric.closedBall (p i) (2 * δ) ⊆ Kt := by
    intro i z hz
    apply closedBall_subset_box (t := 3 * δ) (by linarith) (hcgbox i) le_rfl
    rw [Metric.mem_closedBall] at hz ⊢
    calc dist z (cg i) ≤ dist z (p i) + dist (p i) (cg i) := dist_triangle _ _ _
      _ ≤ 2 * δ + δ := add_le_add hz (hpd i).le
      _ = 3 * δ := by ring

  set a : ℝ := MeasureTheory.volume.real (Metric.ball (0 : ℂ) (2 * δ)) * (C₁ * (k + 1) + k * (m_hi - m_lo)) / lam with ha
  have hdisc : ∀ i, MeasureTheory.volume (Metric.ball (p i) (2 * δ) ∩
      {z | ‖ATLINT.ext (N := N) w z‖ ≤ Real.exp (supPsiX D x k w - lam + k * GX (N := N) x z)})
      ≤ ENNReal.ofReal a := by
    intro i
    have h := hS.volume_bad_ball_le (by linarith) (hsub i) (hpgen i)
      (fun z hz => (hbnd z (hsubK i hz)).1) (fun z hz => (hbnd z (hsubK i hz)).2) (hpψ i) hlam
    rw [ha, PLBANA.Setup.volumeReal_ball _ (by linarith)]
    rw [PLBANA.Setup.volumeReal_ball _ (by linarith)] at h
    exact h

  have hcover : {z : ℂ | |z.re| ≤ Bx ∧ yl ≤ z.im ∧ z.im ≤ yu ∧
        ‖ATLINT.ext (N := N) w z‖ ≤ Real.exp (supPsiX D x k w - lam) * (⨆ i, ‖ATLINT.ext (N := N) (x i) z‖) ^ k}
      ⊆ ⋃ i, (Metric.ball (p i) (2 * δ) ∩
        {z | ‖ATLINT.ext (N := N) w z‖ ≤ Real.exp (supPsiX D x k w - lam + k * GX (N := N) x z)}) := by
    rintro z ⟨h1, h2, h3, h4⟩
    have hzU : z ∈ UH := hyl.trans_le h2
    have hzbig : z ∈ (Set.Icc (-B') B' ×ℂ Set.Icc yl Y') := by
      rw [← mem_box_iff_reProdIm]
      exact ⟨h1.trans (le_max_left _ _), h2, h3.trans (le_max_left _ _)⟩
    obtain ⟨i, hi⟩ := hcg_cov z hzbig
    refine Set.mem_iUnion.mpr ⟨i, ?_, bad_imp hx hzU h4⟩
    rw [Metric.mem_ball]
    calc dist z (p i) ≤ dist z (cg i) + dist (cg i) (p i) := dist_triangle _ _ _
      _ < δ + δ := add_lt_add hi (by rw [dist_comm]; exact hpd i)
      _ = 2 * δ := by ring
  have ha0 : 0 ≤ a := by
    rw [ha]; apply div_nonneg _ hlam.le
    exact mul_nonneg MeasureTheory.measureReal_nonneg (by positivity)
  calc MeasureTheory.volume _ ≤ MeasureTheory.volume (⋃ i, (Metric.ball (p i) (2 * δ) ∩
        {z | ‖ATLINT.ext (N := N) w z‖ ≤ Real.exp (supPsiX D x k w - lam + k * GX (N := N) x z)})) :=
        MeasureTheory.measure_mono hcover
    _ ≤ ∑ i, MeasureTheory.volume (Metric.ball (p i) (2 * δ) ∩
        {z | ‖ATLINT.ext (N := N) w z‖ ≤ Real.exp (supPsiX D x k w - lam + k * GX (N := N) x z)}) :=
        MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (m + 1) × Fin (n + 1), ENNReal.ofReal a := Finset.sum_le_sum fun i _ => hdisc i
    _ = ENNReal.ofReal (M * a) := by
        rw [Finset.sum_const, Finset.card_univ, ← hM, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg M),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (C * (k + 1) / lam) := by
        apply ENNReal.ofReal_le_ofReal
        rw [ha, hC, PLBANA.Setup.volumeReal_ball _ (by linarith)]
        have hnum : Real.pi * (2 * δ) ^ 2 * (C₁ * (k + 1) + k * (m_hi - m_lo))
            ≤ Real.pi * (2 * δ) ^ 2 * ((C₁ + (m_hi - m_lo)) * (k + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [mul_nonneg hkR hosc0]
        have hfin : (M : ℝ) * (Real.pi * (2 * δ) ^ 2 * (C₁ * (k + 1) + k * (m_hi - m_lo)) / lam)
            ≤ (M : ℝ) * (Real.pi * (2 * δ) ^ 2) * (C₁ + (m_hi - m_lo)) * (k + 1) / lam := by
          rw [show (M : ℝ) * (Real.pi * (2 * δ) ^ 2) * (C₁ + (m_hi - m_lo)) * (k + 1) / lam
              = (M : ℝ) * (Real.pi * (2 * δ) ^ 2 * ((C₁ + (m_hi - m_lo)) * (k + 1)) / lam) by ring]
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hlam.le) (Nat.cast_nonneg M)
        exact hfin

theorem isOpen_deep (γ : SL(2, ℤ)) (Y₀ : ℝ) : IsOpen {z : ℂ | 0 < z.im ∧ Y₀ < (PLBCUSP.mob γ z).im} := by
  have h1 : ContinuousOn (PLBCUSP.mob γ) UH := fun z hz =>
    (PLBCUSP.differentiableAt_mob γ ⟨z, hz⟩).continuousAt.continuousWithinAt
  have h2 : ContinuousOn (fun z => (PLBCUSP.mob γ z).im) UH := Complex.continuous_im.comp_continuousOn h1
  have h3 := h2.isOpen_inter_preimage (t := Set.Ioi Y₀) isOpen_UH isOpen_Ioi
  have heq : {z : ℂ | 0 < z.im ∧ Y₀ < (PLBCUSP.mob γ z).im} = UH ∩ (fun z => (PLBCUSP.mob γ z).im) ⁻¹' Set.Ioi Y₀ := by
    ext z; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi, UH]
  rw [heq]; exact h3

theorem bad_volume_cusp_X {x : Fin r → FC N} (hx : XData D x) [(CongruenceSubgroup.Gamma0 N).FiniteIndex]
    (γ : SL(2, ℤ)) (h : ℝ) (hh : 0 < h) (hper : h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods)
    (R : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (w : FC N), WData D x k w → ∀ lam : ℝ, 0 < lam →
      MeasureTheory.volume {q : ℂ | q ∈ Metric.ball (0 : ℂ) R ∧ q ≠ 0 ∧
          ‖ATLINT.ext (N := N) w ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℍ) : ℂ)‖
            ≤ Real.exp (supPsiX D x k w - lam) *
              (⨆ i, ‖ATLINT.ext (N := N) (x i) ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℍ) : ℂ)‖) ^ k}
        ≤ ENNReal.ofReal (C * (k + 1) / lam) := by
  classical

  obtain ⟨n, hn, rfl, hconj⟩ := PLBCUSP.exists_nat_of_mem_strictPeriods N γ hh hper
  have hnR : (0 : ℝ) < (n : ℕ) := hh
  have hn' : ((n : ℕ) : ℝ) ≠ 0 := hnR.ne'

  set e₀ := e0 x hx.r_pos γ hnR hper with he₀
  obtain ⟨hΦan, hΦval, hΦne⟩ := PhiC_spec hx γ hn hconj hnR hper
  set Φc := PhiC (N := N) x γ n e₀ with hΦc
  set r_a : ℝ := (1 - R) / 4 with hra
  have hra0 : 0 < r_a := by rw [hra]; linarith
  set ρ₂ : ℝ := R + r_a with hρ₂
  have hρ₂1 : r_a + ρ₂ < 1 := by rw [hρ₂, hra]; linarith
  have hsubball : Metric.closedBall (0 : ℂ) (r_a + ρ₂) ⊆ Metric.ball 0 1 := Metric.closedBall_subset_ball hρ₂1
  obtain ⟨m_lo, m_hi, hosc, hbnd⟩ : ∃ m_lo m_hi : ℝ, m_lo ≤ m_hi ∧ ∀ q ∈ Metric.closedBall (0 : ℂ) (r_a + ρ₂),
      m_lo ≤ GC Φc q ∧ GC Φc q ≤ m_hi := by
    have hc : ContinuousOn (GC Φc) (Metric.closedBall 0 (r_a + ρ₂)) := (continuousOn_GC hΦan hΦne).mono hsubball
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (r_a + ρ₂)).exists_bound_of_continuousOn hc
    refine ⟨-|C|, |C|, by linarith [abs_nonneg C], fun q hq => ?_⟩
    have h := hC q hq
    rw [Real.norm_eq_abs] at h
    exact ⟨by linarith [neg_abs_le (GC Φc q), abs_nonneg C, le_abs_self C], by linarith [le_abs_self (GC Φc q), le_abs_self C]⟩

  set Y₀ : ℝ := (n : ℝ) * (-Real.log r_a) / (2 * Real.pi) with hY₀
  have hY₀1 : 0 < Y₀ + 1 := by
    have : 0 ≤ Y₀ := by
      rw [hY₀]; apply div_nonneg _ (by positivity)
      apply mul_nonneg hnR.le
      have : r_a < 1 := by rw [hra]; linarith
      linarith [Real.log_neg hra0 this]
    linarith
  set τ₀ : ℍ := ⟨Complex.I * (Y₀ + 1), by simpa using hY₀1⟩ with hτ₀
  set c₀ : ℂ := ((γ • τ₀ : ℍ) : ℂ) with hc₀
  have hc₀im : 0 < c₀.im := by rw [hc₀, UpperHalfPlane.coe_im]; exact (γ • τ₀).im_pos
  have hc₀deep : c₀ ∈ {z : ℂ | 0 < z.im ∧ Y₀ < (PLBCUSP.mob γ⁻¹ z).im} := by
    refine ⟨hc₀im, ?_⟩
    rw [hc₀, ← PLBCUSP.coe_smul_eq, inv_smul_smul, UpperHalfPlane.coe_im]
    show Y₀ < UpperHalfPlane.im τ₀
    rw [hτ₀]
    show Y₀ < (Complex.I * (Y₀ + 1)).im
    simp
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.mp (isOpen_deep γ⁻¹ Y₀) c₀ hc₀deep
  set δ : ℝ := min δ₁ (c₀.im / 5) with hδ
  have hδ0 : 0 < δ := lt_min hδ₁ (by linarith)
  have hδ4 : 4 * δ < c₀.im := by have := min_le_right δ₁ (c₀.im / 5); rw [← hδ] at this; linarith
  obtain ⟨C₁, hC₁, hgood⟩ := good_box (D := D) hx |c₀.re| c₀.im c₀.im δ hc₀im hδ0 hδ4
  set C : ℝ := Real.pi * ρ₂ ^ 2 * (C₁ + (m_hi - m_lo)) with hC
  have hosc0 : 0 ≤ m_hi - m_lo := by linarith
  have hC0 : 0 ≤ C := by rw [hC]; exact mul_nonneg (by positivity) (add_nonneg hC₁ hosc0)
  refine ⟨C, hC0, fun k w hw lam hlam => ?_⟩
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨hFan, hFval⟩ := FCw_spec hx hw.toWData0 γ hn hconj hnR hper
  set F := FCw (N := N) w γ n ((k : ℤ) * e₀) with hF
  have hval : ∀ q ∈ Metric.ball (0 : ℂ) 1, q ≠ 0 →
      F q = ATLINT.ext (N := N) w ((liftC γ n q : ℍ) : ℂ) * q ^ (-((k : ℤ) * e₀)) ∧
      ∀ i, Φc q i = ATLINT.ext (N := N) (x i) ((liftC γ n q : ℍ) : ℂ) * q ^ (-e₀) :=
    fun q hq hq0 => ⟨hFval q hq hq0, hΦval q hq hq0⟩
  have hS := setupC hx hw hn hconj hFan hΦan hval hΦne

  obtain ⟨p, hpd, hpgen, hpψ⟩ := hgood k w hw c₀ ⟨le_rfl, le_rfl, le_rfl⟩
  have hp_deep : p ∈ {z : ℂ | 0 < z.im ∧ Y₀ < (PLBCUSP.mob γ⁻¹ z).im} :=
    hball (Metric.mem_ball.mpr (hpd.trans_le (min_le_left _ _)))
  obtain ⟨hpim, hpY⟩ := hp_deep
  set ph : ℍ := ⟨p, hpim⟩ with hph
  obtain ⟨hq2, hq20, hFq2, hΦq2, hpsi2⟩ := cusp_chart_pullback hx hw.toWData0 hn hconj hval ph
  set q₂ := Function.Periodic.qParam n ((γ⁻¹ • ph : ℍ) : ℂ) with hq₂
  have hq2small : ‖q₂‖ < r_a := by
    rw [hq₂, Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
    have him : Y₀ < (γ⁻¹ • ph).im := by
      have : ((γ⁻¹ • ph : ℍ) : ℂ).im = (γ⁻¹ • ph).im := UpperHalfPlane.coe_im _
      rw [← this, PLBCUSP.coe_smul_eq]; exact hpY
    have h1 : -2 * Real.pi * (γ⁻¹ • ph).im / n < Real.log r_a := by
      rw [div_lt_iff₀ hnR]
      rw [hY₀, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)] at him
      nlinarith [Real.pi_pos]
    calc Real.exp (-2 * Real.pi * (γ⁻¹ • ph).im / n) < Real.exp (Real.log r_a) := Real.exp_lt_exp.mpr h1
      _ = r_a := Real.exp_log hra0
  have hgenp : ph ∈ GenX D w := (mem_GenX_iff hw.reg ph).mpr hpgen
  have hF2ne : F q₂ ≠ 0 := by rw [hFq2]; exact mul_ne_zero hpgen (zpow_ne_zero _ hq20)
  have hψ2 : supPsiX D x k w - C₁ * (k + 1) ≤ PLBANA.psi F (GC Φc) k q₂ := by
    rw [hpsi2 hgenp, psiX_eq_psi hw.reg]; exact hpψ

  have hsub2 : Metric.closedBall q₂ ρ₂ ⊆ Metric.closedBall (0 : ℂ) (r_a + ρ₂) := by
    intro q hq
    rw [Metric.mem_closedBall] at hq ⊢
    rw [dist_zero_right]
    calc ‖q‖ = dist q 0 := (dist_zero_right q).symm
      _ ≤ dist q q₂ + dist q₂ 0 := dist_triangle _ _ _
      _ ≤ ρ₂ + r_a := add_le_add hq (by rw [dist_zero_right]; exact hq2small.le)
      _ = r_a + ρ₂ := add_comm _ _
  have hρ₂0 : 0 < ρ₂ := by rw [hρ₂]; linarith
  have hcheb := hS.volume_bad_ball_le hρ₂0 (hsub2.trans hsubball) hF2ne
    (fun q hq => (hbnd q (hsub2 hq)).1) (fun q hq => (hbnd q (hsub2 hq)).2) hψ2 hlam

  have hcover : {q : ℂ | q ∈ Metric.ball (0 : ℂ) R ∧ q ≠ 0 ∧
        ‖ATLINT.ext (N := N) w ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam (n : ℕ) q) : ℍ) : ℂ)‖
          ≤ Real.exp (supPsiX D x k w - lam) *
            (⨆ i, ‖ATLINT.ext (N := N) (x i) ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam (n : ℕ) q) : ℍ) : ℂ)‖) ^ k}
      ⊆ Metric.ball q₂ ρ₂ ∩ {q | ‖F q‖ ≤ Real.exp (supPsiX D x k w - lam + k * GC Φc q)} := by
    rintro q ⟨hqR, hq0, hbad⟩
    rw [Metric.mem_ball, dist_zero_right] at hqR
    have hq1 : q ∈ Metric.ball (0 : ℂ) 1 := by rw [Metric.mem_ball, dist_zero_right]; linarith
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball]
      calc dist q q₂ ≤ dist q 0 + dist 0 q₂ := dist_triangle _ _ _
        _ < R + r_a := by rw [dist_zero_right, dist_zero_left]; exact add_lt_add hqR hq2small
        _ = ρ₂ := by rw [hρ₂]
    · obtain ⟨hF, hΦ⟩ := hval q hq1 hq0
      show ‖F q‖ ≤ Real.exp (supPsiX D x k w - lam + k * GC Φc q)
      have hlift : ((liftC γ n q : ℍ) : ℂ) = ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam (n : ℕ) q) : ℍ) : ℂ) := rfl
      rw [← pi_norm_eq_ciSup', ← hlift] at hbad
      have hvec : Φc q = (q ^ (-e₀)) • vecX (N := N) x ((liftC γ n q : ℍ) : ℂ) := by
        funext i; simp only [Pi.smul_apply, smul_eq_mul, hΦ i, vecX]; ring
      have hΦpos : 0 < ‖Φc q‖ := norm_pos_iff.mpr (hΦne q hq1)
      rw [Real.exp_add, Real.exp_nat_mul, GC, Real.exp_log hΦpos, hF, norm_mul, norm_zpow, hvec, norm_smul, norm_zpow,
        mul_pow]
      have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
      have hz : (‖q‖ ^ (-e₀)) ^ k = ‖q‖ ^ (-((k : ℤ) * e₀)) := by
        rw [← zpow_natCast, ← zpow_mul]; congr 1; ring
      rw [hz]
      have hnn : 0 ≤ ‖q‖ ^ (-((k : ℤ) * e₀)) := zpow_nonneg (norm_nonneg _) _
      calc ‖ATLINT.ext (N := N) w ((liftC γ n q : ℍ) : ℂ)‖ * ‖q‖ ^ (-((k : ℤ) * e₀))
          ≤ (Real.exp (supPsiX D x k w - lam) * ‖vecX (N := N) x ((liftC γ n q : ℍ) : ℂ)‖ ^ k) * ‖q‖ ^ (-((k : ℤ) * e₀)) :=
            mul_le_mul_of_nonneg_right hbad hnn
        _ = Real.exp (supPsiX D x k w - lam) * (‖q‖ ^ (-((k : ℤ) * e₀)) * ‖vecX (N := N) x ((liftC γ n q : ℍ) : ℂ)‖ ^ k) := by
            ring
  calc MeasureTheory.volume _ ≤ MeasureTheory.volume (Metric.ball q₂ ρ₂ ∩ {q | ‖F q‖ ≤ Real.exp (supPsiX D x k w - lam + k * GC Φc q)}) :=
        MeasureTheory.measure_mono hcover
    _ ≤ ENNReal.ofReal (MeasureTheory.volume.real (Metric.ball q₂ ρ₂) * (C₁ * (k + 1) + k * (m_hi - m_lo)) / lam) := hcheb
    _ ≤ ENNReal.ofReal (C * (k + 1) / lam) := by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ hlam.le
        rw [PLBANA.Setup.volumeReal_ball _ hρ₂0.le, hC]
        rw [show Real.pi * ρ₂ ^ 2 * (C₁ + (m_hi - m_lo)) * (k + 1) = Real.pi * ρ₂ ^ 2 * ((C₁ + (m_hi - m_lo)) * (k + 1)) by ring]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg hkR hosc0]

end GOODH2
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

section BDDH
open PLBANA

variable {D : ComplexPlaceDictionary N}

theorem psiX_bddAbove {x : Fin r → FC N} {k : ℕ} {w : FC N} (hx : XData D x) (hw : WData0 D x k w)
    [(CongruenceSubgroup.Gamma0 N).FiniteIndex] :
    BddAbove (Set.range fun τ : GenX D w => psiX D x k w τ) := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < (N : ℕ) := by exact_mod_cast hN
  obtain ⟨Sc, B, y₀, Y₁, hy₀, hcov⟩ := GLUE.cover_box_or_cusp (N := N) (N : ℝ)
  have hconj : ∀ σc : SL(2, ℤ), σc * ModularGroup.T ^ N * σc⁻¹ ∈ CongruenceSubgroup.Gamma0 N := fun σc => by
    have := CUSPATLAS.conj_T_zpow_mem_Gamma0 N σc
    rwa [zpow_natCast] at this
  have hΓ : ∀ σc : SL(2, ℤ), ((N : ℕ) : ℝ) ∈ (CUSPATLAS.conjGamma0 N σc).strictPeriods :=
    fun σc => CUSPATLAS.natCast_mem_strictPeriods_conjGamma0 N σc

  set Kbox : Set ℂ := {z : ℂ | |z.re| ≤ B ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁} with hKbox
  have hKc := GLUE.isCompact_box B y₀ Y₁
  have hKU : Kbox ⊆ UH := box_subset_UH hy₀
  obtain ⟨m_lo, m_hi, -, hbnd⟩ := exists_bounds_GX hx hKc hKU
  obtain ⟨CU, hCU⟩ := hKc.exists_bound_of_continuousOn ((analyticOnNhd_ext (D := D) hw.reg).continuousOn.mono hKU)

  have hcusp : ∀ σc : SL(2, ℤ), ∃ Cc : ℝ, ∀ τ : ℍ, τ ∈ GenX D w → ∀ z : ℍ, (N : ℝ) < z.im → τ = σc • z →
      psiX D x k w τ ≤ Cc := by
    intro σc
    set e₀ := e0 x hx.r_pos σc hNR (hΓ σc) with he₀
    obtain ⟨hΦan, hΦval, hΦne⟩ := PhiC_spec hx σc hN (hconj σc) hNR (hΓ σc)
    obtain ⟨hFan, hFval⟩ := FCw_spec hx hw σc hN (hconj σc) hNR (hΓ σc)
    set F := FCw (N := N) w σc N ((k : ℤ) * e₀) with hF
    set Φc := PhiC (N := N) x σc N e₀ with hΦc
    have hval : ∀ q ∈ Metric.ball (0 : ℂ) 1, q ≠ 0 →
        F q = ATLINT.ext (N := N) w ((liftC σc N q : ℍ) : ℂ) * q ^ (-((k : ℤ) * e₀)) ∧
        ∀ i, Φc q i = ATLINT.ext (N := N) (x i) ((liftC σc N q : ℍ) : ℂ) * q ^ (-e₀) :=
      fun q hq hq0 => ⟨hFval q hq hq0, hΦval q hq hq0⟩
    have hsub : Metric.closedBall (0 : ℂ) (1 / 2) ⊆ Metric.ball 0 1 := Metric.closedBall_subset_ball (by norm_num)
    obtain ⟨CF, hCF⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn (hFan.continuousOn.mono hsub)
    obtain ⟨CG, hCG⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn
      ((continuousOn_GC hΦan hΦne).mono hsub)
    refine ⟨|Real.log CF| + k * |CG|, fun τ hτ z hz hτz => ?_⟩
    obtain ⟨hq, hq0, hFq, -, hpsi⟩ := cusp_chart_pullback hx hw hN (hconj σc) hval τ
    set q := Function.Periodic.qParam N ((σc⁻¹ • τ : ℍ) : ℂ) with hqdef
    have hzq : σc⁻¹ • τ = z := by rw [hτz, inv_smul_smul]
    have hqsmall : ‖q‖ ≤ 1 / 2 := by
      rw [hqdef, hzq, Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
      have h1 : -2 * Real.pi * z.im / N ≤ -1 := by
        rw [div_le_iff₀ hNR]; nlinarith [Real.pi_gt_three, hz]
      calc Real.exp (-2 * Real.pi * z.im / N) ≤ Real.exp (-1) := Real.exp_le_exp.mpr h1
        _ ≤ 1 / 2 := by
            rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
            have := Real.add_one_le_exp (1 : ℝ)
            linarith
    have hqmem : q ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by rwa [Metric.mem_closedBall, dist_zero_right]
    have hgen : ATLINT.ext (N := N) w τ ≠ 0 := (mem_GenX_iff hw.reg τ).mp hτ
    have hFne : F q ≠ 0 := by rw [hFq]; exact mul_ne_zero hgen (zpow_ne_zero _ hq0)
    rw [← hpsi hτ, PLBANA.psi]
    have h1 : Real.log ‖F q‖ ≤ |Real.log CF| := by
      have hFpos : 0 < ‖F q‖ := norm_pos_iff.mpr hFne
      exact (Real.log_le_log hFpos (hCF q hqmem)).trans (le_abs_self _)
    have h2 : -(k * GC Φc q) ≤ k * |CG| := by
      have h3 : |GC Φc q| ≤ CG := by have := hCG q hqmem; rwa [Real.norm_eq_abs] at this
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [neg_abs_le (GC Φc q), abs_nonneg (GC Φc q), le_abs_self CG]
    linarith
  choose Cc hCc using hcusp
  refine ⟨|Real.log CU| + k * |m_lo| + ∑ σc ∈ Sc, |Cc σc|, ?_⟩
  rintro _ ⟨⟨τ, hτ⟩, rfl⟩
  obtain ⟨g, hg, hcase⟩ := hcov τ
  have hginv : psiX D x k w (g • τ) = psiX D x k w τ := by
    rw [psiX_eq_psi hw.reg, psiX_eq_psi hw.reg, PLBANA.psi, PLBANA.psi, GX, GX, ext_smul' hw.reg g hg]
    have : vecX (N := N) x ((g • τ : ℍ) : ℂ) = vecX (N := N) x τ := funext fun i => ext_smul' (fun τ => hx.reg τ i) g hg τ
    rw [this]
  have hgτ : (g • τ) ∈ GenX D w := by
    rw [mem_GenX_iff hw.reg, ext_smul' hw.reg g hg]; exact (mem_GenX_iff hw.reg τ).mp hτ
  have hsum : 0 ≤ ∑ σc ∈ Sc, |Cc σc| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  show psiX D x k w τ ≤ _
  rw [← hginv]
  rcases hcase with hb | ⟨σc, hσc, z, -, hzY, hgz⟩
  · have hmem : ((g • τ : ℍ) : ℂ) ∈ Kbox := by
      simp only [hKbox, Set.mem_setOf_eq, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; exact hb
    rw [psiX_eq_psi hw.reg, PLBANA.psi]
    have hgen : ATLINT.ext (N := N) w ((g • τ : ℍ) : ℂ) ≠ 0 := (mem_GenX_iff hw.reg _).mp hgτ
    have h1 : Real.log ‖ATLINT.ext (N := N) w ((g • τ : ℍ) : ℂ)‖ ≤ |Real.log CU| :=
      (Real.log_le_log (norm_pos_iff.mpr hgen) (hCU _ hmem)).trans (le_abs_self _)
    have h2 : -(k * GX (N := N) x ((g • τ : ℍ) : ℂ)) ≤ k * |m_lo| := by
      have := (hbnd _ hmem).1
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [neg_abs_le m_lo]
    linarith
  · have h := hCc σc (g • τ) hgτ z hzY hgz
    have h2 : Cc σc ≤ ∑ σ' ∈ Sc, |Cc σ'| :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun σ' => |Cc σ'|) (fun _ _ => abs_nonneg _) hσc)
    have hk : (0 : ℝ) ≤ k * |m_lo| := by positivity
    linarith [abs_nonneg (Real.log CU)]

end BDDH
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

section CUSPVAL
open PLBANA

variable {D : ComplexPlaceDictionary N}

theorem ord_eq_zero_of_ext_ne_zero {x : FC N} (hx0 : x ≠ 0) (τ : ℍ) (hx : x ∈ (D.pt τ).toValuationSubring)
    (hne : ATLINT.ext (N := N) x τ ≠ 0) : (D.pt τ).ord x = 0 := by
  obtain ⟨han, heq, -⟩ := ATLINT.ext_analyticAt D x τ hx
  have hmer := D.meromorphicOrderAt_realize τ x hx0
  rw [meromorphicOrderAt_congr heq, han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr hne] at hmer
  have he := D.ramification_pos τ
  have : ((D.ramification τ : ℤ) * (D.pt τ).ord x : ℤ) = 0 := by
    have h := hmer.symm
    simp only [ENat.map_zero, CharP.cast_eq_zero] at h
    exact_mod_cast h
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (by exact_mod_cast he.ne')
  · exact h

theorem phiU_le_supPsi_of_cuspidal (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (k : ℕ) (u : FB N) (hu : u ≠ 0) (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (hbdd : BddAbove (Set.range fun τ : Gen D σ u => psiU D σ s k u τ))
    (y : Place (AlgebraicClosure ℚ) (FB N)) (hyc : jB N ∉ y.toValuationSubring) (hne : secVal s y k u ≠ 0) :
    phiU σ s k u y ≤ supPsi D σ s k u := by
  classical
  have hr := L2.r_pos N s hs
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  set π := pivotIndex s y hr with hπ
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hrat := CUSPATLAS.isRational_FB (N := N) y
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < (N : ℕ) := by exact_mod_cast hN

  set zu : FB N := u * ((s π)⁻¹) ^ k with hzu
  set z : Fin r → FB N := fun i => s i * (s π)⁻¹ with hz
  have hpk : ((s π)⁻¹) ^ k ≠ 0 := pow_ne_zero _ (inv_ne_zero (hs0 π))
  have hzu0 : zu ≠ 0 := mul_ne_zero hu hpk
  have hz0 : ∀ i, z i ≠ 0 := fun i => mul_ne_zero (hs0 i) (inv_ne_zero (hs0 π))
  have hzumem : zu ∈ y.toValuationSubring := by
    have hord : 0 ≤ y.ord zu := by
      rw [hzu, y.ord_mul hu hpk, ← zpow_natCast, y.ord_zpow, y.ord_inv, L2.ord_pivot N s hs y hr]
      have := L2.neg_le_ord_of_mem _ huL hu y
      simp only [Finsupp.smul_apply, smul_eq_mul, neg_neg] at this ⊢
      linarith
    exact y.mem_of_ord_nonneg hzu0 hord
  have hzmem : ∀ i, z i ∈ y.toValuationSubring := fun i => (L2.ratio_mem N s hs y hr i).1
  have hsec : secVal s y k u = y.evalAt zu := by simp only [secVal, dif_pos hr, hπ, hzu]
  have hvec : ∀ i, evalVec s y i = y.evalAt (z i) := fun i => ((L2.ratio_mem N s hs y hr i).2.2).symm

  obtain ⟨w, hcomap, -, -⟩ := CUSPATLAS.exists_unique_place_over σ y
  have hyw : y.toValuationSubring = w.toValuationSubring.comap (phi N σ) := hcomap.symm
  have hc : IsCusp (⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_full N)⟩ : FC N) w := by
    show (jC N) ∉ w.toValuationSubring
    intro h
    apply hyc
    rw [hyw, ValuationSubring.mem_comap, CUSPATLAS.phi_jB]
    exact h
  obtain ⟨ι, γ, hratw, -, -, htend⟩ := CUSPATLAS.cusp_value_bridge N w hc
  have hmemw : ∀ v : FB N, v ∈ y.toValuationSubring → phi N σ v ∈ w.toValuationSubring := fun v hv => by
    rw [hyw, ValuationSubring.mem_comap] at hv; exact hv

  set Au : ℂ := w.evalAt (phi N σ zu) with hAu
  set Av : Fin r → ℂ := fun i => w.evalAt (phi N σ (z i)) with hAv
  have hAu_eq : σ (secVal s y k u) = Au := by rw [hsec, CUSPATLAS.evalAt_transport σ y w hyw hzumem]
  have hAv_eq : ∀ i, σ (evalVec s y i) = Av i := fun i => by rw [hvec i, CUSPATLAS.evalAt_transport σ y w hyw (hzmem i)]
  have hAu0 : Au ≠ 0 := by rw [← hAu_eq, map_ne_zero]; exact hne
  have hAvπ : Av π = 1 := by
    rw [← hAv_eq π, hvec π]
    have : z π = 1 := by rw [hz]; exact mul_inv_cancel₀ (hs0 π)
    rw [this, show (1 : FB N) = algebraMap (AlgebraicClosure ℚ) (FB N) 1 from (map_one _).symm, y.evalAt_algebraMap, map_one]
  have Tu : Filter.Tendsto (fun τ : ℍ => realize N ((phi N σ zu : FC N) : LaurentSeries ℂ) (γ • τ)) UpperHalfPlane.atImInfty (𝓝 Au) :=
    htend _ (CUSPATLAS.phi_ne_zero σ hzu0) (hmemw zu hzumem)
  have Tv : ∀ i, Filter.Tendsto (fun τ : ℍ => realize N ((phi N σ (z i) : FC N) : LaurentSeries ℂ) (γ • τ)) UpperHalfPlane.atImInfty (𝓝 (Av i)) :=
    fun i => htend _ (CUSPATLAS.phi_ne_zero σ (hz0 i)) (hmemw (z i) (hzmem i))

  have hΓ := CUSPATLAS.natCast_mem_strictPeriods_conjGamma0 N γ
  obtain ⟨Φu, Aᵤ, hAᵤ, -, -, -, hΦu_nz, hexp_u⟩ := ext_cusp_expansion' (D := D) (CUSPATLAS.phi_ne_zero σ hu) γ hNR hΓ
  have hexp_s := fun i => ext_cusp_expansion' (D := D) (CUSPATLAS.phi_ne_zero σ (hs0 i)) γ hNR hΓ
  choose Φs As hAs _h1 _h2 _h3 hΦs_nz hexp_s' using hexp_s
  obtain ⟨Φzu, Azu, hAzu, -, -, -, -, hexp_zu⟩ := ext_cusp_expansion' (D := D) (CUSPATLAS.phi_ne_zero σ hzu0) γ hNR hΓ
  have hexp_z := fun i => ext_cusp_expansion' (D := D) (CUSPATLAS.phi_ne_zero σ (hz0 i)) γ hNR hΓ
  choose Φz Az hAz _k1 _k2 _k3 _k4 hexp_z' using hexp_z
  set Astar : ℝ := max (max Aᵤ Azu) (max (Finset.univ.sup' Finset.univ_nonempty As) (Finset.univ.sup' Finset.univ_nonempty Az)) with hAstar
  have hAu_le : Aᵤ ≤ Astar := (le_max_left _ _).trans (le_max_left _ _)
  have hAzu_le : Azu ≤ Astar := (le_max_right _ _).trans (le_max_left _ _)
  have hAs_le : ∀ i, As i ≤ Astar := fun i =>
    ((Finset.le_sup' As (Finset.mem_univ i)).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hAz_le : ∀ i, Az i ≤ Astar := fun i =>
    ((Finset.le_sup' Az (Finset.mem_univ i)).trans (le_max_right _ _)).trans (le_max_right _ _)

  have hureg := ureg (D := D) σ k u hu huL
  have hsreg := (ATLINT.interiorInputs D σ s hs).reg
  have hratC := fun τ : ℍ => ATLINT.isRational_FC (D.pt τ)

  have hkey : ∀ τ : ℍ, Astar ≤ τ.im →
      (γ • τ) ∈ Gen D σ u ∧
      psiU D σ s k u (γ • τ) =
        Real.log ‖realize N ((phi N σ zu : FC N) : LaurentSeries ℂ) (γ • τ)‖ -
          (k : ℝ) * Real.log (⨆ i, ‖realize N ((phi N σ (z i) : FC N) : LaurentSeries ℂ) (γ • τ)‖) := by
    intro τ hτ
    set q : ℂ := Function.Periodic.qParam N (τ : ℂ) with hq
    have hq0 : q ≠ 0 := by rw [hq]; simp only [Function.Periodic.qParam]; exact Complex.exp_ne_zero _
    have hqmem : ∀ A : ℝ, A ≤ Astar → q ∈ Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * A / N)) := by
      intro A hA
      rw [Metric.mem_closedBall, dist_zero_right, hq, Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff_of_pos_right hNR]
      nlinarith [Real.pi_pos, hA.trans hτ]

    obtain ⟨hext_π, -⟩ := hexp_s' π τ ((hAs_le π).trans hτ) (hsreg _ π)
    have hP : ATLINT.ext (N := N) (phi N σ (s π)) ((γ • τ : ℍ) : ℂ) ≠ 0 := by
      rw [hext_π]; exact mul_ne_zero (zpow_ne_zero _ hq0) (hΦs_nz π q (hqmem _ (hAs_le π)))
    have hordπ : (D.pt (γ • τ)).ord (phi N σ (s π)) = 0 :=
      ord_eq_zero_of_ext_ne_zero (CUSPATLAS.phi_ne_zero σ (hs0 π)) _ (hsreg _ π) hP
    have hπinv : (phi N σ (s π))⁻¹ ∈ (D.pt (γ • τ)).toValuationSubring :=
      (D.pt (γ • τ)).mem_of_ord_nonneg (inv_ne_zero (CUSPATLAS.phi_ne_zero σ (hs0 π)))
        (by rw [(D.pt (γ • τ)).ord_inv, hordπ, neg_zero])
    have hzu_reg : phi N σ zu ∈ (D.pt (γ • τ)).toValuationSubring := by
      rw [hzu, map_mul, map_pow, map_inv₀]; exact mul_mem (hureg _) (pow_mem hπinv k)
    have hz_reg : ∀ i, phi N σ (z i) ∈ (D.pt (γ • τ)).toValuationSubring := fun i => by
      rw [hz]; simp only [map_mul, map_inv₀]; exact mul_mem (hsreg _ i) hπinv

    obtain ⟨hext_zu, hreal_zu⟩ := hexp_zu τ (hAzu_le.trans hτ) hzu_reg
    have hRu : realize N ((phi N σ zu : FC N) : LaurentSeries ℂ) (γ • τ) = ATLINT.ext (N := N) (phi N σ zu) ((γ • τ : ℍ) : ℂ) := by
      rw [hreal_zu, hext_zu]
    have hRz : ∀ i, realize N ((phi N σ (z i) : FC N) : LaurentSeries ℂ) (γ • τ) = ATLINT.ext (N := N) (phi N σ (z i)) ((γ • τ : ℍ) : ℂ) := by
      intro i
      obtain ⟨h1, h2⟩ := hexp_z' i τ ((hAz_le i).trans hτ) (hz_reg i)
      rw [h2, h1]

    set P : ℂ := (D.pt (γ • τ)).evalAt (phi N σ (s π)) with hPdef
    have hPext : ATLINT.ext (N := N) (phi N σ (s π)) ((γ • τ : ℍ) : ℂ) = P := ext_eq_evalAt (D := D) (fun τ => hsreg τ π) _
    have hP0 : P ≠ 0 := by rw [← hPext]; exact hP
    have hinv : (D.pt (γ • τ)).evalAt (phi N σ (s π))⁻¹ = P⁻¹ :=
      (D.pt (γ • τ)).evalAt_inv (hratC _) (CUSPATLAS.phi_ne_zero σ (hs0 π)) hordπ
    have hU : ATLINT.ext (N := N) (phi N σ zu) ((γ • τ : ℍ) : ℂ) = ATLINT.ext (N := N) (phi N σ u) ((γ • τ : ℍ) : ℂ) * P⁻¹ ^ k := by
      rw [(ATLINT.ext_analyticAt D _ _ hzu_reg).2.2, (ATLINT.ext_analyticAt D _ _ (hureg _)).2.2, hzu, map_mul, map_pow,
        map_inv₀, (D.pt (γ • τ)).evalAt_mul (hratC _) (hureg _) (pow_mem hπinv k), evalAt_pow' _ (hratC _) hπinv, hinv]
    have hV : ∀ i, ATLINT.ext (N := N) (phi N σ (z i)) ((γ • τ : ℍ) : ℂ) = ATLINT.ext (N := N) (phi N σ (s i)) ((γ • τ : ℍ) : ℂ) * P⁻¹ := by
      intro i
      rw [(ATLINT.ext_analyticAt D _ _ (hz_reg i)).2.2, (ATLINT.ext_analyticAt D _ _ (hsreg _ i)).2.2, hz]
      simp only [map_mul, map_inv₀]
      rw [(D.pt (γ • τ)).evalAt_mul (hratC _) (hsreg _ i) hπinv, hinv]

    obtain ⟨hext_u, -⟩ := hexp_u τ (hAu_le.trans hτ) (hureg _)
    have hUne : ATLINT.ext (N := N) (phi N σ u) ((γ • τ : ℍ) : ℂ) ≠ 0 := by
      rw [hext_u]; exact mul_ne_zero (zpow_ne_zero _ hq0) (hΦu_nz q (hqmem _ hAu_le))
    refine ⟨(mem_GenX_iff (D := D) hureg _).mpr hUne, ?_⟩

    rw [psiU, ← ext_eq_evalAt (D := D) hureg, hRu, hU]
    simp_rw [hRz, hV]
    have hΦ : ∀ i, Φint σ s ((γ • τ : ℍ) : ℂ) i = ATLINT.ext (N := N) (phi N σ (s i)) ((γ • τ : ℍ) : ℂ) := fun i => rfl
    simp_rw [hΦ]
    rw [norm_mul, norm_pow, Real.log_mul (norm_ne_zero_iff.mpr hUne) (pow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero hP0))),
      Real.log_pow]
    have hsup : (⨆ i, ‖ATLINT.ext (N := N) (phi N σ (s i)) ((γ • τ : ℍ) : ℂ) * P⁻¹‖)
        = (⨆ i, ‖ATLINT.ext (N := N) (phi N σ (s i)) ((γ • τ : ℍ) : ℂ)‖) * ‖P⁻¹‖ := by
      simp_rw [norm_mul]
      exact (Real.iSup_mul_of_nonneg (norm_nonneg P⁻¹) _).symm
    rw [hsup]
    have hMpos : 0 < ⨆ i, ‖ATLINT.ext (N := N) (phi N σ (s i)) ((γ • τ : ℍ) : ℂ)‖ := by
      have := norm_vecX_pos (xData_of (D := D) σ s hs) (γ • τ)
      rwa [pi_norm_eq_ciSup'] at this
    rw [Real.log_mul hMpos.ne' (norm_ne_zero_iff.mpr (inv_ne_zero hP0))]
    ring

  have hev : ∀ᶠ τ : ℍ in UpperHalfPlane.atImInfty,
      Real.log ‖realize N ((phi N σ zu : FC N) : LaurentSeries ℂ) (γ • τ)‖ -
          (k : ℝ) * Real.log (⨆ i, ‖realize N ((phi N σ (z i) : FC N) : LaurentSeries ℂ) (γ • τ)‖)
        ≤ supPsi D σ s k u := by
    rw [Filter.Eventually, UpperHalfPlane.atImInfty_mem]
    refine ⟨Astar, fun τ hτ => ?_⟩
    obtain ⟨hgen, hid⟩ := hkey τ hτ
    show _ ≤ supPsi D σ s k u
    rw [← hid]
    unfold supPsi
    exact le_ciSup hbdd ⟨γ • τ, hgen⟩
  have hlim : Filter.Tendsto (fun τ : ℍ =>
      Real.log ‖realize N ((phi N σ zu : FC N) : LaurentSeries ℂ) (γ • τ)‖ -
        (k : ℝ) * Real.log (⨆ i, ‖realize N ((phi N σ (z i) : FC N) : LaurentSeries ℂ) (γ • τ)‖))
      UpperHalfPlane.atImInfty (𝓝 (Real.log ‖Au‖ - (k : ℝ) * Real.log (⨆ i, ‖Av i‖))) := by
    have T1 : Filter.Tendsto (fun τ : ℍ => Real.log ‖realize N ((phi N σ zu : FC N) : LaurentSeries ℂ) (γ • τ)‖)
        UpperHalfPlane.atImInfty (𝓝 (Real.log ‖Au‖)) :=
      (Real.continuousAt_log (norm_ne_zero_iff.mpr hAu0)).tendsto.comp Tu.norm
    have T2v : Filter.Tendsto (fun τ : ℍ => fun i => realize N ((phi N σ (z i) : FC N) : LaurentSeries ℂ) (γ • τ))
        UpperHalfPlane.atImInfty (𝓝 Av) := tendsto_pi_nhds.mpr Tv
    have hAvpos : 0 < ‖Av‖ := by
      refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ?_
      calc (1 : ℝ) = ‖Av π‖ := by rw [hAvπ, norm_one]
        _ ≤ ‖Av‖ := norm_le_pi_norm Av π
    have T2 : Filter.Tendsto (fun τ : ℍ => Real.log (⨆ i, ‖realize N ((phi N σ (z i) : FC N) : LaurentSeries ℂ) (γ • τ)‖))
        UpperHalfPlane.atImInfty (𝓝 (Real.log (⨆ i, ‖Av i‖))) := by
      have := (Real.continuousAt_log hAvpos.ne').tendsto.comp T2v.norm
      rw [pi_norm_eq_ciSup'] at this
      refine this.congr fun τ => ?_
      simp only [Function.comp]
      rw [pi_norm_eq_ciSup']
    exact T1.sub (T2.const_mul _)
  have hphi : phiU σ s k u y = Real.log ‖Au‖ - (k : ℝ) * Real.log (⨆ i, ‖Av i‖) := by
    unfold phiU
    rw [hAu_eq]
    simp_rw [hAv_eq]
  rw [hphi]
  haveI : (UpperHalfPlane.atImInfty).NeBot := by
    rw [Filter.neBot_iff]
    intro hbot
    have hmem : (∅ : Set ℍ) ∈ UpperHalfPlane.atImInfty := by rw [hbot]; exact Filter.mem_bot
    obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hmem
    have hpos : 0 < max A 1 := lt_max_of_lt_right one_pos
    refine hA ⟨Complex.I * ((max A 1 : ℝ) : ℂ), by simpa using hpos⟩ ?_
    show A ≤ (Complex.I * ((max A 1 : ℝ) : ℂ)).im
    simp
  exact le_of_tendsto hlim hev

end CUSPVAL
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"
section CUSPRATIO

variable {D : ComplexPlaceDictionary N}

end CUSPRATIO
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

end PLB
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace PLBSEP
open CUSPATLAS ATLINT GLUE PLB

variable {N : ℕ} [NeZero N] {r : ℕ}

def wedge {r : ℕ} (y x : Fin r → ℂ) : Fin r × Fin r → ℂ := fun q => y q.1 * x q.2 - y q.2 * x q.1

def pchd {r : ℕ} (y x : Fin r → ℂ) : ℝ := ‖wedge y x‖ / (‖y‖ * ‖x‖)

omit [NeZero N] in
theorem pchd_nonneg (y x : Fin r → ℂ) : 0 ≤ pchd y x := by
  unfold pchd; positivity

omit [NeZero N] in
theorem wedge_self_smul (x : Fin r → ℂ) (c : ℂ) : wedge (c • x) x = 0 := by
  funext q; simp only [wedge, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; ring

omit [NeZero N] in

theorem exists_smul_of_wedge_eq_zero {y x : Fin r → ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (h : wedge y x = 0) :
    ∃ c : ℂ, c ≠ 0 ∧ y = c • x := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra hall; push_neg at hall; exact hx (funext hall)
  refine ⟨y j / x j, ?_, ?_⟩
  · intro h0
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    ·
      apply hy; funext i
      have := congrFun h (i, j)
      simp only [wedge, Pi.zero_apply] at this

      rw [h0, zero_mul, sub_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hj
    · exact hj h0
  · funext i
    have := congrFun h (i, j)
    simp only [wedge, Pi.zero_apply] at this
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination this

omit [NeZero N] in
theorem pchd_eq_zero_iff {y x : Fin r → ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    pchd y x = 0 ↔ ∃ c : ℂ, c ≠ 0 ∧ y = c • x := by
  unfold pchd
  rw [div_eq_zero_iff, norm_eq_zero]
  constructor
  · rintro (h | h)
    · exact exists_smul_of_wedge_eq_zero hx hy h
    · exfalso
      rcases mul_eq_zero.mp h with h | h
      · exact hy (norm_eq_zero.mp h)
      · exact hx (norm_eq_zero.mp h)
  · rintro ⟨c, -, rfl⟩
    exact Or.inl (wedge_self_smul x c)

omit [NeZero N] in
theorem continuous_wedge : Continuous (fun p : (Fin r → ℂ) × (Fin r → ℂ) => wedge p.1 p.2) := by
  apply continuous_pi; intro q
  simp only [wedge]
  fun_prop

end PLBSEP
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace PLBSEP
open CUSPATLAS ATLINT GLUE PLB

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem exists_place_ne_cuspInftyBar : ∃ v : Place (AlgebraicClosure ℚ) (FB N), v ≠ cuspInftyBar N := by
  classical
  have hcurve := ModularCurve.isCurveOver_modularFunctionFieldBar N
  have hj0 : jB N ≠ 0 := fun h => ATLINT.jB_notMem (N := N) (by rw [h]; exact zero_mem _)
  obtain ⟨Dj, hDj, hdeg⟩ := hcurve.toHasPrincipalDivisors.exists_divisor _ hj0
  have hinf : Dj (cuspInftyBar N) < 0 := by
    rw [hDj]
    by_contra h
    push_neg at h
    exact ATLINT.jB_notMem (N := N) ((cuspInftyBar N).mem_of_ord_nonneg hj0 h)
  by_contra hall
  push_neg at hall

  have hsupp : Dj.support ⊆ {cuspInftyBar N} := fun v _ => Finset.mem_singleton.mpr (hall v)
  have hD : Dj = Finsupp.single (cuspInftyBar N) (Dj (cuspInftyBar N)) := by
    ext v
    rw [hall v, Finsupp.single_eq_same]
  have : Divisor.degree Dj = Dj (cuspInftyBar N) := by
    rw [hD, Divisor.degree_single, Finsupp.single_eq_same, ModularCurve.deg_eq_one_modularFunctionFieldBar]
    simp
  rw [this] at hdeg
  exact absurd hdeg hinf.ne

theorem two_le_r (s : Fin r → FB N) (hs : IsEmbBasis N s) : 2 ≤ r := by
  classical
  have hr := L2.r_pos N s hs
  by_contra hlt
  push_neg at hlt
  have hr1 : r = 1 := by omega
  obtain ⟨v, hv⟩ := exists_place_ne_cuspInftyBar (N := N)
  obtain ⟨f, hf0, hfL, hford⟩ := PLBALG.exists_mem_riemannRochSpace_ord_add_eq_one N v
  have hEv : embDivisor N v = 0 := by simp [embDivisor, Finsupp.single_apply, Ne.symm hv]
  rw [hEv, add_zero] at hford
  have h1L : (1 : FB N) ∈ riemannRochSpace (embDivisor N) := by
    rw [mem_riemannRochSpace_iff]
    intro w; right
    rw [w.ord_one, neg_nonpos]
    simp only [embDivisor, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs <;> simp

  subst hr1
  set i₀ : Fin 1 := 0
  have hspan : ∀ g ∈ riemannRochSpace (embDivisor N), ∃ a : AlgebraicClosure ℚ,
      g = algebraMap (AlgebraicClosure ℚ) (FB N) a * s i₀ := by
    intro g hg
    rw [← hs.2] at hg
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hg
    refine ⟨c i₀, ?_⟩
    rw [← hc, Fin.sum_univ_one, Algebra.smul_def]
  obtain ⟨a, ha⟩ := hspan 1 h1L
  obtain ⟨b, hb⟩ := hspan f hfL
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [map_zero, zero_mul] at ha; exact one_ne_zero ha
  have hA0 : algebraMap (AlgebraicClosure ℚ) (FB N) a ≠ 0 := (map_ne_zero _).mpr ha0
  have hf : f = algebraMap (AlgebraicClosure ℚ) (FB N) (b / a) := by
    rw [map_div₀, eq_div_iff hA0]
    calc f * algebraMap (AlgebraicClosure ℚ) (FB N) a
        = algebraMap (AlgebraicClosure ℚ) (FB N) b * (algebraMap (AlgebraicClosure ℚ) (FB N) a * s i₀) := by rw [hb]; ring
      _ = algebraMap (AlgebraicClosure ℚ) (FB N) b := by rw [← ha, mul_one]
  have hba : b / a ≠ 0 := by
    intro h0; apply hf0; rw [hf, h0, map_zero]
  rw [hf, PLBALG.ord_algebraMap_eq_zero v hba] at hford
  exact zero_ne_one hford

theorem interior_ne_cusp_value (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (hs : IsEmbBasis N s) (τ : ℍ) (csp : Place (AlgebraicClosure ℚ) (FB N)) (hc : jB N ∉ csp.toValuationSubring) :
    ¬ ∃ c : ℂ, c ≠ 0 ∧ Φint σ s (τ : ℂ) = c • (fun i => σ (evalVec s csp i)) := by
  classical
  rintro ⟨c, hc0, hprop⟩
  have hr := L2.r_pos N s hs
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  set π := pivotIndex s csp hr with hπ
  have hreg := (ATLINT.interiorInputs D σ s hs).reg τ
  have hratC := ATLINT.isRational_FC (D.pt τ)
  have hV : ∀ i, Φint σ s τ i = (D.pt τ).evalAt (phi N σ (s i)) := fun i =>
    (ATLINT.ext_analyticAt D (phi N σ (s i)) τ (hreg i)).2.2
  have hx : ∀ i, evalVec s csp i = csp.evalAt (s i * (s π)⁻¹) := fun i => ((L2.ratio_mem N s hs csp hr i).2.2).symm
  have hxπ : evalVec s csp π = 1 := by
    rw [hx π, mul_inv_cancel₀ (hs0 π), show (1 : FB N) = algebraMap (AlgebraicClosure ℚ) (FB N) 1 from (map_one _).symm,
      csp.evalAt_algebraMap]
  have hpropi : ∀ i, Φint σ s τ i = c * σ (evalVec s csp i) := fun i => by
    have := congrFun hprop i; simpa [Pi.smul_apply, smul_eq_mul] using this
  have hVπ : (D.pt τ).evalAt (phi N σ (s π)) = c := by
    rw [← hV π, hpropi π, hxπ, map_one, mul_one]
  rcases CUSPATLAS.forall_mem_or_exists_comap σ (D.pt τ) with hall | ⟨y, hy⟩
  ·
    have hunit : ∀ y : FB N, y ≠ 0 → (D.pt τ).ord (phi N σ y) = 0 :=
      fun y hy => CUSPATLAS.ord_pt_eq_zero_of_forall_mem σ _ hall y hy

    haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (two_le_r s hs)
    obtain ⟨j, hj⟩ := exists_ne π
    set xj : AlgebraicClosure ℚ := evalVec s csp j with hxj
    set g : FB N := s j * (s π)⁻¹ - algebraMap (AlgebraicClosure ℚ) (FB N) xj with hg

    have hπinv : (phi N σ (s π))⁻¹ ∈ (D.pt τ).toValuationSubring := by rw [← map_inv₀]; exact hall _
    have hinv : (D.pt τ).evalAt (phi N σ (s π))⁻¹ = c⁻¹ := by
      rw [(D.pt τ).evalAt_inv hratC (CUSPATLAS.phi_ne_zero σ (hs0 π)) (hunit _ (hs0 π)), hVπ]
    have hratio : (D.pt τ).evalAt (phi N σ (s j * (s π)⁻¹)) = σ xj := by
      rw [map_mul, map_inv₀, (D.pt τ).evalAt_mul hratC (hreg j) hπinv, hinv, ← hV j, hpropi j, hxj]
      field_simp
    have hg0 : (D.pt τ).evalAt (phi N σ g) = 0 := by
      have h1 : phi N σ (s j * (s π)⁻¹) = phi N σ g + algebraMap ℂ (FC N) (σ xj) := by
        rw [hg, map_sub, CUSPATLAS.phi_algebraMap]; ring
      have h2 := L2.evalAt_add' (D.pt τ) hratC (hall g) ((D.pt τ).algebraMap_mem' (σ xj))
      rw [← h1, hratio, (D.pt τ).evalAt_algebraMap] at h2
      linear_combination -h2

    have hgz : g = 0 := by
      by_contra hne
      exact (D.pt τ).evalAt_ne_zero hratC (CUSPATLAS.phi_ne_zero σ hne) (hunit g hne) hg0

    have hdep : s j - xj • s π = 0 := by
      have : s j * (s π)⁻¹ = algebraMap (AlgebraicClosure ℚ) (FB N) xj := sub_eq_zero.mp (by rw [← hg]; exact hgz)
      rw [Algebra.smul_def, ← this, mul_assoc, inv_mul_cancel₀ (hs0 π), mul_one, sub_self]
    have hinj : Function.Injective ![j, π] := by
      intro a b h
      fin_cases a <;> fin_cases b
      · rfl
      · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_fin_one] at h
        exact absurd h hj
      · simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_fin_one] at h
        exact absurd h.symm hj
      · rfl
    have hpair : LinearIndependent (AlgebraicClosure ℚ) ![s j, s π] := by
      have h' := hs.1.comp ![j, π] hinj
      convert h' using 1
      funext i; fin_cases i <;> rfl
    have h2 := (LinearIndependent.pair_iff.mp hpair) 1 (-xj)
      (by rw [one_smul, _root_.neg_smul, ← sub_eq_add_neg]; exact hdep)
    exact one_ne_zero h2.1
  ·
    have hjy : jB N ∈ y.toValuationSubring := by
      rw [hy, ValuationSubring.mem_comap, CUSPATLAS.phi_jB]; exact ATLINT.jC_mem_pt D τ
    have hyc : y ≠ csp := fun h => hc (h ▸ hjy)

    obtain ⟨P, hP0, -, hvec⟩ := PLB.dict_values D σ s hs 0 1 y τ hy (one_mem _)
    have hprop2 : ∀ i, σ (evalVec s y i) = (c * P⁻¹) * σ (evalVec s csp i) := fun i => by
      rw [hvec i, hpropi i]; ring
    have hch : chordVec s y csp = 0 := by
      funext p
      apply σ.injective
      simp only [chordVec, map_sub, map_mul, map_zero, Pi.zero_apply, hprop2]
      ring
    exact ModularCurve.JZero.chordVec_ne_zero_of_ne N s hs y csp hyc hch

end PLBSEP
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace PLBSEP
open CUSPATLAS ATLINT GLUE PLB

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem continuous_smul_SL (γ : SL(2, ℤ)) : Continuous fun τ : ℍ => γ • τ := by
  rw [UpperHalfPlane.isEmbedding_coe.isInducing.continuous_iff]
  have h1 : ContinuousOn (PLBCUSP.mob γ) PLB.UH := fun z hz =>
    (PLBCUSP.differentiableAt_mob γ ⟨z, hz⟩).continuousAt.continuousWithinAt
  have h2 : Continuous fun τ : ℍ => PLBCUSP.mob γ (τ : ℂ) :=
    h1.comp_continuous UpperHalfPlane.continuous_coe (fun τ => PLB.coe_mem_UH τ)
  convert h2 using 1
  funext τ
  exact PLBCUSP.coe_smul_eq γ τ

omit [NeZero N] in
theorem continuousOn_pchd {X : Type} [TopologicalSpace X] {S : Set X} {f g : X → (Fin r → ℂ)}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S) (hf0 : ∀ x ∈ S, f x ≠ 0) (hg0 : ∀ x ∈ S, g x ≠ 0) :
    ContinuousOn (fun x => pchd (f x) (g x)) S := by
  unfold pchd
  refine ContinuousOn.div ?_ ((hf.norm).mul (hg.norm)) (fun x hx => mul_ne_zero (norm_ne_zero_iff.mpr (hf0 x hx))
    (norm_ne_zero_iff.mpr (hg0 x hx)))
  exact (continuous_wedge.comp_continuousOn (hf.prodMk hg)).norm

theorem unifsep_core_of_inj (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (hs : IsEmbBasis N s)
    (hinj : ∀ z₁ z₂ : ℍ, (∃ c : ℂ, c ≠ 0 ∧ Φint σ s (z₁ : ℂ) = c • Φint σ s (z₂ : ℂ)) → D.pt z₁ = D.pt z₂)
    {ι : Type} [Fintype ι] (Z : ι → Set ℂ) (hZ : ∀ j, IsCompact (Z j))
    (Λ : ι → ℂ → ℍ) (hΛ : ∀ j, ContinuousOn (fun z => ((Λ j z : ℍ) : ℂ)) (Z j))
    (V : ι → ℂ → (Fin r → ℂ)) (hV : ∀ j, ContinuousOn (V j) (Z j)) (hV0 : ∀ j, ∀ z ∈ Z j, V j z ≠ 0)
    (hVΦ : ∀ j, ∀ z ∈ Z j, ∃ c : ℂ, c ≠ 0 ∧ V j z = c • Φint σ s ((Λ j z : ℍ) : ℂ))
    (W : Set ℂ) (hW : IsCompact W) (B : ℂ → (Fin r → ℂ)) (hB : ContinuousOn B W) (hB0 : ∀ u ∈ W, B u ≠ 0)
    (κ : ℍ → ℂ) (hκ : Continuous κ)
    (hBΦ : ∀ u ∈ W, ∃ w : ℍ, κ w = u ∧ ∃ c : ℂ, c ≠ 0 ∧ B u = c • Φint σ s (w : ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ j, ∀ z ∈ Z j, ∀ u ∈ W,
      pchd (V j z) (B u) < eta → ∃ γ : CongruenceSubgroup.Gamma0 N, dist (κ ((γ : SL(2, ℤ)) • Λ j z)) u < ε := by
  classical

  have hper : ∀ j, ∃ eta : ℝ, 0 < eta ∧ ∀ z ∈ Z j, ∀ u ∈ W,
      pchd (V j z) (B u) < eta → ∃ γ : CongruenceSubgroup.Gamma0 N, dist (κ ((γ : SL(2, ℤ)) • Λ j z)) u < ε := by
    intro j
    set S : Set (ℂ × ℂ) := Z j ×ˢ W with hS
    have hSc : IsCompact S := (hZ j).prod hW

    have hΛ' : ContinuousOn (Λ j) (Z j) :=
      (UpperHalfPlane.isEmbedding_coe.isInducing.continuousOn_iff).mpr (hΛ j)

    have hg : ∀ γ : CongruenceSubgroup.Gamma0 N,
        ContinuousOn (fun p : ℂ × ℂ => dist (κ ((γ : SL(2, ℤ)) • Λ j p.1)) p.2) S := by
      intro γ
      have h1 : ContinuousOn (fun p : ℂ × ℂ => κ ((γ : SL(2, ℤ)) • Λ j p.1)) S :=
        (hκ.comp (continuous_smul_SL (γ : SL(2, ℤ)))).comp_continuousOn
          (hΛ'.comp continuous_fst.continuousOn (fun p hp => (Set.mem_prod.mp hp).1))
      exact continuous_dist.comp_continuousOn (h1.prodMk continuous_snd.continuousOn)
    set A : Set (ℂ × ℂ) := S ∩ ⋂ γ : CongruenceSubgroup.Gamma0 N,
      (S ∩ (fun p : ℂ × ℂ => dist (κ ((γ : SL(2, ℤ)) • Λ j p.1)) p.2) ⁻¹' Set.Ici ε) with hA
    have hAclosed : IsClosed A :=
      hSc.isClosed.inter (isClosed_iInter fun γ => (hg γ).preimage_isClosed_of_isClosed hSc.isClosed isClosed_Ici)
    have hAc : IsCompact A := hSc.of_isClosed_subset hAclosed Set.inter_subset_left

    have hF : ContinuousOn (fun p : ℂ × ℂ => pchd (V j p.1) (B p.2)) S :=
      continuousOn_pchd ((hV j).comp continuous_fst.continuousOn (fun p hp => (Set.mem_prod.mp hp).1))
        (hB.comp continuous_snd.continuousOn (fun p hp => (Set.mem_prod.mp hp).2))
        (fun p hp => hV0 j _ (Set.mem_prod.mp hp).1) (fun p hp => hB0 _ (Set.mem_prod.mp hp).2)

    have hpos : ∀ p ∈ A, 0 < pchd (V j p.1) (B p.2) := by
      rintro ⟨z, u⟩ ⟨hpS, hpI⟩
      obtain ⟨hz, hu⟩ := Set.mem_prod.mp hpS
      refine lt_of_le_of_ne (pchd_nonneg _ _) (fun h0 => ?_)

      obtain ⟨c₁, hc₁, h1⟩ := (pchd_eq_zero_iff (hB0 u hu) (hV0 j z hz)).mp h0.symm
      obtain ⟨w, hκw, c₂, hc₂, h2⟩ := hBΦ u hu
      obtain ⟨c₃, hc₃, h3⟩ := hVΦ j z hz
      have hprop : ∃ c : ℂ, c ≠ 0 ∧ Φint σ s ((Λ j z : ℍ) : ℂ) = c • Φint σ s (w : ℂ) := by
        refine ⟨c₃⁻¹ * c₁ * c₂, mul_ne_zero (mul_ne_zero (inv_ne_zero hc₃) hc₁) hc₂, ?_⟩
        have : Φint σ s ((Λ j z : ℍ) : ℂ) = c₃⁻¹ • V j z := by
          rw [h3, smul_smul, inv_mul_cancel₀ hc₃, one_smul]
        rw [this, h1, h2, smul_smul, smul_smul]
      have hpt := hinj _ _ hprop
      obtain ⟨γ, hγ⟩ := (ModularCurve.ComplexPlaceDictionary.pt_eq_pt_iff D _ _).mp hpt
      have hfar := Set.mem_iInter.mp hpI γ
      have hfar' : ε ≤ dist (κ ((γ : SL(2, ℤ)) • Λ j z)) u := (Set.mem_preimage.mp hfar.2)
      rw [hγ, hκw, dist_self] at hfar'
      exact absurd hfar' (not_le.mpr hε)

    by_cases hAe : A = ∅
    · refine ⟨1, one_pos, fun z hz u hu _ => ?_⟩
      by_contra hno
      push_neg at hno
      have : (z, u) ∈ A := by
        refine ⟨Set.mk_mem_prod hz hu, Set.mem_iInter.mpr fun γ => ⟨Set.mk_mem_prod hz hu, ?_⟩⟩
        exact Set.mem_preimage.mpr (Set.mem_Ici.mpr (hno γ))
      rw [hAe] at this
      exact this
    · obtain ⟨p₀, hp₀, hmin⟩ := hAc.exists_isMinOn (Set.nonempty_iff_ne_empty.mpr hAe) (hF.mono Set.inter_subset_left)
      refine ⟨pchd (V j p₀.1) (B p₀.2), hpos p₀ hp₀, fun z hz u hu hlt => ?_⟩
      by_contra hno
      push_neg at hno
      have hmem : (z, u) ∈ A := by
        refine ⟨Set.mk_mem_prod hz hu, Set.mem_iInter.mpr fun γ => ⟨Set.mk_mem_prod hz hu, ?_⟩⟩
        exact Set.mem_preimage.mpr (Set.mem_Ici.mpr (hno γ))
      have := hmin hmem
      simp only at this
      exact absurd hlt (not_lt.mpr this)
  choose eta heta hsep using hper
  by_cases hι : Nonempty ι
  · refine ⟨Finset.univ.inf' (Finset.univ_nonempty_iff.mpr hι) eta, ?_, fun j z hz u hu hlt => ?_⟩
    · rw [Finset.lt_inf'_iff]; exact fun j _ => heta j
    · exact hsep j z hz u hu (hlt.trans_le (Finset.inf'_le _ (Finset.mem_univ j)))
  · exact ⟨1, one_pos, fun j => (hι ⟨j⟩).elim⟩

end PLBSEP
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace PLBSEP
open CUSPATLAS ATLINT GLUE PLB

variable {N : ℕ} [NeZero N] {r : ℕ}

theorem exists_mem_lSpace_sub_single (E' : Divisor ℂ (FC N))
    (hE : E'.degree = 2 * (genusFF ℂ (FC N) : ℤ) + 1) (P Q : Place ℂ (FC N)) (hPQ : P ≠ Q) :
    ∃ f : FC N, f ≠ 0 ∧ f ∈ LSpace (E' - Finsupp.single P 1) ∧ Q.ord f + E' Q = 0 := by
  classical
  set g : ℕ := genusFF ℂ (FC N) with hg
  have hdeg1 : ∀ v : Place ℂ (FC N), (v.deg : ℤ) = 1 := fun v => by exact_mod_cast deg_eq_one_FC v
  set D₁ : Divisor ℂ (FC N) := E' - Finsupp.single P 1 with hD₁
  set D₂ : Divisor ℂ (FC N) := E' - Finsupp.single P 1 - Finsupp.single Q 1 with hD₂
  have hdeg₁ : D₁.degree = 2 * g := by rw [hD₁, map_sub, hE, Divisor.degree_single, hdeg1]; ring
  have hdeg₂ : D₂.degree = 2 * g - 1 := by
    rw [hD₂, map_sub, map_sub, hE, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]; ring
  have hell₁ : (ell D₁ : ℤ) = g + 1 := by
    have h := ell_eq_degree_add_one_sub_genusFF_FC N D₁ (by rw [hdeg₁]; omega)
    rw [hdeg₁] at h; rw [h]; ring
  have hell₂ : (ell D₂ : ℤ) = g := by
    have h := ell_eq_degree_add_one_sub_genusFF_FC N D₂ (by rw [hdeg₂])
    rw [hdeg₂] at h; rw [h]; ring
  have hD₁Q : D₁ Q = E' Q := by simp [hD₁, Finsupp.single_apply, hPQ]
  have hD₂Q : D₂ Q = E' Q - 1 := by simp [hD₂, Finsupp.single_apply, hPQ]
  have hD₂v : ∀ v, v ≠ Q → D₂ v = D₁ v := fun v hv => by simp [hD₁, hD₂, Finsupp.single_apply, Ne.symm hv]
  have hle : LSpace D₂ ≤ LSpace D₁ := by
    refine AlgebraicCurve.lSpace_mono (fun v => ?_)
    by_cases hv : v = Q
    · subst hv; rw [hD₁Q, hD₂Q]; omega
    · rw [hD₂v v hv]
  have hlt : LSpace D₂ < LSpace D₁ := by
    refine Submodule.lt_of_le_of_finrank_lt_finrank hle ?_
    have e1 : Module.finrank ℂ ↥(LSpace D₁) = ell D₁ := rfl
    have e2 : Module.finrank ℂ ↥(LSpace D₂) = ell D₂ := rfl
    rw [e1, e2]
    omega
  obtain ⟨f, hf₁, hf₂⟩ := SetLike.exists_of_lt hlt
  have hf0 : f ≠ 0 := by rintro rfl; exact hf₂ (zero_mem _)
  refine ⟨f, hf0, hf₁, ?_⟩
  have hf₁' := hf₁
  have hf₂' := hf₂
  rw [show LSpace D₁ = riemannRochSpace D₁ from rfl, mem_riemannRochSpace_iff] at hf₁'
  rw [show LSpace D₂ = riemannRochSpace D₂ from rfl, mem_riemannRochSpace_iff] at hf₂'
  push_neg at hf₂'
  obtain ⟨v, -, hv⟩ := hf₂'
  have h1 := (hf₁' Q).resolve_left hf0
  rw [hD₁Q] at h1
  by_cases hvw : v = Q
  · subst hvw
    rw [hD₂Q] at hv
    omega
  · have := (hf₁' v).resolve_left hf0
    rw [hD₂v v hvw] at hv
    omega

set_option maxHeartbeats 16000000 in

theorem inj_all (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (z₁ z₂ : ℍ) (h : ∃ c : ℂ, c ≠ 0 ∧ Φint σ s (z₁ : ℂ) = c • Φint σ s (z₂ : ℂ)) : D.pt z₁ = D.pt z₂ := by
  classical
  by_contra hne12
  obtain ⟨c, hc0, hprop⟩ := h

  have hU := fun v => exists_unique_place_over (N := N) σ v
  choose lift hlift_comap hlift_ord hlift_uniq using hU
  have hlift_inj : Function.Injective lift := fun v v' h =>
    Place.ext ((hlift_comap v).symm.trans (h ▸ hlift_comap v'))
  have hlift_new : ∀ w : Place ℂ (FC N), (∀ v, lift v ≠ w) →
      ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
        w.toValuationSubring.comap (phi N σ) ≠ v.toValuationSubring := by
    intro w hw v h
    exact hw v (hlift_uniq v w h).symm

  letI : Algebra (AlgebraicClosure ℚ) ℂ := σ.toAlgebra
  letI : Algebra ↥(modularFunctionFieldBar N) (FC N) := (phi N σ).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (FC N) := ((algebraMap ℂ (FC N)).comp σ).toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ (FC N) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (FC N) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      show ((algebraMap ℂ (FC N)).comp σ) c = phi N σ (algebraMap (AlgebraicClosure ℚ) _ c)
      rw [phi_algebraMap]; rfl
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI : IsCurveOver ℂ (FC N) := ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull ℂ N
  have hrange : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionFieldFull N),
      (⟨coeffEmb ℂ y, coeffEmb_mem_laurentBaseChange ℂ hy⟩ : FC N) ∈
        Set.range (algebraMap ↥(modularFunctionFieldBar N) (FC N)) := fun y hy =>
    ⟨⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩,
      phi_coeffEmb σ y hy⟩
  have hgen : IntermediateField.adjoin ℂ (Set.range (algebraMap ↥(modularFunctionFieldBar N) (FC N))) = ⊤ := by
    apply top_le_iff.mp
    rw [← ModularCurve.adjoin_jBar_jNBar_eq_top ℂ N]
    apply IntermediateField.adjoin.mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h <;> rw [h]
    · exact hrange jq (jq_mem_full N)
    · exact hrange (qExpand ℚ N jq) (jqd_mem_full N (dvd_refl N))
  have hfg := ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar N
  have hfg' : ∃ x : FC N, Transcendental ℂ x ∧ FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set (FC N))) (FC N) :=
    ⟨_, ModularCurve.transcendental_coeffEmb_jq ℂ N, ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full ℂ N⟩

  have hgg : genusFF ℂ (FC N) = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed
      (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) ℂ (FC N) hfg hfg' hgen

  have hembs : embDivisor N = Finsupp.single (cuspInftyBar N) (embDegree N : ℤ) := by
    rw [embDivisor, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hmapEC : Finsupp.mapDomain lift (embDivisor N) =
      Finsupp.single (lift (cuspInftyBar N)) (embDegree N : ℤ) := by
    rw [hembs, Finsupp.mapDomain_single]
  set EC : Divisor ℂ (FC N) := Finsupp.single (lift (cuspInftyBar N)) (embDegree N : ℤ) with hEC
  have hdegEC : EC.degree = 2 * (genusFF ℂ (FC N) : ℤ) + 1 := by
    rw [hEC, Divisor.degree_single, deg_eq_one_FC, hgg, embDegree]
    push_cast
    ring

  have hnotinf : ∀ τ : ℍ, D.pt τ ≠ lift (cuspInftyBar N) := by
    intro τ h
    have hc : (D.pt τ).toValuationSubring.comap (phi N σ) = (cuspInftyBar N).toValuationSubring := by
      rw [h]; exact hlift_comap _
    have : jB N ∈ (cuspInftyBar N).toValuationSubring := by
      rw [← hc, ValuationSubring.mem_comap, phi_jB]; exact ATLINT.jC_mem_pt D τ
    exact ATLINT.jB_notMem this
  have hEC0 : ∀ τ : ℍ, EC (D.pt τ) = 0 := fun τ => by
    rw [hEC, Finsupp.single_apply, if_neg (Ne.symm (hnotinf τ))]

  obtain ⟨f, hf0, hfL, hford⟩ := exists_mem_lSpace_sub_single EC hdegEC (D.pt z₁) (D.pt z₂) hne12
  rw [hEC0, add_zero] at hford

  have hord1 : 0 < (D.pt z₁).ord f := by
    have := hfL
    rw [show LSpace (EC - Finsupp.single (D.pt z₁) 1) = riemannRochSpace (EC - Finsupp.single (D.pt z₁) 1) from rfl,
      mem_riemannRochSpace_iff] at this
    have h1 := (this (D.pt z₁)).resolve_left hf0
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same, hEC0] at h1
    omega

  have hfLE : f ∈ LSpace (K := ℂ) EC := by
    refine AlgebraicCurve.lSpace_mono (fun v => ?_) hfL
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hfspan : f ∈ Submodule.span ℂ (Set.range fun i => phi N σ (s i)) := by
    have hfL := hfLE
    have hfL' : f ∈ LSpace (K := ℂ) (Finsupp.mapDomain lift (embDivisor N)) := by rw [hmapEC]; exact hfL
    have hspan := AlgebraicCurve.lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
      (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) ℂ (FC N) hfg hfg' hgen lift hlift_ord hlift_inj hlift_new
      (embDivisor N) hfL'
    refine Submodule.span_le.mpr ?_ hspan
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by
      rw [hs.2]; exact hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hy'
    show phi N σ y ∈ _
    rw [← hc, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, map_mul, phi_algebraMap, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hfspan

  have hreg := (ATLINT.interiorInputs D σ s hs).reg
  have hval : ∀ τ : ℍ, f ∈ (D.pt τ).toValuationSubring ∧ (D.pt τ).evalAt f = ∑ i, a i * Φint σ s (τ : ℂ) i := by
    intro τ
    obtain ⟨hmem, hv⟩ := ATLINT.evalAt_sum_smul' (D.pt τ) (ATLINT.isRational_FC _) Finset.univ a
      (fun i => phi N σ (s i)) (fun i _ => hreg τ i)
    rw [ha] at hmem hv
    refine ⟨hmem, ?_⟩
    rw [hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (ATLINT.ext_analyticAt D (phi N σ (s i)) τ (hreg τ i)).2.2]
    rfl
  have hv1 : (D.pt z₁).evalAt f = 0 := by
    rw [← L2.evalAt_zero' (D.pt z₁)]
    exact (D.pt z₁).evalAt_congr (hval z₁).1 (zero_mem _) (Or.inr (by simpa using hord1))
  have hv2 : (D.pt z₂).evalAt f ≠ 0 := (D.pt z₂).evalAt_ne_zero (ATLINT.isRational_FC _) hf0 hford

  have hsum : ∑ i, a i * Φint σ s (z₁ : ℂ) i = c * ∑ i, a i * Φint σ s (z₂ : ℂ) i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hprop, Pi.smul_apply, smul_eq_mul]; ring
  rw [(hval z₁).2, hsum] at hv1
  rw [(hval z₂).2] at hv2
  exact hv2 ((mul_eq_zero.mp hv1).resolve_left hc0)

theorem unifsep_core (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (hs : IsEmbBasis N s)
    {ι : Type} [Fintype ι] (Z : ι → Set ℂ) (hZ : ∀ j, IsCompact (Z j))
    (Λ : ι → ℂ → ℍ) (hΛ : ∀ j, ContinuousOn (fun z => ((Λ j z : ℍ) : ℂ)) (Z j))
    (V : ι → ℂ → (Fin r → ℂ)) (hV : ∀ j, ContinuousOn (V j) (Z j)) (hV0 : ∀ j, ∀ z ∈ Z j, V j z ≠ 0)
    (hVΦ : ∀ j, ∀ z ∈ Z j, ∃ c : ℂ, c ≠ 0 ∧ V j z = c • Φint σ s ((Λ j z : ℍ) : ℂ))
    (W : Set ℂ) (hW : IsCompact W) (B : ℂ → (Fin r → ℂ)) (hB : ContinuousOn B W) (hB0 : ∀ u ∈ W, B u ≠ 0)
    (κ : ℍ → ℂ) (hκ : Continuous κ)
    (hBΦ : ∀ u ∈ W, ∃ w : ℍ, κ w = u ∧ ∃ c : ℂ, c ≠ 0 ∧ B u = c • Φint σ s (w : ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ j, ∀ z ∈ Z j, ∀ u ∈ W,
      pchd (V j z) (B u) < eta → ∃ γ : CongruenceSubgroup.Gamma0 N, dist (κ ((γ : SL(2, ℤ)) • Λ j z)) u < ε :=
  unifsep_core_of_inj D σ s hs (fun z₁ z₂ h => inj_all D σ s hs z₁ z₂ h) Z hZ Λ hΛ V hV hV0 hVΦ W hW B hB hB0 κ hκ hBΦ hε

end PLBSEP
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

section
open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace PLBG
open CUSPATLAS ATLINT AlgebraicCurve ModularCurve MeasureTheory Metric UpperHalfPlane
open scoped Topology ENNReal MatrixGroups NNReal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000

section Engine
variable {r : ℕ}

theorem pi_norm_eq_ciSup (v : Fin r → ℂ) : ‖v‖ = ⨆ i, ‖v i‖ := by
  rcases isEmpty_or_nonempty (Fin r) with h | h
  · rw [Real.iSup_of_isEmpty, Pi.norm_def]
    simp
  · apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg fun i => norm_nonneg _)).2 fun i => ?_
      exact le_ciSup (Finite.bddAbove_range fun i => ‖v i‖) i
    · exact ciSup_le fun i => norm_le_pi_norm v i

theorem exists_finset_cover {K : Set ℂ} (hK : IsCompact K) (hKim : ∀ z ∈ K, 0 < z.im) :
    ∃ T : Finset ℂ, (∀ t ∈ T, 0 < t.im) ∧ (∀ z ∈ K, ∃ t ∈ T, z ∈ closedBall t (t.im / 16)) ∧ (∀ t ∈ T, t ∈ K) := by
  obtain ⟨T, hTK, hcov⟩ := hK.elim_nhds_subcover (fun t => closedBall t (t.im / 16))
    (fun t ht => closedBall_mem_nhds t (by linarith [hKim t ht]))
  refine ⟨T, fun t ht => hKim t (hTK t ht), fun z hz => ?_, hTK⟩
  obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.mp (hcov hz)
  exact ⟨t, ht, hzt⟩

theorem norm_qParam_le_of_le_im {w r₀ : ℝ} (hw : 0 < w) (hr₀ : 0 < r₀) :
    ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → ‖Function.Periodic.qParam w (τ : ℂ)‖ ≤ r₀ := by
  refine ⟨-(w * Real.log r₀) / (2 * Real.pi), fun τ hτ => ?_⟩
  rw [Function.Periodic.norm_qParam, ← Real.exp_log hr₀, Real.exp_le_exp, UpperHalfPlane.coe_im]
  rw [div_le_iff₀ (by positivity)] at hτ
  rw [div_le_iff₀ hw]
  nlinarith [Real.pi_pos]

theorem exists_coset_reps' (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    ∃ S₀ : Finset SL(2, ℤ), ∀ g : SL(2, ℤ), ∃ γ ∈ Γ, ∃ s₀ ∈ S₀, g = γ * s₀ := by
  classical
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : SL(2, ℤ) ⧸ Γ => (Quotient.out q)⁻¹, fun g => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ g⁻¹
  refine ⟨h, h.2, (Quotient.out ((g⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Γ))⁻¹,
    Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
  rw [hh, mul_inv_rev, inv_inv, mul_inv_cancel_left]

theorem volume_ball_inter_hyperplane (w : Fin r → ℂ) (hw : w ≠ 0) :
    volume {b : Fin r → ℂ | b ∈ ball 0 1 ∧ ∑ j, w j * b j = 0} = 0 := by
  refine nonpos_iff_eq_zero.1 ?_
  have h := Complex.volume_ball_inter_norm_sum_mul_le w hw 0
  rw [zero_div, zero_pow two_ne_zero, ENNReal.ofReal_zero, zero_mul] at h
  refine (measure_mono ?_).trans h
  rintro b ⟨hb, h0⟩
  refine ⟨hb, ?_⟩
  have : ∑ j, b j * w j = ∑ j, w j * b j := Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [this, h0, norm_zero]

theorem exists_algebraic_mem {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (σ : F →+* ℂ)
    {G : Set (Fin r → ℂ)} (hG : IsOpen G)
    (hvol : volume (ball (0 : Fin r → ℂ) 1 ∩ Gᶜ) < volume (ball (0 : Fin r → ℂ) 1)) :
    ∃ e : Fin r → F, (fun i => σ (e i)) ∈ ball (0 : Fin r → ℂ) 1 ∩ G := by
  have hne : (ball (0 : Fin r → ℂ) 1 ∩ G).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hsub : ball (0 : Fin r → ℂ) 1 ⊆ ball 0 1 ∩ Gᶜ := fun b hb => ⟨hb, fun hbG => by
      have : b ∈ ball (0 : Fin r → ℂ) 1 ∩ G := ⟨hb, hbG⟩
      rw [h] at this
      exact this⟩
    exact absurd (measure_mono hsub) (not_le.2 hvol)
  obtain ⟨b, hb, hbσ⟩ := RingHom.exists_mem_forall_mem_range_of_isOpen σ (isOpen_ball.inter hG) hne
  choose e he using hbσ
  refine ⟨e, ?_⟩
  have : (fun i => σ (e i)) = b := funext he
  rw [this]
  exact hb

def chord (Φ : ℂ → (Fin r → ℂ)) (x : Fin r → ℂ) (p : Fin r) : ℂ → (Fin r → ℂ) :=
  fun z i => Φ z i - Φ z p * x i

def pencilCov (x : Fin r → ℂ) (p : Fin r) (b : Fin r → ℂ) : Fin r → ℂ :=
  fun i => b i - (∑ j, x j * b j) * (if i = p then 1 else 0)

theorem pencilCov_apply (x : Fin r → ℂ) (p : Fin r) (b y : Fin r → ℂ) :
    ∑ i, y i * pencilCov x p b i = ∑ i, b i * (y i - y p * x i) := by
  classical
  simp only [pencilCov, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have : ∑ i, b i * (y p * x i) = y p * ∑ j, x j * b j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem pencilCov_chart (Φ : ℂ → (Fin r → ℂ)) (x : Fin r → ℂ) (p : Fin r) (b : Fin r → ℂ) (z : ℂ) :
    ∑ i, Φ z i * pencilCov x p b i = ∑ i, b i * chord Φ x p z i := by
  rw [pencilCov_apply]; rfl

theorem chord_sub_le {Φ : ℂ → (Fin r → ℂ)} {x : Fin r → ℂ} (hx : ‖x‖ ≤ 1) (p : Fin r) {y z : ℂ} {L : ℝ}
    (hL : ‖Φ y - Φ z‖ ≤ L * ‖y - z‖) : ‖chord Φ x p y - chord Φ x p z‖ ≤ 2 * L * ‖y - z‖ := by
  have hL0 : 0 ≤ L * ‖y - z‖ := (norm_nonneg _).trans hL
  have hL2 : 0 ≤ 2 * L * ‖y - z‖ := by nlinarith
  refine (pi_norm_le_iff_of_nonneg hL2).2 fun i => ?_
  simp only [chord, Pi.sub_apply]
  have h1 : ‖Φ y i - Φ z i‖ ≤ L * ‖y - z‖ := (norm_le_pi_norm (Φ y - Φ z) i).trans hL
  have h2 : ‖Φ y p - Φ z p‖ ≤ L * ‖y - z‖ := (norm_le_pi_norm (Φ y - Φ z) p).trans hL
  have h3 : ‖x i‖ ≤ 1 := (norm_le_pi_norm x i).trans hx
  calc ‖Φ y i - Φ y p * x i - (Φ z i - Φ z p * x i)‖
      = ‖(Φ y i - Φ z i) - (Φ y p - Φ z p) * x i‖ := by ring_nf
    _ ≤ ‖Φ y i - Φ z i‖ + ‖(Φ y p - Φ z p) * x i‖ := norm_sub_le _ _
    _ ≤ L * ‖y - z‖ + L * ‖y - z‖ * 1 := by
        rw [norm_mul]; exact add_le_add h1 (mul_le_mul h2 h3 (norm_nonneg _) hL0)
    _ = 2 * L * ‖y - z‖ := by ring

theorem far_piece {Φ : ℂ → (Fin r → ℂ)} {x : Fin r → ℂ} (hx : ‖x‖ ≤ 1) (p : Fin r)
    {c : ℂ} {ρ ρ₁ : ℝ} (hρ : ρ < ρ₁) {L : NNReal} (hL : ∀ i, LipschitzOnWith L (fun z => Φ z i) (closedBall c ρ₁))
    (K : Set ℂ) (hK : K ⊆ closedBall c ρ) {η₀ : ℝ} (hη : 0 < η₀) (hηK : ∀ z ∈ K, η₀ ≤ ‖chord Φ x p z‖) :
    volume {b : Fin r → ℂ | b ∈ ball 0 1 ∧ ∃ z ∈ K, ∑ j, b j * chord Φ x p z j = 0}
      ≤ ENNReal.ofReal ((r * (2 * (r * (L : ℝ))) / η₀) ^ 2 / Real.pi) * volume (ball (0 : Fin r → ℂ) 1) * volume K := by
  refine Complex.volume_ball_inter_exists_sum_mul_eq_zero_le_mul_volume (chord Φ x p) K hη hηK ?_
  intro z hz
  refine ⟨ρ₁ - ρ, by linarith, fun y hy => ?_⟩
  have hz₁ : z ∈ closedBall c ρ₁ := closedBall_subset_closedBall hρ.le (hK hz)
  have hy₁ : y ∈ closedBall c ρ₁ := by
    rw [mem_closedBall] at hy hz₁ ⊢
    have := mem_closedBall.1 (hK hz)
    linarith [dist_triangle y z c]
  refine chord_sub_le hx p ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Pi.sub_apply]
  refine ((hL i).norm_sub_le hy₁ hz₁).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have : (0 : ℝ) ≤ L := L.coe_nonneg
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0; exact (IsEmpty.false i).elim
  · have : (1 : ℝ) ≤ r := by exact_mod_cast hpos
    nlinarith

theorem isClosed_near_bad {Ψw : ℂ → (Fin r × Fin r → ℂ)} {w : ℂ} {ρ₁ : ℝ}
    (hc : ContinuousOn Ψw (closedBall w ρ₁)) (p : Fin r) :
    IsClosed {b : Fin r → ℂ | ∃ z ∈ closedBall w ρ₁, ∑ j, b j * Ψw z (p, j) = 0} := by
  haveI : CompactSpace (closedBall w ρ₁) := isCompact_iff_compactSpace.1 (isCompact_closedBall w ρ₁)
  have hc' : Continuous fun z : closedBall w ρ₁ => Ψw z := hc.restrict
  let F : (Fin r → ℂ) × (closedBall w ρ₁) → ℂ := fun q => ∑ j, q.1 j * Ψw q.2 (p, j)
  have hF : Continuous F := continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp continuous_fst).mul (((continuous_apply (p, j)).comp hc').comp continuous_snd)
  have himage : {b : Fin r → ℂ | ∃ z ∈ closedBall w ρ₁, ∑ j, b j * Ψw z (p, j) = 0}
      = Prod.fst '' {q : (Fin r → ℂ) × (closedBall w ρ₁) | F q = 0} := by
    ext b
    constructor
    · rintro ⟨z, hz, h1⟩
      exact ⟨(b, ⟨z, hz⟩), h1, rfl⟩
    · rintro ⟨⟨b', z⟩, h1, rfl⟩
      exact ⟨z.1, z.2, h1⟩
  rw [himage]
  exact isClosedMap_fst_of_compactSpace _ (isClosed_eq hF continuous_const)

theorem isClosed_far_bad {C : ℂ → (Fin r → ℂ)} {K : Set ℂ} (hK : IsCompact K) (hc : ContinuousOn C K) :
    IsClosed {b : Fin r → ℂ | ∃ z ∈ K, ∑ j, b j * C z j = 0} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hc' : Continuous fun z : K => C z := hc.restrict
  let F : (Fin r → ℂ) × K → ℂ := fun q => ∑ j, q.1 j * C q.2 j
  have hF : Continuous F := continuous_finsetSum _ fun j _ =>
    ((continuous_apply j).comp continuous_fst).mul (((continuous_apply j).comp hc').comp continuous_snd)
  have himage : {b : Fin r → ℂ | ∃ z ∈ K, ∑ j, b j * C z j = 0}
      = Prod.fst '' {q : (Fin r → ℂ) × K | F q = 0} := by
    ext b
    constructor
    · rintro ⟨z, hz, h1⟩
      exact ⟨(b, ⟨z, hz⟩), h1, rfl⟩
    · rintro ⟨⟨b', z⟩, h1, rfl⟩
      exact ⟨z.1, z.2, h1⟩
  rw [himage]
  exact isClosedMap_fst_of_compactSpace _ (isClosed_eq hF continuous_const)

theorem chord_eq_divided' {Φ : ℂ → (Fin r → ℂ)} {zb : ℂ} {S : Set ℂ}
    {Ψb : ℂ → (Fin r × Fin r → ℂ)}
    (hΨ : ∀ z ∈ S, ∀ q : Fin r × Fin r, Φ zb q.1 * Φ z q.2 - Φ zb q.2 * Φ z q.1 = (z - zb) * Ψb z q)
    (p : Fin r) {x : Fin r → ℂ} (hxw : Φ zb = (Φ zb p) • x) (hwp : Φ zb p ≠ 0)
    (b : Fin r → ℂ) {z : ℂ} (hz : z ∈ S) :
    ∑ j, b j * chord Φ x p z j = (z - zb) * (Φ zb p)⁻¹ * ∑ j, b j * Ψb z (p, j) := by
  have hx : ∀ i, x i = (Φ zb p)⁻¹ * Φ zb i := fun i => by
    have := congrFun hxw i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    field_simp
    rw [this]; ring
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [chord]
  have hΨi := hΨ z hz (p, i)
  simp only at hΨi
  rw [hx i]
  have h1 : (z - zb) * (Φ zb p)⁻¹ * (b i * Ψb z (p, i)) = (Φ zb p)⁻¹ * b i * ((z - zb) * Ψb z (p, i)) := by ring
  rw [h1, ← hΨi]
  field_simp

theorem diag_floor {Φ : ℂ → (Fin r → ℂ)} {c : ℂ} {ρ C L : ℝ} (hL : 0 ≤ L)
    {Ψ : ℂ → ℂ → (Fin r × Fin r → ℂ)}
    (hId : ∀ w ∈ ball c ρ, ∀ z ∈ ball c ρ, ∀ q : Fin r × Fin r,
      Φ w q.1 * Φ z q.2 - Φ w q.2 * Φ z q.1 = (z - w) * Ψ w z q)
    (hLip : ∀ w ∈ ball c ρ, ∀ z ∈ ball c ρ, ∀ z' ∈ ball c ρ, ‖Ψ w z - Ψ w z'‖ ≤ L * ‖z - z'‖)
    (hIM2 : ∀ z ∈ ball c ρ, ∀ w ∈ ball c ρ,
      C * ‖z - w‖ ≤ ⨆ q : Fin r × Fin r, ‖Φ z q.1 * Φ w q.2 - Φ z q.2 * Φ w q.1‖)
    {w : ℂ} (hw : w ∈ ball c ρ) : C ≤ ‖Ψ w w‖ := by

  by_contra hlt
  rw [not_le] at hlt

  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_ball w hw
  set δ : ℝ := min (ε / 2) ((C - ‖Ψ w w‖) / (2 * (L + 1))) with hδ
  have hgap : 0 < C - ‖Ψ w w‖ := by linarith
  have hδpos : 0 < δ := by positivity
  set z : ℂ := w + δ with hz
  have hzw : z - w = δ := by rw [hz]; ring
  have hnorm : ‖z - w‖ = δ := by rw [hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
  have hzb : z ∈ ball c ρ := hball (by rw [mem_ball, dist_eq_norm, hnorm]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hne : z ≠ w := by intro h; rw [h, sub_self, norm_zero] at hnorm; linarith
  have h1 : C * ‖z - w‖ ≤ ‖z - w‖ * ‖Ψ w z‖ := by
    refine (hIM2 z hzb w hw).trans ?_
    haveI : Nonempty (Fin r × Fin r) := by
      by_contra hn
      rw [not_nonempty_iff] at hn
      have := hIM2 z hzb w hw
      rw [Real.iSup_of_isEmpty] at this
      have : 0 < C * ‖z - w‖ := by rw [hnorm]; exact mul_pos (by linarith [norm_nonneg (Ψ w w)]) hδpos
      linarith
    refine ciSup_le fun q => ?_
    have hq := hId w hw z hzb (q.2, q.1)
    simp only at hq
    have : Φ z q.1 * Φ w q.2 - Φ z q.2 * Φ w q.1 = (z - w) * Ψ w z (q.2, q.1) := by rw [← hq]; ring
    rw [this, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (Ψ w z) (q.2, q.1)) (norm_nonneg _)
  have h2 : C ≤ ‖Ψ w z‖ := by
    have hpos : 0 < ‖z - w‖ := by rw [hnorm]; exact hδpos
    have h1' : C * ‖z - w‖ ≤ ‖Ψ w z‖ * ‖z - w‖ := by rwa [mul_comm ‖z - w‖] at h1
    exact le_of_mul_le_mul_right h1' hpos
  have h3 : ‖Ψ w z‖ ≤ ‖Ψ w w‖ + L * ‖z - w‖ := by
    have := hLip w hw z hzb w hw
    linarith [norm_le_insert' (Ψ w z) (Ψ w w), norm_sub_rev (Ψ w z) (Ψ w w)]
  have h4 : L * ‖z - w‖ ≤ (C - ‖Ψ w w‖) / 2 := by
    rw [hnorm]
    have hδle : δ ≤ (C - ‖Ψ w w‖) / (2 * (L + 1)) := min_le_right _ _
    have : L * δ ≤ (L + 1) * δ := by nlinarith
    refine this.trans ?_
    rw [le_div_iff₀ (by positivity)] at hδle
    linarith
  linarith

theorem row_floor {Φw : Fin r → ℂ} {M : Fin r × Fin r → ℂ} {D : Fin r → ℂ}
    (hM : ∀ q : Fin r × Fin r, M q = Φw q.1 * D q.2 - Φw q.2 * D q.1)
    (p : Fin r) (hp : ‖Φw p‖ = ‖Φw‖) (hΦ : Φw ≠ 0) :
    ‖M‖ ≤ 2 * ‖fun i => M (p, i)‖ := by
  have hΦp : 0 < ‖Φw p‖ := by rw [hp]; exact norm_pos_iff.2 hΦ
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun q => ?_

  have hid : Φw p * M q = Φw q.1 * M (p, q.2) - Φw q.2 * M (p, q.1) := by
    rw [hM q, hM (p, q.2), hM (p, q.1)]; ring
  have h1 : ‖Φw p‖ * ‖M q‖ ≤ ‖Φw‖ * ‖fun i => M (p, i)‖ + ‖Φw‖ * ‖fun i => M (p, i)‖ := by
    rw [← norm_mul, hid]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm _ _) (norm_le_pi_norm (fun i => M (p, i)) q.2) (norm_nonneg _) (norm_nonneg _)
    · rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm _ _) (norm_le_pi_norm (fun i => M (p, i)) q.1) (norm_nonneg _) (norm_nonneg _)
  rw [hp] at h1 hΦp
  nlinarith

theorem near_package {Φ : ℂ → (Fin r → ℂ)} {U : Set ℂ} (hU : IsOpen U)
    (hA : ∀ i, DifferentiableOn ℂ (fun z => Φ z i) U)
    {Kb : Set ℂ} (hKb : IsCompact Kb) (hKbU : Kb ⊆ U) (hZ : ∀ w ∈ Kb, Φ w ≠ 0)
    (himm : ∀ w ∈ Kb, ∃ q : Fin r × Fin r,
      Φ w q.1 * deriv (fun z => Φ z q.2) w - Φ w q.2 * deriv (fun z => Φ z q.1) w ≠ 0) :
    ∃ ρ₁ L m₀ : ℝ, 0 < ρ₁ ∧ 0 ≤ L ∧ 0 < m₀ ∧ ∀ w ∈ Kb, closedBall w ρ₁ ⊆ U ∧
      ∃ Ψw : ℂ → (Fin r × Fin r → ℂ),
        (∀ z ∈ closedBall w ρ₁, ∀ q : Fin r × Fin r, Φ w q.1 * Φ z q.2 - Φ w q.2 * Φ z q.1 = (z - w) * Ψw z q) ∧
        (∀ z ∈ closedBall w ρ₁, ∀ z' ∈ closedBall w ρ₁, ‖Ψw z - Ψw z'‖ ≤ L * ‖z - z'‖) ∧
        (∀ p : Fin r, ‖Φ w p‖ = ‖Φ w‖ → m₀ ≤ ‖fun i => Ψw w (p, i)‖) := by
  classical

  have key : ∀ c ∈ Kb, ∃ (ρc Lc Cc : ℝ) (Ψc : ℂ → ℂ → (Fin r × Fin r → ℂ)), 0 < ρc ∧ 0 ≤ Lc ∧ 0 < Cc ∧
      ball c ρc ⊆ U ∧
      (∀ w ∈ ball c ρc, ∀ z ∈ ball c ρc, ∀ q : Fin r × Fin r,
        Φ w q.1 * Φ z q.2 - Φ w q.2 * Φ z q.1 = (z - w) * Ψc w z q) ∧
      (∀ w ∈ ball c ρc, ∀ q : Fin r × Fin r,
        Ψc w w q = Φ w q.1 * deriv (fun z => Φ z q.2) w - Φ w q.2 * deriv (fun z => Φ z q.1) w) ∧
      (∀ w ∈ ball c ρc, ∀ z ∈ ball c ρc, ∀ z' ∈ ball c ρc, ‖Ψc w z - Ψc w z'‖ ≤ Lc * ‖z - z'‖) ∧
      (∀ z ∈ ball c ρc, ∀ w ∈ ball c ρc,
        Cc * ‖z - w‖ ≤ ⨆ q : Fin r × Fin r, ‖Φ z q.1 * Φ w q.2 - Φ z q.2 * Φ w q.1‖) := by
    intro c hc
    obtain ⟨Rc, hRc, hRcU⟩ := Metric.isOpen_iff.1 hU c (hKbU hc)
    have hφ : ∀ i, DifferentiableOn ℂ (fun z => Φ z i) (ball c Rc) := fun i => (hA i).mono hRcU
    obtain ⟨ρ₄, hρ₄, L₄, hL₄, Ψ, hId, hDiag, hLip⟩ := Complex.exists_lipschitzWith_divided_minor hRc hφ
    obtain ⟨ρ₂, hρ₂, C₂, hC₂, hIM2⟩ :=
      Complex.exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero hRc hφ (himm c hc)
    refine ⟨min (min ρ₄ ρ₂) Rc, L₄, C₂, Ψ, by positivity, hL₄, hC₂, ?_, ?_, ?_, ?_, ?_⟩
    · exact (ball_subset_ball (min_le_right _ _)).trans hRcU
    · intro w hw z hz q
      exact hId w (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hw)
        z (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hz) q
    · intro w hw q
      exact hDiag w (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hw) q
    · intro w hw z hz z' hz'
      have hs : ball c (min (min ρ₄ ρ₂) Rc) ⊆ ball c ρ₄ := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
      exact hLip w (hs hw) z (hs hz) z' (hs hz')
    · intro z hz w hw
      have hs : ball c (min (min ρ₄ ρ₂) Rc) ⊆ ball c ρ₂ := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
      exact hIM2 z (hs hz) w (hs hw)
  choose! ρc Lc Cc Ψc hρc hLc hCc hsubU hId hDiag hLip hIM2 using key

  obtain ⟨F, hFK, hcov⟩ := hKb.elim_nhds_subcover (fun c => ball c (ρc c / 2))
    (fun c hc => ball_mem_nhds c (by linarith [hρc c hc]))
  rcases F.eq_empty_or_nonempty with hF | hF
  ·
    refine ⟨1, 0, 1, one_pos, le_rfl, one_pos, fun w hw => ?_⟩
    have := hcov hw
    rw [hF] at this
    simp at this
  set ρ₁ : ℝ := F.inf' hF ρc / 4 with hρ₁
  set L : ℝ := F.sup' hF Lc with hLdef
  set m₀ : ℝ := F.inf' hF Cc / 2 with hm₀
  have hρ₁pos : 0 < ρ₁ := by
    rw [hρ₁]; exact div_pos ((Finset.lt_inf'_iff _).2 fun c hc => hρc c (hFK c hc)) four_pos
  have hLnn : 0 ≤ L := by
    obtain ⟨c₀, hc₀⟩ := hF
    exact (hLc c₀ (hFK c₀ hc₀)).trans (Finset.le_sup' Lc hc₀)
  have hm₀pos : 0 < m₀ := by
    rw [hm₀]; exact div_pos ((Finset.lt_inf'_iff _).2 fun c hc => hCc c (hFK c hc)) two_pos
  refine ⟨ρ₁, L, m₀, hρ₁pos, hLnn, hm₀pos, fun w hw => ?_⟩
  obtain ⟨c, hcF, hwc⟩ := Set.mem_iUnion₂.mp (hcov hw)
  have hcK : c ∈ Kb := hFK c hcF
  have hρ₁c : ρ₁ ≤ ρc c / 4 := by
    rw [hρ₁]; exact div_le_div_of_nonneg_right (Finset.inf'_le ρc hcF) (by norm_num)
  have hsub : closedBall w ρ₁ ⊆ ball c (ρc c) := by
    intro z hz
    rw [mem_closedBall] at hz; rw [mem_ball] at hwc ⊢
    linarith [dist_triangle z w c, hρc c hcK]
  have hwb : w ∈ ball c (ρc c) := hsub (mem_closedBall_self hρ₁pos.le)
  refine ⟨hsub.trans (hsubU c hcK), Ψc c w, fun z hz q => hId c hcK w hwb z (hsub hz) q,
    fun z hz z' hz' => ?_, fun p hp => ?_⟩
  · refine (hLip c hcK w hwb z (hsub hz) z' (hsub hz')).trans ?_
    exact mul_le_mul_of_nonneg_right (Finset.le_sup' Lc hcF) (norm_nonneg _)
  ·
    have hdiag : Cc c ≤ ‖Ψc c w w‖ :=
      diag_floor (hLc c hcK) (hId c hcK) (hLip c hcK) (hIM2 c hcK) hwb
    have hrow := row_floor (Φw := Φ w) (M := Ψc c w w) (D := fun j => deriv (fun z => Φ z j) w)
      (fun q => hDiag c hcK w hwb q) p hp (hZ w hw)
    have hm : m₀ ≤ Cc c / 2 := by
      rw [hm₀]; exact div_le_div_of_nonneg_right (Finset.inf'_le Cc hcF) (by norm_num)
    linarith

theorem near_piece' {zb : ℂ} {ρ₁ L m₀ : ℝ} (hρ₁ : 0 < ρ₁) (hL : 0 ≤ L) (hm₀ : 0 < m₀)
    {Ψb : ℂ → (Fin r × Fin r → ℂ)}
    (hLip : ∀ z ∈ closedBall zb ρ₁, ∀ z' ∈ closedBall zb ρ₁, ‖Ψb z - Ψb z'‖ ≤ L * ‖z - z'‖)
    (p : Fin r) (hfloor : m₀ ≤ ‖fun i => Ψb zb (p, i)‖) :
    volume {b : Fin r → ℂ | b ∈ ball 0 1 ∧ ∃ z ∈ closedBall zb ρ₁, ∑ j, b j * Ψb z (p, j) = 0}
      ≤ ENNReal.ofReal ((r * (L * ρ₁) / m₀) ^ 2) * volume (ball (0 : Fin r → ℂ) 1) := by
  have h0 : (fun i => Ψb zb (p, i)) ≠ 0 := by
    intro h; rw [h, norm_zero] at hfloor; linarith
  have h := Complex.volume_ball_inter_exists_sum_mul_eq_zero_le (fun z i => Ψb z (p, i)) zb (closedBall zb ρ₁) h0
    (δ := L * ρ₁) (fun z hz => ?_)
  · refine h.trans ?_
    gcongr ?_ * _
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_pow, div_pow]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact pow_le_pow_left₀ hm₀.le hfloor 2
  · have h1 : ‖Ψb z - Ψb zb‖ ≤ L * ‖z - zb‖ := hLip z hz zb (mem_closedBall_self hρ₁.le)
    refine le_trans ?_ (h1.trans ?_)
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      exact norm_le_pi_norm (Ψb z - Ψb zb) (p, i)
    · rw [← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left (mem_closedBall.1 hz) hL

def wedge (y x : Fin r → ℂ) : Fin r × Fin r → ℂ := fun q => y q.1 * x q.2 - y q.2 * x q.1

def pchd (y x : Fin r → ℂ) : ℝ := ‖wedge y x‖ / (‖y‖ * ‖x‖)

theorem wedge_sub_smul (y x : Fin r → ℂ) (t : ℂ) : wedge (fun i => y i - t * x i) x = wedge y x := by
  funext q; simp only [wedge]; ring

theorem norm_wedge_le (y x : Fin r → ℂ) : ‖wedge y x‖ ≤ 2 * ‖y‖ * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun q => ?_
  simp only [wedge]
  calc ‖y q.1 * x q.2 - y q.2 * x q.1‖ ≤ ‖y q.1 * x q.2‖ + ‖y q.2 * x q.1‖ := norm_sub_le _ _
    _ ≤ ‖y‖ * ‖x‖ + ‖y‖ * ‖x‖ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul (norm_le_pi_norm y _) (norm_le_pi_norm x _) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul (norm_le_pi_norm y _) (norm_le_pi_norm x _) (norm_nonneg _) (norm_nonneg _))
    _ = 2 * ‖y‖ * ‖x‖ := by ring

theorem pchd_nonneg (y x : Fin r → ℂ) : 0 ≤ pchd y x := by unfold pchd; positivity

theorem pchd_mul_norm_le (y x : Fin r → ℂ) (p : Fin r) (hxp : x p = 1) (hx1 : ‖x‖ = 1) :
    pchd y x * ‖y‖ ≤ 2 * ‖fun i => y i - y p * x i‖ := by
  unfold pchd
  rw [hx1, mul_one]
  rcases eq_or_ne ‖y‖ 0 with h | h
  · rw [h, mul_zero]; positivity
  · rw [div_mul_cancel₀ _ h, ← wedge_sub_smul y x (y p)]
    have := norm_wedge_le (fun i => y i - y p * x i) x
    rw [hx1, mul_one] at this
    exact this

theorem wedge_smul_left (t : ℂ) (y x : Fin r → ℂ) : wedge (t • y) x = t • wedge y x := by
  funext q; simp only [wedge, Pi.smul_apply, smul_eq_mul]; ring

theorem pchd_smul_left {t : ℂ} (ht : t ≠ 0) (y x : Fin r → ℂ) : pchd (t • y) x = pchd y x := by
  unfold pchd
  rw [wedge_smul_left, norm_smul, norm_smul, mul_assoc, mul_div_mul_left _ _ (norm_ne_zero_iff.2 ht)]

theorem continuousOn_pchd_left {X : Type*} [TopologicalSpace X] {F : X → (Fin r → ℂ)} {S : Set X}
    (hF : ContinuousOn F S) (hF0 : ∀ z ∈ S, F z ≠ 0) {x : Fin r → ℂ} (hx : x ≠ 0) :
    ContinuousOn (fun z => pchd (F z) x) S := by
  unfold pchd
  refine ContinuousOn.div ?_ (hF.norm.mul continuousOn_const) fun z hz => ?_
  · refine ContinuousOn.norm ?_
    refine continuousOn_pi.2 fun q => ?_
    simp only [wedge]
    exact ((continuousOn_pi.1 hF q.1).mul continuousOn_const).sub ((continuousOn_pi.1 hF q.2).mul continuousOn_const)
  · exact mul_ne_zero (norm_ne_zero_iff.2 (hF0 z hz)) (norm_ne_zero_iff.2 hx)

theorem random_core {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (ρ ρ' R : ι → ℝ) (Φ : ι → ℂ → (Fin r → ℂ))
    (hρ : ∀ j, 0 < ρ j) (hρρ' : ∀ j, ρ j < ρ' j) (hρ'R : ∀ j, ρ' j < R j)
    (hA : ∀ j i, AnalyticOnNhd ℂ (fun z => Φ j z i) (ball (c j) (R j)))
    (hLip : ∀ j i, ∃ Lji, LipschitzOnWith Lji (fun z => Φ j z i) (closedBall (c j) (ρ' j)))
    (hZ : ∀ j, ∀ z ∈ ball (c j) (R j), Φ j z ≠ 0)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ β : ℝ, 0 < β ∧
    ∀ {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (σ : F →+* ℂ)

      (Φb : ℂ → (Fin r → ℂ)) (zb : ℂ) (ρ₁ L m₀ : ℝ) (Ψb : ℂ → (Fin r × Fin r → ℂ)) (p : Fin r),
      0 < ρ₁ → 0 ≤ L → 0 < m₀ →
      (∀ z ∈ closedBall zb ρ₁, ∀ q : Fin r × Fin r,
        Φb zb q.1 * Φb z q.2 - Φb zb q.2 * Φb z q.1 = (z - zb) * Ψb z q) →
      (∀ z ∈ closedBall zb ρ₁, ∀ z' ∈ closedBall zb ρ₁, ‖Ψb z - Ψb z'‖ ≤ L * ‖z - z'‖) →
      ‖Φb zb p‖ = ‖Φb zb‖ → Φb zb ≠ 0 → m₀ ≤ ‖fun i => Ψb zb (p, i)‖ →
      (r * (L * ρ₁) / m₀) ^ 2 ≤ 1 / 8 →

      ∀ (K : ι → Set ℂ) (Vn : Finset (Fin r → ℂ)),
      (∀ j, IsClosed (K j)) → (∀ j, K j ⊆ closedBall (c j) (ρ j)) →
      (∀ j, ∀ z ∈ K j, eta ≤ pchd (Φ j z) ((Φb zb p)⁻¹ • Φb zb)) →
      (∀ j, volume (K j) ≤ ENNReal.ofReal β) →
      (∀ v ∈ Vn, v ≠ 0) →
      ∃ e : Fin r → F,
        (fun i => σ (e i)) ∈ ball (0 : Fin r → ℂ) 1 ∧
        (∀ v ∈ Vn, ∑ i, v i * σ (e i) ≠ 0) ∧
        (∀ z ∈ closedBall zb ρ₁, ∑ i, σ (e i) * Ψb z (p, i) ≠ 0) ∧
        (∀ j, ∀ z ∈ K j, ∑ i, σ (e i) * chord (Φ j) ((Φb zb p)⁻¹ • Φb zb) p z i ≠ 0) := by
  classical

  have hLipj : ∀ j, ∃ Lj : NNReal, ∀ i, LipschitzOnWith Lj (fun z => Φ j z i) (closedBall (c j) (ρ' j)) := by
    intro j
    choose Li hLi using fun i => hLip j i
    refine ⟨∑ i, Li i, fun i => (hLi i).weaken ?_⟩
    exact_mod_cast Finset.single_le_sum (fun k _ => (bot_le : (0 : NNReal) ≤ Li k)) (Finset.mem_univ i)
  choose Lj hLj using hLipj
  have hfloorj : ∀ j, ∃ mj : ℝ, 0 < mj ∧ ∀ z ∈ closedBall (c j) (ρ j), mj ≤ ‖Φ j z‖ := by
    intro j
    have hsub : closedBall (c j) (ρ j) ⊆ ball (c j) (R j) := closedBall_subset_ball ((hρρ' j).trans (hρ'R j))
    have hcont : ContinuousOn (Φ j) (closedBall (c j) (ρ j)) :=
      continuousOn_pi.2 fun i => (hA j i).continuousOn.mono hsub
    obtain ⟨zm, hzm, hmin⟩ := (isCompact_closedBall (c j) (ρ j)).exists_isMinOn
      (nonempty_closedBall.2 (hρ j).le) hcont.norm
    exact ⟨‖Φ j zm‖, norm_pos_iff.2 (hZ j zm (hsub hzm)), fun z hz => hmin hz⟩
  choose mj hmj hmjle using hfloorj

  set FC : ι → ℝ := fun j => (r * (2 * (r * (Lj j : ℝ))) / (eta * mj j / 2)) ^ 2 / Real.pi with hFC
  have hFC0 : ∀ j, 0 ≤ FC j := fun j => by positivity
  set β : ℝ := (8 * (∑ j, FC j + 1))⁻¹ with hβ
  have hβpos : 0 < β := by positivity
  refine ⟨β, hβpos, ?_⟩
  intro F _ _ _ σ Φb zb ρ₁ L m₀ Ψb p hρ₁ hL hm₀ hId hLipb hp hb0 hfloor hnear K Vn hKc hKsub hKeta hvol hVn
  set xh : Fin r → ℂ := (Φb zb p)⁻¹ • Φb zb with hxh
  have hbp : Φb zb p ≠ 0 := by
    intro h; rw [h, norm_zero] at hp; exact hb0 (norm_eq_zero.1 hp.symm)
  have hxhp : xh p = 1 := by simp [xh, inv_mul_cancel₀ hbp]
  have hxh1 : ‖xh‖ = 1 := by
    rw [hxh, norm_smul, norm_inv, hp, inv_mul_cancel₀ (norm_ne_zero_iff.2 hb0)]
  have hxhle : ‖xh‖ ≤ 1 := hxh1.le

  set Vb := volume (ball (0 : Fin r → ℂ) 1) with hVb
  have hVtop : Vb ≠ ⊤ := measure_ball_lt_top.ne
  have hVpos : Vb ≠ 0 := (measure_ball_pos volume (0 : Fin r → ℂ) one_pos).ne'
  set X : ℝ≥0∞ := ENNReal.ofReal (1/8) * Vb with hX

  set BadF : ι → Set (Fin r → ℂ) := fun j =>
    {b : Fin r → ℂ | ∃ z ∈ K j, ∑ i, b i * chord (Φ j) xh p z i = 0} with hBadF
  set BadN : Set (Fin r → ℂ) := {b : Fin r → ℂ | ∃ z ∈ closedBall zb ρ₁, ∑ i, b i * Ψb z (p, i) = 0} with hBadN
  set Gd : Set (Fin r → ℂ) := {b | ∀ v ∈ Vn, ∑ i, v i * b i ≠ 0} ∩ (BadNᶜ ∩ ⋂ j, (BadF j)ᶜ) with hGd

  have hKcpt : ∀ j, IsCompact (K j) := fun j => (isCompact_closedBall _ _).of_isClosed_subset (hKc j) (hKsub j)
  have hcontC : ∀ j, ContinuousOn (chord (Φ j) xh p) (K j) := by
    intro j
    have hsub : K j ⊆ ball (c j) (R j) := (hKsub j).trans (closedBall_subset_ball ((hρρ' j).trans (hρ'R j)))
    have hc : ContinuousOn (Φ j) (K j) := continuousOn_pi.2 fun i => (hA j i).continuousOn.mono hsub
    refine continuousOn_pi.2 fun i => ?_
    simp only [chord]
    exact ((continuousOn_pi.1 hc i).sub ((continuousOn_pi.1 hc p).mul continuousOn_const))
  have hcontΨ : ContinuousOn Ψb (closedBall zb ρ₁) := by
    refine Metric.continuousOn_iff.2 fun z hz ε hε => ⟨ε / (L + 1), by positivity, fun z' hz' hd => ?_⟩
    rw [dist_eq_norm] at hd ⊢
    have h := hLipb z' hz' z hz
    have h2 : L * ‖z' - z‖ ≤ (L + 1) * ‖z' - z‖ := by nlinarith [norm_nonneg (z' - z)]
    have h3 : (L + 1) * ‖z' - z‖ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left hd (by linarith)
    rw [mul_div_cancel₀ _ (by linarith : L + 1 ≠ 0)] at h3
    linarith
  have hGopen : IsOpen Gd := by
    refine IsOpen.inter ?_ ((isClosed_near_bad hcontΨ p).isOpen_compl.inter ?_)
    · have : {b : Fin r → ℂ | ∀ v ∈ Vn, ∑ i, v i * b i ≠ 0} = ⋂ v ∈ Vn, {b | ∑ i, v i * b i = 0}ᶜ := by
        ext b; simp
      rw [this]
      refine isOpen_biInter_finset fun v _ => (isClosed_eq ?_ continuous_const).isOpen_compl
      exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
    · exact isOpen_iInter_of_finite fun j => (isClosed_far_bad (hKcpt j) (hcontC j)).isOpen_compl

  have hFar : ∀ j, volume {b : Fin r → ℂ | b ∈ ball 0 1 ∧ b ∈ BadF j} ≤ ENNReal.ofReal (FC j) * Vb * ENNReal.ofReal β := by
    intro j
    have hetaK : ∀ z ∈ K j, eta * mj j / 2 ≤ ‖chord (Φ j) xh p z‖ := by
      intro z hz
      have h1 := pchd_mul_norm_le (Φ j z) xh p hxhp hxh1
      have h2 : eta * mj j ≤ pchd (Φ j z) xh * ‖Φ j z‖ :=
        mul_le_mul (hKeta j z hz) (hmjle j z (hKsub j hz)) (hmj j).le (pchd_nonneg _ _)
      have : (fun i => Φ j z i - Φ j z p * xh i) = chord (Φ j) xh p z := rfl
      rw [this] at h1
      linarith
    have h := far_piece (Φ := Φ j) hxhle p (hρρ' j) (hLj j) (K j) (hKsub j) (by have := hmj j; positivity) hetaK
    refine (le_of_eq_of_le (by rfl) h).trans ?_
    gcongr
    exact hvol j
  have hNear : volume {b : Fin r → ℂ | b ∈ ball 0 1 ∧ b ∈ BadN} ≤ X := by
    refine (near_piece' hρ₁ hL hm₀ hLipb p hfloor).trans ?_
    rw [hX]
    gcongr
  have hNull : volume (⋃ v ∈ Vn, {b : Fin r → ℂ | b ∈ ball 0 1 ∧ ∑ i, v i * b i = 0}) = 0 :=
    (measure_biUnion_null_iff Vn.countable_toSet).2 fun v hv => volume_ball_inter_hyperplane v (hVn v hv)

  have hsub : ball (0 : Fin r → ℂ) 1 ∩ Gdᶜ ⊆
      (⋃ v ∈ Vn, {b : Fin r → ℂ | b ∈ ball 0 1 ∧ ∑ i, v i * b i = 0}) ∪
      ({b : Fin r → ℂ | b ∈ ball 0 1 ∧ b ∈ BadN} ∪ ⋃ j, {b : Fin r → ℂ | b ∈ ball 0 1 ∧ b ∈ BadF j}) := by
    rintro b ⟨hb, hbG⟩
    by_cases h1 : ∃ v ∈ Vn, ∑ i, v i * b i = 0
    · obtain ⟨v, hv, h0⟩ := h1
      exact Or.inl (Set.mem_iUnion₂.2 ⟨v, hv, hb, h0⟩)
    by_cases h2 : b ∈ BadN
    · exact Or.inr (Or.inl ⟨hb, h2⟩)
    by_cases h3 : ∃ j, b ∈ BadF j
    · obtain ⟨j, hj⟩ := h3
      exact Or.inr (Or.inr (Set.mem_iUnion.2 ⟨j, hb, hj⟩))
    exfalso
    apply hbG
    exact ⟨fun v hv h0 => h1 ⟨v, hv, h0⟩, h2, Set.mem_iInter.2 fun j hj => h3 ⟨j, hj⟩⟩
  have hFarSum : volume (⋃ j, {b : Fin r → ℂ | b ∈ ball 0 1 ∧ b ∈ BadF j}) ≤ X := by
    calc volume (⋃ j, {b : Fin r → ℂ | b ∈ ball 0 1 ∧ b ∈ BadF j})
        ≤ ∑ j, volume {b : Fin r → ℂ | b ∈ ball 0 1 ∧ b ∈ BadF j} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ j, ENNReal.ofReal (FC j) * Vb * ENNReal.ofReal β := Finset.sum_le_sum fun j _ => hFar j
      _ = ENNReal.ofReal ((∑ j, FC j) * β) * Vb := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hFC0 j),
            mul_comm _ Vb, mul_assoc, ← ENNReal.ofReal_mul (Finset.sum_nonneg fun j _ => hFC0 j), mul_comm]
      _ ≤ X := by
          rw [hX]
          gcongr
          rw [hβ, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
          nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hFC0 j)]
  have hGvol : volume (ball (0 : Fin r → ℂ) 1 ∩ Gdᶜ) < Vb := by
    calc volume (ball (0 : Fin r → ℂ) 1 ∩ Gdᶜ)
        ≤ volume (⋃ v ∈ Vn, {b : Fin r → ℂ | b ∈ ball 0 1 ∧ ∑ i, v i * b i = 0}) +
          (volume {b : Fin r → ℂ | b ∈ ball 0 1 ∧ b ∈ BadN} + volume (⋃ j, {b : Fin r → ℂ | b ∈ ball 0 1 ∧ b ∈ BadF j})) :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _)))
      _ ≤ 0 + (X + X) := add_le_add hNull.le (add_le_add hNear hFarSum)
      _ = ENNReal.ofReal (1/4) * Vb := by
          rw [zero_add, hX, ← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
      _ < Vb := by
          have h34 : ENNReal.ofReal (3/4) * Vb ≠ 0 :=
            mul_ne_zero (ENNReal.ofReal_pos.2 (by norm_num : (0:ℝ) < 3/4)).ne' hVpos
          have hq : ENNReal.ofReal (1/4) * Vb ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop
          have h := ENNReal.lt_add_right hq h34
          have heq : ENNReal.ofReal (1/4) * Vb + ENNReal.ofReal (3/4) * Vb = Vb := by
            rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
            norm_num
          rwa [heq] at h

  obtain ⟨e, heG⟩ := exists_algebraic_mem σ hGopen hGvol
  obtain ⟨hb_ball, hb_null, hb_near, hb_far⟩ := heG
  refine ⟨e, hb_ball, fun v hv => hb_null v hv, fun z hz h0 => hb_near ⟨z, hz, h0⟩, fun j z hz h0 => ?_⟩
  exact (Set.mem_iInter.1 hb_far j) ⟨z, hz, h0⟩

end Engine
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

private theorem _root_.PLBG.isRational (N : ℕ) [NeZero N] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : w.IsRational :=
  (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField w).1
    (ModularCurve.deg_eq_one_modularFunctionFieldBar N w)

p2m_export "PLBG" "isRational"
private theorem _root_.PLBG.evalAt_add' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

p2m_export "PLBG" "evalAt_add'"
private theorem _root_.PLBG.evalAt_zero' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.evalAt (0 : F) = 0 := by
  simpa using v.evalAt_algebraMap (0 : K)

p2m_export "PLBG" "evalAt_zero'"

theorem evalAt_sum_smul {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    {ι : Type*} (t : Finset ι) (a : ι → K) (g : ι → F) (hg : ∀ i ∈ t, g i ∈ v.toValuationSubring) :
    (∑ i ∈ t, a i • g i) ∈ v.toValuationSubring ∧
    v.evalAt (∑ i ∈ t, a i • g i) = ∑ i ∈ t, a i * v.evalAt (g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨by simp, by simp [evalAt_zero']⟩
  | insert j t hj ih =>
    obtain ⟨hmem, hval⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hgj : g j ∈ v.toValuationSubring := hg j (Finset.mem_insert_self _ _)
    have hsm : a j • g j ∈ v.toValuationSubring := by
      rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' _) hgj
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    refine ⟨add_mem hsm hmem, ?_⟩
    rw [evalAt_add' v hv hsm hmem, hval, Algebra.smul_def, v.evalAt_mul hv (v.algebraMap_mem' _) hgj,
      v.evalAt_algebraMap]

private theorem _root_.PLBG.neg_le_ord_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) {f : F}
    (hf : f ∈ riemannRochSpace D) (hf0 : f ≠ 0) (w : Place K F) : -D w ≤ w.ord f := by
  have hval : w.adicValuation f ≤ WithZero.exp (D w) := hf w
  have hlog := (WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hf0)).2 hval
  simp only [AlgebraicCurve.Place.ord]
  linarith

p2m_export "PLBG" "neg_le_ord_of_mem"
private theorem _root_.PLBG.r_pos (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    0 < r := by
  rcases Nat.eq_zero_or_pos r with h0 | h
  · exfalso
    subst h0
    have h1 : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (embDivisor N) := by
      rw [mem_riemannRochSpace_iff]
      intro w
      right
      rw [w.ord_one, neg_nonpos]
      classical
      simp only [embDivisor, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs <;> simp
    rw [← hs.2] at h1
    have : Set.range s = ∅ := Set.range_eq_empty s
    rw [this, Submodule.span_empty, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · exact h

p2m_export "PLBG" "r_pos"
theorem s_ne_zero (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (i : Fin r) : s i ≠ 0 := hs.1.ne_zero i

private theorem _root_.PLBG.s_mem (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (i : Fin r) : s i ∈ riemannRochSpace (embDivisor N) := by
  rw [← hs.2]; exact Submodule.subset_span ⟨i, rfl⟩

p2m_export "PLBG" "s_mem"

private theorem _root_.PLBG.ord_pivot (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hr : 0 < r) : w.ord (s (pivotIndex s w hr)) = -embDivisor N w := by
  classical
  have hex : ∃ i : Fin r, ∀ j : Fin r, w.ord (s i) ≤ w.ord (s j) := by
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact Finite.exists_min fun i => w.ord (s i)
  have hpiv : ∀ j, w.ord (s (pivotIndex s w hr)) ≤ w.ord (s j) := by
    unfold pivotIndex
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  obtain ⟨i₀, hi₀⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs w
  refine le_antisymm (by linarith [hpiv i₀]) ?_
  exact neg_le_ord_of_mem _ (s_mem N s hs _) (s_ne_zero N s hs _) w

p2m_export "PLBG" "ord_pivot"

private theorem _root_.PLBG.ratio_mem (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hr : 0 < r) (i : Fin r) :
    s i * (s (pivotIndex s w hr))⁻¹ ∈ w.toValuationSubring ∧
    0 ≤ w.ord (s i * (s (pivotIndex s w hr))⁻¹) ∧
    w.evalAt (s i * (s (pivotIndex s w hr))⁻¹) = evalVec s w i := by
  have hne : s i * (s (pivotIndex s w hr))⁻¹ ≠ 0 :=
    mul_ne_zero (s_ne_zero N s hs i) (inv_ne_zero (s_ne_zero N s hs _))
  have hord : 0 ≤ w.ord (s i * (s (pivotIndex s w hr))⁻¹) := by
    rw [w.ord_mul (s_ne_zero N s hs i) (inv_ne_zero (s_ne_zero N s hs _)), w.ord_inv, ord_pivot N s hs w hr]
    have := neg_le_ord_of_mem _ (s_mem N s hs i) (s_ne_zero N s hs i) w
    linarith
  refine ⟨w.mem_of_ord_nonneg hne hord, hord, ?_⟩
  simp only [evalVec, dif_pos hr]

p2m_export "PLBG" "ratio_mem"
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem _root_.PLBG.hypSec_facts (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (a : Fin r → AlgebraicClosure ℚ) (ha : linSec s a ≠ 0) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hZa : ∀ w, Za w = w.ord (linSec s a) + embDivisor N w) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    0 ≤ Za w ∧ (Za w = 0 ↔ ∑ i, evalVec s w i * a i ≠ 0) := by
  classical
  have hr := r_pos N s hs
  have hv := isRational N w
  obtain ⟨hGmem, hGval⟩ := evalAt_sum_smul w hv Finset.univ a
    (fun i => s i * (s (pivotIndex s w hr))⁻¹) (fun i _ => (ratio_mem N s hs w hr i).1)
  have hGval' : w.evalAt (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) = ∑ i, evalVec s w i * a i := by
    rw [hGval]
    exact Finset.sum_congr rfl fun i _ => by rw [(ratio_mem N s hs w hr i).2.2, mul_comm]
  have hfactor : linSec s a = (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) * s (pivotIndex s w hr) := by
    rw [Finset.sum_mul]
    unfold linSec
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, inv_mul_cancel_right₀ (s_ne_zero N s hs _)]
  have hG0 : (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) ≠ 0 := by
    intro h0; apply ha; rw [hfactor, h0, zero_mul]
  have hZaw : Za w = w.ord (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) := by
    rw [hZa w, hfactor, w.ord_mul hG0 (s_ne_zero N s hs _), ord_pivot N s hs w hr]; ring
  refine ⟨hZaw ▸ w.ord_nonneg_of_mem hGmem, ?_⟩
  rw [hZaw, ← hGval']
  constructor
  · intro h0; exact w.evalAt_ne_zero hv hG0 h0
  · intro hne
    by_contra hne0
    have hpos : 0 < w.ord (∑ i, a i • (s i * (s (pivotIndex s w hr))⁻¹)) :=
      lt_of_le_of_ne (w.ord_nonneg_of_mem hGmem) (Ne.symm hne0)
    apply hne
    rw [← evalAt_zero' w]
    exact w.evalAt_congr hGmem (zero_mem _) (Or.inr (by simpa using hpos))

p2m_export "PLBG" "hypSec_facts"

variable {N : ℕ} [NeZero N] {r : ℕ}

def Pinned (s : Fin r → modularFunctionFieldBar N) (c : Fin r → AlgebraicClosure ℚ)
    (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : Prop :=
  ∀ w, Z w = w.ord (linSec s c) + embDivisor N w

theorem linSec_ne_zero_of_ne_zero (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (e : Fin r → AlgebraicClosure ℚ) (he : e ≠ 0) : linSec s e ≠ 0 := fun h0 =>
  he (funext fun i => (Fintype.linearIndependent_iff.1 hs.1 _ h0) i)

theorem exists_pinned (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (e : Fin r → AlgebraicClosure ℚ) (he : linSec s e ≠ 0) :
    ∃ Ze : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), Pinned s e Ze := by
  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  obtain ⟨D, hD, -⟩ := hcurve.toHasPrincipalDivisors.exists_divisor _ he
  exact ⟨D + embDivisor N, fun w => by rw [Finsupp.add_apply, hD w]⟩

theorem pinned_eq_zero_iff (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    {c : Fin r → AlgebraicClosure ℚ} (hc : linSec s c ≠ 0)
    {Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hZ : Pinned s c Z)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Z w = 0 ↔ ∑ i, evalVec s w i * c i ≠ 0 :=
  (hypSec_facts N s hs c hc Z hZ w).2

theorem sigma_evalVec_ne_zero (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (σ : AlgebraicClosure ℚ →+* ℂ) (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (fun i => σ (evalVec s w i)) ≠ 0 := by
  intro h0
  have hr := r_pos N s hs
  have h1 := congrFun h0 (pivotIndex s w hr)
  rw [evalVec_pivotIndex s w hr (s_ne_zero N s hs _), map_one] at h1
  exact one_ne_zero h1

theorem finite_cusps : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) |
    jB N ∉ w.toValuationSubring}.Finite := by
  classical
  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N
  have hj0 : jB N ≠ 0 := fun h => jB_notMem (N := N) (h ▸ zero_mem _)
  obtain ⟨Dj, hDj, -⟩ := hcurve.toHasPrincipalDivisors.exists_divisor _ hj0
  refine (Dj.support.finite_toSet).subset fun w hw => ?_
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hDj w]
  intro h0
  exact hw ((w.mem_of_ord_nonneg hj0 (le_of_eq h0.symm)))

theorem place_proj' (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ)
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hj : jB N ∈ v.toValuationSubring) :
    ∃ τ : ℍ, v.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) ∧
      ∃ t : ℂ, t ≠ 0 ∧ (fun i => σ (evalVec s v i)) = t • Φint σ s (τ : ℂ) := by
  classical
  have hr := r_pos N s hs
  obtain ⟨τ, hord, hcomap⟩ := placePoint D σ v hj
  have hreg : ∀ i, phi N σ (s i) ∈ (D.pt τ).toValuationSubring := fun i => (interiorInputs D σ s hs).reg τ i
  have hval : ∀ i, Φint σ s (τ : ℂ) i = (D.pt τ).evalAt (phi N σ (s i)) := fun i => by
    rw [Φint_eq_ext]; exact (ext_analyticAt D (phi N σ (s i)) τ (hreg i)).2.2
  have hvinf : embDivisor N v = 0 := by
    by_contra hne
    have hv : v = cuspInftyBar N := by
      by_contra hv
      apply hne
      simp [embDivisor, Finsupp.single_apply, hv]
    subst hv
    exact jB_notMem (N := N) hj
  have hordp : v.ord (s (pivotIndex s v hr)) = 0 := by rw [ord_pivot N s hs v hr, hvinf, neg_zero]
  have hordp' : (D.pt τ).ord (phi N σ (s (pivotIndex s v hr))) = 0 := by rw [hord, hordp]
  have hsp0 : phi N σ (s (pivotIndex s v hr)) ≠ 0 := phi_ne_zero σ (s_ne_zero N s hs _)
  have hunit : (D.pt τ).evalAt (phi N σ (s (pivotIndex s v hr))) ≠ 0 :=
    (D.pt τ).evalAt_ne_zero (isRational_FC _) hsp0 hordp'
  have hinvmem : (phi N σ (s (pivotIndex s v hr)))⁻¹ ∈ (D.pt τ).toValuationSubring := by
    apply (D.pt τ).mem_of_ord_nonneg (inv_ne_zero hsp0)
    rw [(D.pt τ).ord_inv, hordp', neg_zero]
  have hinv : (D.pt τ).evalAt ((phi N σ (s (pivotIndex s v hr)))⁻¹)
      = ((D.pt τ).evalAt (phi N σ (s (pivotIndex s v hr))))⁻¹ := by
    have h1 : (D.pt τ).evalAt (phi N σ (s (pivotIndex s v hr)))
        * (D.pt τ).evalAt ((phi N σ (s (pivotIndex s v hr)))⁻¹) = 1 := by
      rw [← (D.pt τ).evalAt_mul (isRational_FC _) (hreg _) hinvmem, mul_inv_cancel₀ hsp0,
        (D.pt τ).evalAt_one]
    exact eq_inv_of_mul_eq_one_right h1
  refine ⟨τ, hcomap, ((D.pt τ).evalAt (phi N σ (s (pivotIndex s v hr))))⁻¹, inv_ne_zero hunit, funext fun i => ?_⟩
  obtain ⟨hmem, -, hev⟩ := ratio_mem N s hs v hr i
  rw [Pi.smul_apply, smul_eq_mul, ← hev, evalAt_transport σ v (D.pt τ) hcomap hmem, map_mul, map_inv₀,
    hval i, (D.pt τ).evalAt_mul (isRational_FC _) (hreg i) hinvmem, hinv, mul_comm]

theorem Φint_eq_realize (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → modularFunctionFieldBar N)
    (τ : ℍ) (i : Fin r)
    (hc : ContinuousAt (fun z : ℂ => realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ)) :
    Φint σ s (τ : ℂ) i = realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) τ := by
  have ht : Filter.Tendsto (fun z : ℂ => realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (ofComplex z))
      (𝓝[≠] (τ : ℂ)) (𝓝 (realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) τ)) := by
    have h := hc.tendsto
    rw [UpperHalfPlane.ofComplex_apply] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ht.limUnder_eq

theorem Φint_smul (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ)
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    Φint σ s (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = Φint σ s (τ : ℂ) := by
  funext i
  exact ext_smul D γ (phi N σ (s i)) τ ((interiorInputs D σ s hs).reg τ i)

theorem Φint_congr {σ σ₀ : AlgebraicClosure ℚ →+* ℂ} {s : Fin r → modularFunctionFieldBar N}
    (h : (fun i => phi N σ (s i)) = fun i => phi N σ₀ (s i)) : Φint σ s = Φint σ₀ s := by
  funext z i
  simp only [Φint_eq_ext, congrFun h i]

theorem exists_coset_reps :
    ∃ S₀ : Finset SL(2, ℤ), ∀ g : SL(2, ℤ), ∃ γ ∈ CongruenceSubgroup.Gamma0 N, ∃ s₀ ∈ S₀, g = γ * s₀ :=
  exists_coset_reps' (CongruenceSubgroup.Gamma0 N)

omit [NeZero N] in
theorem isCompact_box' (B y₀ Y₁ : ℝ) :
    IsCompact {z : ℂ | |z.re| ≤ B ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁} := by
  have : {z : ℂ | |z.re| ≤ B ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁} = (Set.Icc (-B) B) ×ℂ (Set.Icc y₀ Y₁) := by
    ext z
    simp only [Set.mem_setOf_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le]
  rw [this]
  exact isCompact_Icc.reProdIm isCompact_Icc

theorem interior_chart' (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ)
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (t : ℂ) (ht : 0 < t.im) :
    (∀ i, AnalyticOnNhd ℂ (fun z => Φint σ s z i) (ball t (t.im / 2))) ∧
    (∀ z ∈ ball t (t.im / 2), Φint σ s z ≠ 0) ∧
    (∀ a : Fin r → ℂ, a ≠ 0 → ∀ z ∈ ball t (t.im / 2),
      analyticOrderAt (fun w => ∑ j, a j * Φint σ s w j) z ≠ ⊤) ∧
    (∀ i, ∀ ρ' : ℝ, ρ' < t.im / 2 → ∃ L, LipschitzOnWith L (fun z => Φint σ s z i) (closedBall t ρ')) := by
  obtain ⟨-, hA, -, hZ, hF⟩ := interior_chart D σ s hs ⟨t, ht⟩
  exact ⟨hA, hZ, fun a ha => hF a (linComb_phi_ne_zero' σ hs.1 a ha),
    fun i ρ' hρ' => lipschitzOn_of_analyticOnNhd (hA i) hρ'⟩

theorem phi_mem_pt_of_memL (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) {k : ℕ} {u : FB N}
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (τ : ℍ) :
    phi N σ u ∈ (D.pt τ).toValuationSubring := by
  classical
  rcases CUSPATLAS.forall_mem_or_exists_comap σ (D.pt τ) with hall | ⟨y, hy⟩
  · exact hall u
  · rcases eq_or_ne u 0 with rfl | hu0
    · rw [map_zero]; exact zero_mem _
    have hyinf : y ≠ cuspInftyBar N := by
      intro h
      apply ATLINT.jB_notMem (N := N)
      rw [← h, hy, ValuationSubring.mem_comap, phi_jB]
      exact ATLINT.jC_mem_pt D τ
    have hE : ((k : ℤ) • embDivisor N) y = 0 := by
      simp [embDivisor, Finsupp.smul_apply, Finsupp.single_apply, Ne.symm hyinf]
    have hord : 0 ≤ y.ord u := by
      have h := neg_le_ord_of_mem _ huL hu0 y
      rw [hE, neg_zero] at h
      exact h
    have huy : u ∈ y.toValuationSubring := y.mem_of_ord_nonneg hu0 hord
    rw [hy, ValuationSubring.mem_comap] at huy
    exact huy

theorem ext_eq_evalAt_of_memL (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) {k : ℕ} {u : FB N}
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (τ : ℍ) :
    ATLINT.ext (N := N) (phi N σ u) (τ : ℂ) = (D.pt τ).evalAt (phi N σ u) :=
  (ATLINT.ext_analyticAt D _ τ (phi_mem_pt_of_memL D σ huL τ)).2.2

theorem analyticAt_ext_of_memL (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) {k : ℕ} {u : FB N}
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (τ : ℍ) :
    AnalyticAt ℂ (ATLINT.ext (N := N) (phi N σ u)) (τ : ℂ) :=
  (ATLINT.ext_analyticAt D _ τ (phi_mem_pt_of_memL D σ huL τ)).1

theorem continuousOn_ext_of_memL (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) {k : ℕ} {u : FB N}
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) {S : Set ℂ} (hS : ∀ z ∈ S, 0 < z.im) :
    ContinuousOn (ATLINT.ext (N := N) (phi N σ u)) S :=
  fun z hz => (analyticAt_ext_of_memL D σ huL ⟨z, hS z hz⟩).continuousAt.continuousWithinAt

theorem ext_smul_of_memL (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) {k : ℕ} {u : FB N}
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    ATLINT.ext (N := N) (phi N σ u) (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = ATLINT.ext (N := N) (phi N σ u) (τ : ℂ) :=
  ATLINT.ext_smul D γ _ τ (phi_mem_pt_of_memL D σ huL τ)

theorem iSup_norm_Φint_pos (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (hs : IsEmbBasis N s) (τ : ℍ) : 0 < ⨆ i, ‖Φint σ s (τ : ℂ) i‖ := by
  rw [← pi_norm_eq_ciSup]
  exact norm_pos_iff.2 (ATLINT.interior_ne_zero D σ s hs (ATLINT.interiorInputs D σ s hs) τ)

theorem psiU_gt_of_not_le (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (hs : IsEmbBasis N s) {k : ℕ} {u : FB N} (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) (τ : ℍ)
    {S lam : ℝ}
    (h : ¬ ‖ATLINT.ext (N := N) (phi N σ u) (τ : ℂ)‖ ≤ Real.exp (S - lam) * (⨆ i, ‖Φint σ s (τ : ℂ) i‖) ^ k) :
    S - lam < PLB.psiU D σ s k u τ := by
  rw [not_le] at h
  have hM := iSup_norm_Φint_pos D σ s hs τ
  have hpos : 0 < Real.exp (S - lam) * (⨆ i, ‖Φint σ s (τ : ℂ) i‖) ^ k := by positivity
  have hU : 0 < ‖ATLINT.ext (N := N) (phi N σ u) (τ : ℂ)‖ := hpos.trans h
  unfold PLB.psiU
  rw [← ext_eq_evalAt_of_memL D σ huL τ]
  have := Real.log_lt_log hpos h
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hM k).ne', Real.log_exp, Real.log_pow] at this
  linarith

theorem analyticOrderAt_eq_one_of_divided {F G : ℂ → ℂ} {w : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hF : AnalyticAt ℂ F w)
    (hFG : ∀ z ∈ closedBall w ρ, F z = (z - w) * G z) (hGc : ContinuousAt G w) (hG0 : G w ≠ 0) :
    analyticOrderAt F w = 1 := by
  have hGan : AnalyticAt ℂ G w := by
    refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hGc
    have hFev : ∀ᶠ z in 𝓝 w, AnalyticAt ℂ F z := hF.eventually_analyticAt
    have h1 : ∀ᶠ z in 𝓝[≠] w, AnalyticAt ℂ F z ∧ z ∈ ball w ρ :=
      mem_nhdsWithin_of_mem_nhds (hFev.and (ball_mem_nhds w hρ))
    filter_upwards [self_mem_nhdsWithin, h1] with z hz ⟨hFz, hzb⟩
    have hev : G =ᶠ[𝓝 z] fun y => F y / (y - w) := by
      have hopen : IsOpen (ball w ρ \ {w}) := isOpen_ball.sdiff isClosed_singleton
      filter_upwards [hopen.mem_nhds ⟨hzb, hz⟩] with y hy
      rw [hFG y (ball_subset_closedBall hy.1), mul_div_cancel_left₀ _ (sub_ne_zero.2 hy.2)]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    exact hFz.differentiableAt.div (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.2 hz)
  have h : analyticOrderAt F w = (1 : ℕ) := by
    rw [hF.analyticOrderAt_eq_natCast]
    refine ⟨G, hGan, hG0, ?_⟩
    filter_upwards [closedBall_mem_nhds w hρ] with z hz
    rw [hFG z hz, pow_one, smul_eq_mul]
  exact_mod_cast h

theorem exists_minor_ne_zero_of_order_one {F : ℂ → (Fin r → ℂ)} {c : ℂ}
    (hA : ∀ i, AnalyticAt ℂ (fun z => F z i) c) (hF0 : F c ≠ 0)
    {b : Fin r → ℂ} (hb : analyticOrderAt (fun z => ∑ i, b i * F z i) c = 1) :
    ∃ q : Fin r × Fin r, F c q.1 * deriv (fun z => F z q.2) c - F c q.2 * deriv (fun z => F z q.1) c ≠ 0 := by
  classical
  have hsum : AnalyticAt ℂ (fun z => ∑ i, b i * F z i) c :=
    Finset.univ.analyticAt_sum (c := c) (f := fun i => fun z => b i * F z i)
      (fun i _ => analyticAt_const.mul (hA i)) |>.congr (Filter.Eventually.of_forall fun z => by simp [Finset.sum_apply])
  obtain ⟨g, hg, hg0, hev⟩ := (hsum.analyticOrderAt_eq_natCast (n := 1)).1 (by exact_mod_cast hb)

  have hval : ∑ i, b i * F c i = 0 := by
    have := hev.self_of_nhds; simpa using this
  have hder : deriv (fun z => ∑ i, b i * F z i) c = g c := by
    have h1 : HasDerivAt (fun z => (z - c) ^ 1 • g z) (g c) c := by
      have := ((hasDerivAt_id c).sub_const c).fun_smul (hg.differentiableAt.hasDerivAt)
      first
        | simpa using this
        | (have h' := this; simp at h'; exact h')
        | (simp; exact this)
        | exact this
    exact (h1.congr_of_eventuallyEq hev).deriv

  set Dv : Fin r → ℂ := fun j => deriv (fun z => F z j) c with hDv
  have hder' : deriv (fun z => ∑ i, b i * F z i) c = ∑ i, b i * Dv i := by
    rw [hDv]
    have : (fun z => ∑ i, b i * F z i) = ∑ i, (fun z => b i * F z i) := by funext z; simp [Finset.sum_apply]
    rw [this, deriv_sum (fun i _ => (hA i).differentiableAt.const_mul (b i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [deriv_const_mul _ (hA i).differentiableAt]
  by_contra hall
  rw [not_exists] at hall
  simp only [not_not] at hall

  obtain ⟨p, hp⟩ : ∃ p, F c p ≠ 0 := by
    by_contra h; apply hF0; funext i; simp only [not_exists, not_not] at h; exact h i
  have hpar : ∀ i, Dv i = (Dv p / F c p) * F c i := by
    intro i
    have := hall (p, i)
    simp only at this
    field_simp
    linear_combination this
  have : g c = 0 := by
    rw [← hder, hder']
    calc ∑ i, b i * Dv i = (Dv p / F c p) * ∑ i, b i * F c i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hpar i]; ring
      _ = 0 := by rw [hval, mul_zero]
  exact hg0 this

theorem exists_ball_minor_ne_zero {F : ℂ → (Fin r → ℂ)} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hA : ∀ i, AnalyticOnNhd ℂ (fun z => F z i) (ball c R))
    (h0 : ∃ q : Fin r × Fin r, F c q.1 * deriv (fun z => F z q.2) c - F c q.2 * deriv (fun z => F z q.1) c ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ ∀ w ∈ closedBall c ρ,
      ∃ q : Fin r × Fin r, F w q.1 * deriv (fun z => F z q.2) w - F w q.2 * deriv (fun z => F z q.1) w ≠ 0 := by
  obtain ⟨q, hq⟩ := h0
  have hcont : ContinuousAt (fun w => F w q.1 * deriv (fun z => F z q.2) w - F w q.2 * deriv (fun z => F z q.1) w) c := by
    have hF : ∀ i, ContinuousAt (fun w => F w i) c := fun i => (hA i c (mem_ball_self hR)).continuousAt
    have hD : ∀ i, ContinuousAt (fun w => deriv (fun z => F z i) w) c := fun i =>
      ((hA i).deriv c (mem_ball_self hR)).continuousAt
    exact ((hF q.1).mul (hD q.2)).sub ((hF q.2).mul (hD q.1))
  have hev := hcont.eventually_ne hq
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨min (ε / 2) (R / 2), by positivity, by linarith [min_le_right (ε/2) (R/2)], fun w hw => ⟨q, ?_⟩⟩
  exact hεb w (closedBall_subset_ball (by linarith [min_le_left (ε/2) (R/2)]) hw)

theorem exists_smul_of_wedge_eq_zero {y x : Fin r → ℂ} (h : wedge y x = 0) (hx : x ≠ 0) :
    ∃ c : ℂ, y = c • x := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
    by_contra h'; apply hx; funext i; simp only [not_exists, not_not] at h'; exact h' i
  refine ⟨y p / x p, funext fun i => ?_⟩
  have := congrFun h (p, i)
  simp only [wedge, Pi.zero_apply] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination (-1 : ℂ) * this

theorem pchd_pos_of_not_prop {y x : Fin r → ℂ} (hy : y ≠ 0) (hx : x ≠ 0)
    (h : ¬ ∃ c : ℂ, c ≠ 0 ∧ y = c • x) : 0 < pchd y x := by
  have hw : wedge y x ≠ 0 := by
    intro hw
    obtain ⟨c, hc⟩ := exists_smul_of_wedge_eq_zero hw hx
    refine h ⟨c, ?_, hc⟩
    rintro rfl
    rw [zero_smul] at hc
    exact hy hc
  unfold pchd
  exact div_pos (norm_pos_iff.2 hw) (mul_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx))

theorem qParam_add_int_mul' (h : ℝ) (hh : h ≠ 0) (z : ℂ) (n : ℤ) :
    Function.Periodic.qParam h (z + n * h) = Function.Periodic.qParam h z := by
  simp only [Function.Periodic.qParam]
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  rw [show 2 * ↑Real.pi * Complex.I * (z + ↑n * ↑h) / ↑h =
      2 * ↑Real.pi * Complex.I * z / ↑h + n * (2 * ↑Real.pi * Complex.I) by field_simp]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem ofComplex_add_int_mul_nat_eq (z : ℂ) (hz : 0 < z.im) (n : ℤ) (h : ℕ) :
    UpperHalfPlane.ofComplex (z + n * ((h : ℝ) : ℂ)) = (ModularGroup.T ^ (n * (h : ℤ))) • UpperHalfPlane.ofComplex z := by
  rw [UpperHalfPlane.modular_T_zpow_smul]
  apply UpperHalfPlane.ext
  have hz' : 0 < (z + n * ((h : ℝ) : ℂ)).im := by simpa using hz
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz', UpperHalfPlane.coe_vadd, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  push_cast
  ring

theorem conj_T_zpow_int_mul_mem (N : ℕ) (g : SL(2, ℤ)) (n : ℤ) :
    g * ModularGroup.T ^ (n * (N : ℤ)) * g⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
  have h1 : MulAut.conj g (ModularGroup.T ^ (N : ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
    rw [MulAut.conj_apply]; exact conj_T_zpow_mem_Gamma0 N g
  have h2 := Subgroup.zpow_mem _ h1 n
  rw [← map_zpow, ← zpow_mul, MulAut.conj_apply] at h2
  rwa [mul_comm n]

theorem ofComplex_add_nat_eq (z : ℂ) (hz : 0 < z.im) (h : ℕ) :
    UpperHalfPlane.ofComplex (z + h) = (ModularGroup.T ^ (h : ℤ)) • UpperHalfPlane.ofComplex z := by
  rw [UpperHalfPlane.modular_T_zpow_smul]
  apply UpperHalfPlane.ext
  have hz' : 0 < (z + h).im := by simpa using hz
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz', UpperHalfPlane.coe_vadd, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  push_cast
  ring

theorem differentiableAt_coe_smul_ofComplex (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) z := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) =ᶠ[𝓝 z]
      fun z => (((g 0 0 : ℤ) : ℂ) * z + ((g 0 1 : ℤ) : ℂ)) / (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) := by
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    rw [Rot3.coe_smul_eq, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hden : ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero g (UpperHalfPlane.ofComplex z)
    rw [UpperHalfPlane.denom, UpperHalfPlane.ofComplex_apply_of_im_pos hz] at this
    simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe] using this
  exact ((differentiableAt_const _ |>.mul differentiableAt_id).add (differentiableAt_const _)).div
    ((differentiableAt_const _ |>.mul differentiableAt_id).add (differentiableAt_const _)) hden

theorem utilde (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (g : SL(2, ℤ)) {h : ℕ} (hh : 0 < h) (hΓ : g * ModularGroup.T ^ (h : ℤ) * g⁻¹ ∈ CongruenceSubgroup.Gamma0 N)
    {Φc : ℂ → (Fin r → ℂ)} {m : ℤ} {A rc : ℝ} (hA : 0 < A) (hrc : 0 < rc) (hrc1 : rc < 1)
    (hΦcc : ContinuousOn Φc (closedBall 0 rc))
    (hlift : ∀ q : ℂ, q ≠ 0 → ‖q‖ ≤ rc → A ≤ (Function.Periodic.invQParam (h : ℝ) q).im)
    {A' : ℝ} (hqA : ∀ τ : ℍ, A' ≤ τ.im → ‖Function.Periodic.qParam (h : ℝ) (τ : ℂ)‖ ≤ rc)
    (hV : ∀ τ : ℍ, A ≤ τ.im →
      Φc (Function.Periodic.qParam (h : ℝ) (τ : ℂ)) = Function.Periodic.qParam (h : ℝ) (τ : ℂ) ^ m • Φint σ s ((g • τ : ℍ) : ℂ))
    {k : ℕ} {u : FB N} (hu : u ≠ 0) (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    {S : ℝ} (hS : ∀ τ : ℍ, (D.pt τ).evalAt (phi N σ u) ≠ 0 → PLB.psiU D σ s k u τ ≤ S) :
    ∃ Ut : ℂ → ℂ, ContinuousOn Ut (closedBall 0 rc) ∧
      ∀ q : ℂ, q ≠ 0 → ‖q‖ ≤ rc →
        Ut q = (q ^ m) ^ k * ATLINT.ext (N := N) (phi N σ u)
          ((g • UpperHalfPlane.ofComplex (Function.Periodic.invQParam (h : ℝ) q) : ℍ) : ℂ) := by
  classical
  have hw : (0 : ℝ) < h := by exact_mod_cast hh
  set U : ℂ → ℂ := fun z => ATLINT.ext (N := N) (phi N σ u) z with hUdef
  set F : ℂ → ℂ := fun z => U ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ) with hFdef
  set G : ℂ → ℂ := fun z => (Function.Periodic.qParam (h : ℝ) z ^ m) ^ k * F z with hGdef

  have hper_q : Function.Periodic (Function.Periodic.qParam (h : ℝ)) (h : ℝ) := by
    intro z
    simp only [Function.Periodic.qParam]
    have hh0 : ((h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    rw [show 2 * ↑Real.pi * Complex.I * (z + ↑(h : ℝ)) / ↑(h : ℝ) =
        2 * ↑Real.pi * Complex.I * z / ↑(h : ℝ) + 2 * ↑Real.pi * Complex.I by field_simp]
    simp [Complex.exp_add]
  have hperF : Function.Periodic F (h : ℝ) := by
    intro z
    simp only [F]
    by_cases hz : 0 < z.im
    · have h1 : UpperHalfPlane.ofComplex (z + (h : ℝ)) = (ModularGroup.T ^ (h : ℤ)) • UpperHalfPlane.ofComplex z := by
        have := ofComplex_add_nat_eq z hz h
        push_cast at this ⊢
        exact this
      rw [h1, ← mul_smul, show g * ModularGroup.T ^ (h : ℤ) = (g * ModularGroup.T ^ (h : ℤ) * g⁻¹) * g by group,
        mul_smul]
      exact ext_smul_of_memL D σ huL ⟨_, hΓ⟩ _
    · have hz' : ¬ 0 < (z + (h : ℝ)).im := by simpa using hz
      rw [UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.1 hz'),
        UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.1 hz)]
  have hperG : Function.Periodic G (h : ℝ) := fun z => by
    simp only [G]; rw [hper_q z, hperF z]

  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hdiffF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ F z := by
    intro z hz
    have hU : DifferentiableAt ℂ (fun w : ℂ => ATLINT.ext (N := N) (phi N σ u) w) ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ) :=
      (analyticAt_ext_of_memL D σ huL (g • UpperHalfPlane.ofComplex z)).differentiableAt
    show DifferentiableAt ℂ ((fun w : ℂ => ATLINT.ext (N := N) (phi N σ u) w) ∘
      (fun z : ℂ => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ))) z
    exact DifferentiableAt.comp z hU (differentiableAt_coe_smul_ofComplex g hz)
  have hdiffG : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ G z := by
    intro z hz
    have hq0 : Function.Periodic.qParam (h : ℝ) z ≠ 0 := by
      first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]
    exact (((Function.Periodic.differentiable_qParam (h := (h : ℝ))) z |>.zpow (Or.inl hq0)).pow k).mul (hdiffF z hz)
  have hevH : ∀ᶠ z in Filter.comap Complex.im Filter.atTop, DifferentiableAt ℂ G z := by
    refine Filter.eventually_comap.2 ((Filter.eventually_gt_atTop 0).mono fun y hy z hz => hdiffG z (by rw [hz]; exact hy))

  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) rc).exists_bound_of_continuousOn hΦcc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_closedBall_self hrc.le))
  have hbound : ∀ z : ℂ, max A A' ≤ z.im → ‖G z‖ ≤ Real.exp S * M ^ k := by
    intro z hz
    have hzA : A ≤ z.im := (le_max_left _ _).trans hz
    have hzA' : A' ≤ z.im := (le_max_right _ _).trans hz
    have hzpos : 0 < z.im := hA.trans_le hzA
    set τ : ℍ := ⟨z, hzpos⟩ with hτ
    have hτim : A ≤ τ.im := hzA
    have hτim' : A' ≤ τ.im := hzA'
    have hofc : UpperHalfPlane.ofComplex z = τ := by
      rw [hτ]; exact UpperHalfPlane.ofComplex_apply_of_im_pos hzpos
    set q : ℂ := Function.Periodic.qParam (h : ℝ) z with hqdef
    have hq0 : q ≠ 0 := by rw [hqdef]; first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]
    have hqrc : q ∈ closedBall (0 : ℂ) rc := by
      rw [mem_closedBall, dist_zero_right]; exact hqA τ hτim'
    have hΦq : Φc q = q ^ m • Φint σ s ((g • τ : ℍ) : ℂ) := hV τ hτim
    have hGz : G z = (q ^ m) ^ k * U ((g • τ : ℍ) : ℂ) := by simp only [hGdef, hFdef, hofc, hqdef]
    rw [hGz, norm_mul, norm_pow]
    by_cases hU0 : (D.pt (g • τ)).evalAt (phi N σ u) = 0
    · have : U ((g • τ : ℍ) : ℂ) = 0 := by rw [hUdef]; simp only []; rw [ext_eq_evalAt_of_memL D σ huL, hU0]
      rw [this, norm_zero, mul_zero]; positivity
    · have hψ := hS (g • τ) hU0
      unfold PLB.psiU at hψ
      rw [← ext_eq_evalAt_of_memL D σ huL] at hψ
      have hMτ := iSup_norm_Φint_pos D σ s hs (g • τ)
      have hsup : (⨆ i, ‖Φint σ s ((g • τ : ℍ) : ℂ) i‖) = ‖q ^ m‖⁻¹ * ⨆ i, ‖Φc q i‖ := by
        rw [← pi_norm_eq_ciSup, ← pi_norm_eq_ciSup, hΦq, norm_smul, ← mul_assoc,
          inv_mul_cancel₀ (norm_ne_zero_iff.2 (zpow_ne_zero _ hq0)), one_mul]
      have hUpos : 0 < ‖U ((g • τ : ℍ) : ℂ)‖ := by
        rw [hUdef]; simp only []
        rw [ext_eq_evalAt_of_memL D σ huL]; exact norm_pos_iff.2 hU0

      have h1 : Real.log ‖U ((g • τ : ℍ) : ℂ)‖ ≤ S + k * Real.log (‖q ^ m‖⁻¹ * ⨆ i, ‖Φc q i‖) := by
        rw [← hsup]; linarith
      have hcpos : 0 < ⨆ i, ‖Φc q i‖ := by
        have : 0 < ‖q ^ m‖⁻¹ * ⨆ i, ‖Φc q i‖ := by rw [← hsup]; exact hMτ
        exact pos_of_mul_pos_right this (by positivity)
      have hcle : (⨆ i, ‖Φc q i‖) ≤ M := by rw [← pi_norm_eq_ciSup]; exact hM q hqrc
      have h2 : ‖U ((g • τ : ℍ) : ℂ)‖ ≤ Real.exp S * (‖q ^ m‖⁻¹ * ⨆ i, ‖Φc q i‖) ^ k := by
        have := Real.exp_le_exp.2 h1
        rwa [Real.exp_log hUpos, Real.exp_add, ← Real.log_pow,
          Real.exp_log (pow_pos (mul_pos (inv_pos.2 (norm_pos_iff.2 (zpow_ne_zero _ hq0))) hcpos) k)] at this
      calc ‖q ^ m‖ ^ k * ‖U ((g • τ : ℍ) : ℂ)‖
          ≤ ‖q ^ m‖ ^ k * (Real.exp S * (‖q ^ m‖⁻¹ * ⨆ i, ‖Φc q i‖) ^ k) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Real.exp S * (⨆ i, ‖Φc q i‖) ^ k := by
            rw [mul_pow, inv_pow]; field_simp
        _ ≤ Real.exp S * M ^ k := by gcongr
  have hbdd : (Filter.comap Complex.im Filter.atTop).BoundedAtFilter G := by
    rw [Filter.BoundedAtFilter, Asymptotics.isBigO_iff]
    refine ⟨Real.exp S * M ^ k, Filter.eventually_comap.2 ((Filter.eventually_ge_atTop (max A A')).mono fun y hy z hz => ?_)⟩
    simp only [Pi.one_apply, norm_one, mul_one]
    exact hbound z (by rw [hz]; exact hy)

  refine ⟨Function.Periodic.cuspFunction (h : ℝ) G, fun q hq => ?_, fun q hq0 hqn => ?_⟩
  · by_cases hq0 : q = 0
    · subst hq0
      exact (Function.Periodic.differentiableAt_cuspFunction_zero hw hperG hevH hbdd).continuousAt.continuousWithinAt
    · have hqn : ‖q‖ ≤ rc := by simpa [mem_closedBall, dist_zero_right] using hq
      have him : 0 < (Function.Periodic.invQParam (h : ℝ) q).im := hA.trans_le (hlift q hq0 hqn)
      have hd := Function.Periodic.differentiableAt_cuspFunction hw.ne' hperG (hdiffG _ him)
      rw [Function.Periodic.qParam_right_inv hw.ne' hq0] at hd
      exact hd.continuousAt.continuousWithinAt
  · have h1 := Function.Periodic.eq_cuspFunction hw.ne' hperG (Function.Periodic.invQParam (h : ℝ) q)
    rw [Function.Periodic.qParam_right_inv hw.ne' hq0] at h1
    rw [h1]
    simp only [hGdef, hFdef, hUdef, Function.Periodic.qParam_right_inv hw.ne' hq0]

theorem cusp_strong {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → ↥(modularFunctionFieldBar N))
    (hs : IsEmbBasis N s) (γ : SL(2, ℤ)) {w : ℝ} (hw : 0 < w)
    (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) :
    ∃ (Φ : ℂ → (Fin r → ℂ)) (m : ℤ), (∀ i, AnalyticAt ℂ (fun q => Φ q i) 0) ∧ Φ 0 ≠ 0 ∧
      (∃ p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), jB N ∉ p.toValuationSubring ∧
        ∃ c : ℂ, c ≠ 0 ∧ Φ 0 = c • (fun i => σ (evalVec s p i))) ∧
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ τ : ℍ, A₀ ≤ τ.im →
      (∀ i, ContinuousAt (fun z : ℂ => realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (ofComplex z))
        ((γ • τ : ℍ) : ℂ)) ∧
      ∀ i, Φ (Function.Periodic.qParam w (τ : ℂ)) i =
        Function.Periodic.qParam w (τ : ℂ) ^ m * realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (γ • τ) := by
  classical
  have hr := r_pos N s hs
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  set x : Fin r → FC N := fun i => phi N σ (s i) with hxdef
  have hx : ∀ i, x i ≠ 0 := fun i => phi_ne_zero σ (hs0 i)

  have hpres : ∀ i, ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      ((x i : FC N) : LaurentSeries ℂ) * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := fun i =>
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N _ (x i).2
  choose k g h hh0 hxhg using hpres
  have hsc := fun i => slash_chart N (x i) (hx i) (g i) (h i) (hh0 i) (hxhg i) γ hw hΓ
  choose hQ0 Φc hΦc hΦc0 hev using hsc
  set e : Fin r → ℤ := fun i => (slashQuot N (g i) (h i) γ w).order with he

  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  set m : ℤ := e i₀ with hm
  have hmle : ∀ i, m ≤ e i := fun i => hi₀ i (Finset.mem_univ i)
  have hn : ∀ i, ∃ n : ℕ, e i - m = n := fun i => ⟨_, (Int.toNat_of_nonneg (sub_nonneg.mpr (hmle i))).symm⟩
  choose n hn using hn
  set Φ : ℂ → Fin r → ℂ := fun q i => q ^ (n i) * Φc i q with hΦ

  have hqlim : Tendsto (fun τ : ℍ => Function.Periodic.qParam w (τ : ℂ)) atImInfty (𝓝 0) :=
    UpperHalfPlane.qParam_tendsto_atImInfty hw
  obtain ⟨A₀, hA₀pos, hA₀⟩ := exists_forall_of_eventually_atImInfty (P := fun i τ =>
    realize N ((x i : FC N) : LaurentSeries ℂ) (γ • τ) =
      Function.Periodic.qParam w (τ : ℂ) ^ (slashQuot N (g i) (h i) γ w).order *
        Φc i (Function.Periodic.qParam w (τ : ℂ)) ∧
      AnalyticAt ℂ (Φc i) (Function.Periodic.qParam w (τ : ℂ)))
    (fun i => (hev i).and (hqlim.eventually (hΦc i).eventually_analyticAt))

  have hΦc00 : ∀ i, Φc i 0 ≠ 0 := fun i => by
    rw [hΦc0 i, ← HahnSeries.leadingCoeff_eq]
    exact HahnSeries.leadingCoeff_ne_zero.mpr (hQ0 i)
  refine ⟨Φ, -m, ?_, ?_, ?_, A₀ + 1, by linarith, fun τ hτ => ⟨fun i => ?_, ?_⟩⟩
  · exact fun i => (analyticAt_id.pow (n i)).mul (hΦc i)
  · intro h0
    have h1 : Φ 0 i₀ = 0 := by rw [h0]; rfl
    have hni : n i₀ = 0 := by have := hn i₀; rw [hm] at this; omega
    have : Φc i₀ 0 = 0 := by
      have h2 : (0 : ℂ) ^ (n i₀) * Φc i₀ 0 = 0 := h1
      rwa [hni, pow_zero, one_mul] at h2
    exact hΦc00 i₀ this

  ·
    obtain ⟨p, hp⟩ := exists_place_cuspW γ hw hΓ σ
    have hθ : ∀ i, cuspExpHomW γ hw hΓ (x i) = slashQuot N (g i) (h i) γ w := fun i => by
      rw [cuspExpHomW_apply]; exact cuspExpW_eq_slashQuot γ hw hΓ ⟨hh0 i, hxhg i⟩
    have hθ0 : ∀ i, cuspExpHomW γ hw hΓ (x i) ≠ 0 := fun i => by rw [hθ i]; exact hQ0 i
    have he' : ∀ i, (cuspExpHomW γ hw hΓ (x i)).order = e i := fun i => by rw [hθ i]
    have hlc : ∀ i, (cuspExpHomW γ hw hΓ (x i)).leadingCoeff = Φc i 0 := fun i => by
      rw [HahnSeries.leadingCoeff_eq, hθ i, ← hΦc0 i]
    have hpc : jB N ∉ p.toValuationSubring := by
      intro hmem
      have h1 := (mem_place_cuspW_iff hp (jB N)).mp hmem
      rw [phi_jB] at h1
      linarith [order_cuspExpHomW_jC_neg γ hw hΓ (N := N)]
    set π := pivotIndex s p hr with hπ
    have hrat : ∀ i, s i * (s π)⁻¹ ∈ p.toValuationSubring ∧ evalVec s p i = p.evalAt (s i * (s π)⁻¹) := fun i => by
      obtain ⟨hmem, -, hev⟩ := ratio_mem N s hs p hr i
      exact ⟨hmem, hev.symm⟩
    have heπ : ∀ i, e π ≤ e i := by
      intro i
      have h1 := (mem_place_cuspW_iff hp _).mp (hrat i).1
      have h2 : cuspExpHomW γ hw hΓ (phi N σ (s i * (s π)⁻¹)) = cuspExpHomW γ hw hΓ (x i) * (cuspExpHomW γ hw hΓ (x π))⁻¹ := by
        rw [map_mul, map_inv₀, map_mul, map_inv₀]
      rw [h2, HahnSeries.order_mul (hθ0 i) (inv_ne_zero (hθ0 π)), LaurentSeries.order_inv' (hθ0 π), he', he'] at h1
      linarith
    have heπm : e π = m := le_antisymm ((heπ i₀).trans (le_of_eq hm.symm)) (hmle π)
    have hnπ : n π = 0 := by have := hn π; omega
    refine ⟨p, hpc, Φc π 0, hΦc00 π, funext fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [(hrat i).2, ← coeff_zero_cuspExp_eq hp (hrat i).1]
    have h2 : cuspExpHomW γ hw hΓ (phi N σ (s i * (s π)⁻¹)) = cuspExpHomW γ hw hΓ (x i) * (cuspExpHomW γ hw hΓ (x π))⁻¹ := by
      rw [map_mul, map_inv₀, map_mul, map_inv₀]
    rw [h2]
    show (0 : ℂ) ^ (n i) * Φc i 0 = Φc π 0 * (cuspExpHomW γ hw hΓ (x i) * (cuspExpHomW γ hw hΓ (x π))⁻¹).coeff 0
    have hRord : (cuspExpHomW γ hw hΓ (x i) * (cuspExpHomW γ hw hΓ (x π))⁻¹).order = e i - e π := by
      rw [HahnSeries.order_mul (hθ0 i) (inv_ne_zero (hθ0 π)), LaurentSeries.order_inv' (hθ0 π), he', he']; ring
    by_cases hei : e i = e π
    · have hni : n i = 0 := by have := hn i; omega
      have hR0 : (cuspExpHomW γ hw hΓ (x i) * (cuspExpHomW γ hw hΓ (x π))⁻¹).order = 0 := by rw [hRord, hei, sub_self]
      have h1 : (cuspExpHomW γ hw hΓ (x i) * (cuspExpHomW γ hw hΓ (x π))⁻¹).coeff 0 =
          (cuspExpHomW γ hw hΓ (x i) * (cuspExpHomW γ hw hΓ (x π))⁻¹).leadingCoeff := by
        rw [HahnSeries.leadingCoeff_eq, hR0]
      have h3 : (cuspExpHomW γ hw hΓ (x i) * (cuspExpHomW γ hw hΓ (x π))⁻¹).leadingCoeff * (cuspExpHomW γ hw hΓ (x π)).leadingCoeff
          = (cuspExpHomW γ hw hΓ (x i)).leadingCoeff := by
        rw [← HahnSeries.leadingCoeff_mul, inv_mul_cancel_right₀ (hθ0 π)]
      rw [hni, pow_zero, one_mul, h1]
      rw [hlc, hlc] at h3
      rw [← h3]; ring
    · have hni : 0 < n i := by have := hn i; have := heπ i; omega
      have hR0 : (0 : ℤ) < (cuspExpHomW γ hw hΓ (x i) * (cuspExpHomW γ hw hΓ (x π))⁻¹).order := by
        rw [hRord]; have := heπ i; omega
      rw [zero_pow hni.ne', zero_mul, HahnSeries.coeff_eq_zero_of_lt_order hR0, mul_zero]
  ·
    have hopen : IsOpen {τ' : ℍ | A₀ < τ'.im} := isOpen_lt continuous_const UpperHalfPlane.continuous_im
    have hev' : (fun τ' : ℍ => realize N ((x i : FC N) : LaurentSeries ℂ) (γ • τ')) =ᶠ[𝓝 τ]
        fun τ' => Function.Periodic.qParam w (τ' : ℂ) ^ e i * Φc i (Function.Periodic.qParam w (τ' : ℂ)) := by
      filter_upwards [hopen.mem_nhds (show A₀ < τ.im by linarith)] with τ' hτ'
      exact (hA₀ τ' hτ'.le i).1
    have hqd : Differentiable ℂ (Function.Periodic.qParam w) := Function.Periodic.differentiable_qParam
    have hq : ContinuousAt (fun τ' : ℍ => Function.Periodic.qParam w (τ' : ℂ)) τ :=
      (hqd _).continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt
    have hq0 : Function.Periodic.qParam w (τ : ℂ) ≠ 0 := by
      first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]
    have hF : ContinuousAt (fun τ' : ℍ => realize N ((x i : FC N) : LaurentSeries ℂ) (γ • τ')) τ :=
      (continuousAt_congr hev').mpr
        ((hq.zpow₀ _ (Or.inl hq0)).mul
          (ContinuousAt.comp_of_eq ((hA₀ τ (by linarith)) i).2.continuousAt hq rfl))

    have hfun : (fun z : ℂ => realize N ((x i : FC N) : LaurentSeries ℂ) (ofComplex z)) =
        (fun τ' : ℍ => realize N ((x i : FC N) : LaurentSeries ℂ) (γ • τ')) ∘
          (fun τ'' : ℍ => ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) • τ'') ∘ ofComplex := by
      funext z
      simp only [Function.comp_apply]
      congr 1
      exact (smul_inv_smul γ (ofComplex z)).symm
    rw [hfun]
    have hofc : ContinuousAt (UpperHalfPlane.ofComplex : ℂ → ℍ) ((γ • τ : ℍ) : ℂ) :=
      (UpperHalfPlane.isOpenEmbedding_coe.isInducing.continuousAt_iff).mpr
        ((continuousAt_congr (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex (γ • τ).im_pos)).mpr continuousAt_id)
    have hsm : ContinuousAt (fun τ'' : ℍ => ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) • τ'') (γ • τ) :=
      (continuous_const_smul ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)).continuousAt
    refine ContinuousAt.comp_of_eq hF (ContinuousAt.comp_of_eq hsm hofc (UpperHalfPlane.ofComplex_apply _)) ?_
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    exact inv_smul_smul γ τ
  · have hq0 : Function.Periodic.qParam w (τ : ℂ) ≠ 0 := by
      first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]
    intro i
    have h1 := (hA₀ τ (by linarith) i).1
    show Function.Periodic.qParam w (τ : ℂ) ^ (n i) * Φc i (Function.Periodic.qParam w (τ : ℂ)) = _
    rw [h1, ← mul_assoc, ← zpow_natCast, ← hn i, ← zpow_add₀ hq0]
    congr 2
    ring

theorem cusp_strong_Φint (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) (hs : IsEmbBasis N s) (γ : SL(2, ℤ))
    {w : ℝ} (hw : 0 < w) (hΓ : w ∈ (conjGamma0 N γ).strictPeriods) :
    ∃ (Φ : ℂ → (Fin r → ℂ)) (m : ℤ), (∀ i, AnalyticAt ℂ (fun q => Φ q i) 0) ∧ Φ 0 ≠ 0 ∧
      (∃ p : Place (AlgebraicClosure ℚ) (FB N), jB N ∉ p.toValuationSubring ∧
        ∃ c : ℂ, c ≠ 0 ∧ Φ 0 = c • (fun i => σ (evalVec s p i))) ∧
      ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ τ : ℍ, A₀ ≤ τ.im →
        Φ (Function.Periodic.qParam w (τ : ℂ)) =
          Function.Periodic.qParam w (τ : ℂ) ^ m • Φint σ s ((γ • τ : ℍ) : ℂ) := by
  obtain ⟨Φ, m, hA, h0, hval, A₀, hA₀, h⟩ := cusp_strong σ s hs γ hw hΓ
  refine ⟨Φ, m, hA, h0, hval, A₀, hA₀, fun τ hτ => ?_⟩
  obtain ⟨hcont, hΦ⟩ := h τ hτ
  funext i
  rw [hΦ i, Pi.smul_apply, smul_eq_mul, Φint_eq_realize σ s (γ • τ) i (hcont i)]

def pencilAlg (s : Fin r → FB N) (v : Place (AlgebraicClosure ℚ) (FB N)) (p : Fin r)
    (e : Fin r → AlgebraicClosure ℚ) : Fin r → AlgebraicClosure ℚ :=
  fun i => e i - (∑ j, evalVec s v j * (evalVec s v p)⁻¹ * e j) * (if i = p then 1 else 0)

theorem sigma_pencilAlg (s : Fin r → FB N) (σ : AlgebraicClosure ℚ →+* ℂ) (v : Place (AlgebraicClosure ℚ) (FB N))
    (p : Fin r) (e : Fin r → AlgebraicClosure ℚ) (i : Fin r) :
    σ (pencilAlg s v p e i) = pencilCov (fun i => σ (evalVec s v i * (evalVec s v p)⁻¹)) p (fun i => σ (e i)) i := by
  classical
  simp only [pencilAlg, pencilCov, map_sub, map_mul, map_sum]
  congr 1
  split_ifs <;> simp

theorem phi_linSec (s : Fin r → FB N) (σ : AlgebraicClosure ℚ →+* ℂ) (a : Fin r → AlgebraicClosure ℚ) :
    phi N σ (linSec s a) = ∑ i, σ (a i) • phi N σ (s i) := by
  simp only [linSec, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, phi_algebraMap, Algebra.smul_def]

theorem simple_ell (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (t w : ℍ) (v : Place (AlgebraicClosure ℚ) (FB N))
    (hv : v.toValuationSubring = (D.pt w).toValuationSubring.comap (phi N σ))
    {F : ℂ → (Fin r → ℂ)}
    (hA : ∀ i, AnalyticOnNhd ℂ (fun u => F u i) (ball 0 1))
    (hORD0 : ∀ b : Fin r → ℂ, (∑ i, b i • phi N σ (s i)) ≠ 0 →
      analyticOrderAt (fun u => ∑ i, b i * F u i) 0 = ((((D.pt t).ord (∑ i, b i • phi N σ (s i))).toNat : ℕ) : ℕ∞))
    (hORD : ∀ b : Fin r → ℂ, (∑ i, b i • phi N σ (s i)) ≠ 0 → ∀ z : ℂ, ∀ hz : 0 < z.im, Cay.cay t z ≠ 0 →
      analyticOrderAt (fun u => ∑ i, b i * F u i) (Cay.cay t z ^ D.ramification t)
        = ((((D.ramification ⟨z, hz⟩ : ℤ) * (D.pt ⟨z, hz⟩).ord (∑ i, b i • phi N σ (s i))).toNat : ℕ) : ℕ∞))
    {zb : ℂ} (hzb : zb = Cay.cay t w ^ D.ramification t) (hzb1 : zb ∈ ball (0 : ℂ) 1)
    (p : Fin r) (hbp : F zb p ≠ 0)
    {xh : Fin r → ℂ} (hxh : xh = fun i => σ (evalVec s v i * (evalVec s v p)⁻¹)) (hxw : F zb = (F zb p) • xh)
    {ρ₁ L : ℝ} (hρ₁ : 0 < ρ₁) (hL : 0 ≤ L) {Ψb : ℂ → (Fin r × Fin r → ℂ)}
    (hId : ∀ z ∈ closedBall zb ρ₁, ∀ q : Fin r × Fin r, F zb q.1 * F z q.2 - F zb q.2 * F z q.1 = (z - zb) * Ψb z q)
    (hLip : ∀ z ∈ closedBall zb ρ₁, ∀ z' ∈ closedBall zb ρ₁, ‖Ψb z - Ψb z'‖ ≤ L * ‖z - z'‖)
    (e : Fin r → AlgebraicClosure ℚ) (ha0 : linSec s (pencilAlg s v p e) ≠ 0)
    (hgood : ∀ z ∈ closedBall zb ρ₁, ∑ i, σ (e i) * Ψb z (p, i) ≠ 0) :
    v.ord (linSec s (pencilAlg s v p e)) + embDivisor N v = 1 := by
  classical
  set a := pencilAlg s v p e with ha
  set b : Fin r → ℂ := fun i => σ (e i) with hb
  set f : FC N := ∑ i, σ (a i) • phi N σ (s i) with hf
  have hfeq : f = phi N σ (linSec s a) := by rw [hf, phi_linSec]
  have hf0 : f ≠ 0 := by rw [hfeq]; exact phi_ne_zero σ ha0

  have hFG : ∀ z ∈ closedBall zb ρ₁, (∑ i, σ (a i) * F z i) = (z - zb) * ((F zb p)⁻¹ * ∑ i, b i * Ψb z (p, i)) := by
    intro z hz
    have h1 : ∑ i, σ (a i) * F z i = ∑ i, F z i * pencilCov xh p b i :=
      Finset.sum_congr rfl fun i _ => by rw [ha, sigma_pencilAlg, ← hxh, mul_comm]
    rw [h1, pencilCov_chart, chord_eq_divided' (S := closedBall zb ρ₁) hId p hxw hbp b hz]
    ring
  have hFan : AnalyticAt ℂ (fun z => ∑ i, σ (a i) * F z i) zb := by
    have := Finset.univ.analyticAt_sum (c := zb) (f := fun i => fun z => σ (a i) * F z i)
      (fun i _ => analyticAt_const.mul (hA i zb hzb1))
    exact this.congr (Filter.Eventually.of_forall fun z => by simp [Finset.sum_apply])
  have hGc : ContinuousAt (fun z => (F zb p)⁻¹ * ∑ i, b i * Ψb z (p, i)) zb := by
    have hΨc : ContinuousAt Ψb zb := by
      refine Metric.continuousAt_iff.2 fun ε hε => ⟨min ρ₁ (ε / (L + 1)), by positivity, fun z hz => ?_⟩
      have hz1 : z ∈ closedBall zb ρ₁ := mem_closedBall.2 (hz.le.trans (min_le_left _ _))
      rw [dist_eq_norm]
      have h := hLip z hz1 zb (mem_closedBall_self hρ₁.le)
      have hd : ‖z - zb‖ < ε / (L + 1) := by
        have := hz; rw [dist_eq_norm] at this; exact this.trans_le (min_le_right _ _)
      calc ‖Ψb z - Ψb zb‖ ≤ L * ‖z - zb‖ := h
        _ ≤ (L + 1) * ‖z - zb‖ := by nlinarith [norm_nonneg (z - zb)]
        _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left hd (by linarith)
        _ = ε := mul_div_cancel₀ _ (by linarith)
    refine continuousAt_const.mul ?_
    exact tendsto_finset_sum _ fun i _ => (continuousAt_const.mul ((continuousAt_apply (p, i) _).comp hΨc)).tendsto
  have hG0 : (F zb p)⁻¹ * ∑ i, b i * Ψb zb (p, i) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hbp) (hgood zb (mem_closedBall_self hρ₁.le))
  have h1 : analyticOrderAt (fun z => ∑ i, σ (a i) * F z i) zb = 1 :=
    analyticOrderAt_eq_one_of_divided hρ₁ hFan hFG hGc hG0
  have hbcoef : (∑ i, σ (a i) • phi N σ (s i)) ≠ 0 := by rw [← hf]; exact hf0
  have hfmem : f ∈ (D.pt w).toValuationSubring := by rw [hf]; exact ATLINT.linComb_mem D σ s hs _ w
  have hord0 : 0 ≤ (D.pt w).ord f := (D.pt w).ord_nonneg_of_mem hfmem
  have hram : 0 < D.ramification w := D.ramification_pos w

  have hordw : (D.pt w).ord f = 1 := by
    by_cases hc : Cay.cay t (w : ℂ) = 0
    ·
      have hwt : w = t := by
        apply UpperHalfPlane.ext
        have hden := Cay.sub_conj_ne_zero t (le_of_lt w.im_pos)
        simp only [Cay.cay, div_eq_zero_iff] at hc
        rcases hc with hc | hc
        · exact sub_eq_zero.1 hc
        · exact absurd hc hden
      subst hwt
      have h0 : zb = 0 := by rw [hzb, hc, zero_pow (D.ramification_pos _).ne']
      have h2 := hORD0 (fun i => σ (a i)) hbcoef
      rw [← h0, h1] at h2
      have h3 : ((D.pt w).ord f).toNat = 1 := by
        rw [hf]; exact_mod_cast h2.symm
      have := Int.toNat_of_nonneg hord0
      omega
    · have h2 := hORD (fun i => σ (a i)) hbcoef (w : ℂ) w.im_pos hc
      have hw' : (⟨(w : ℂ), w.im_pos⟩ : ℍ) = w := rfl
      rw [hw', ← hzb, h1] at h2
      have h3 : ((D.ramification w : ℤ) * (D.pt w).ord f).toNat = 1 := by
        rw [hf]; exact_mod_cast h2.symm
      have hprod_nn : 0 ≤ (D.ramification w : ℤ) * (D.pt w).ord f := by positivity
      have hprod : (D.ramification w : ℤ) * (D.pt w).ord f = 1 := by
        have := Int.toNat_of_nonneg hprod_nn; omega
      exact Int.eq_one_of_mul_eq_one_left hord0 hprod
  rw [PLB.embDivisor_eq_zero_of_comap D σ v w hv, add_zero, ← CUSPATLAS.ord_eq_of_comap_eq σ v (D.pt w) hv,
    ← hfeq, hordw]

theorem pencil_chord_ne_zero (s : Fin r → FB N) (hs : IsEmbBasis N s) (σ : AlgebraicClosure ℚ →+* ℂ)
    (v w : Place (AlgebraicClosure ℚ) (FB N)) (hwv : w ≠ v) (p : Fin r) (hp : evalVec s v p ≠ 0) :
    (fun i => σ (evalVec s w i) - σ (evalVec s w p) * σ (evalVec s v i * (evalVec s v p)⁻¹)) ≠ 0 := by
  intro h0
  apply ModularCurve.JZero.chordVec_ne_zero_of_ne N s hs v w (Ne.symm hwv)
  have hc : ∀ i, evalVec s w i = evalVec s w p * (evalVec s v i * (evalVec s v p)⁻¹) := by
    intro i
    have := congrFun h0 i
    simp only [Pi.zero_apply, sub_eq_zero] at this
    apply σ.injective
    simpa only [map_mul, map_inv₀] using this
  funext q
  simp only [chordVec, Pi.zero_apply]
  rw [hc q.1, hc q.2]
  field_simp
  ring

theorem loc_pkg (D : ComplexPlaceDictionary N) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (σ₀ : AlgebraicClosure ℚ →+* ℂ) (Bx₀ y₀₀ Y₁₀ : ℝ) (hy₀₀ : 0 < y₀₀)
    (hbdd : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) (k : ℕ) (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      BddAbove (Set.range fun τ : PLB.Gen D σ u => PLB.psiU D σ s k u τ))
    (hbox : ∀ (Bx yl yu : ℝ), 0 < yl → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) → ∀ lam : ℝ, 0 < lam →
        MeasureTheory.volume {z : ℂ | |z.re| ≤ Bx ∧ yl ≤ z.im ∧ z.im ≤ yu ∧
            ‖ATLINT.ext (N := N) (phi N σ u) z‖
              ≤ Real.exp (PLB.supPsi D σ s k u - lam) * (⨆ i, ‖Φint σ s z i‖) ^ k}
          ≤ ENNReal.ofReal (C * (k + 1) / lam))
    (hcusp : ∀ (γ : SL(2, ℤ)) (h : ℝ), 0 < h → h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods →
      ∀ R : ℝ, 0 < R → R < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) → ∀ lam : ℝ, 0 < lam →
        MeasureTheory.volume {q : ℂ | q ∈ Metric.ball (0 : ℂ) R ∧ q ≠ 0 ∧
            ‖ATLINT.ext (N := N) (phi N σ u)
                ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℍ) : ℂ)‖
              ≤ Real.exp (PLB.supPsi D σ s k u - lam)
                * (⨆ i, ‖Φint σ s ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℍ) : ℂ) i‖) ^ k}
          ≤ ENNReal.ofReal (C * (k + 1) / lam)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (ρ ρ' R : ι → ℝ) (Φ : ι → ℂ → (Fin r → ℂ)) (lift : ι → ℂ → ℍ)
      (Dom : ι → Set ℂ) (Cvol : ℝ)
      (κs : Type) (_ : Fintype κs) (Zs : κs → Set ℂ) (Λs : κs → ℂ → ℍ) (Vs : κs → ℂ → (Fin r → ℂ)) (etain : ℝ),
      (∀ j, 0 < ρ j) ∧ (∀ j, ρ j < ρ' j) ∧ (∀ j, ρ' j < R j) ∧
      (∀ j i, AnalyticOnNhd ℂ (fun z => Φ j z i) (ball (c j) (R j))) ∧
      (∀ j i, ∃ Lji, LipschitzOnWith Lji (fun z => Φ j z i) (closedBall (c j) (ρ' j))) ∧
      (∀ j, ∀ z ∈ ball (c j) (R j), Φ j z ≠ 0) ∧ 0 ≤ Cvol ∧

      (∀ k, IsCompact (Zs k)) ∧ (∀ k, ContinuousOn (fun z => ((Λs k z : ℍ) : ℂ)) (Zs k)) ∧
      (∀ k, ContinuousOn (Vs k) (Zs k)) ∧ (∀ k, ∀ z ∈ Zs k, Vs k z ≠ 0) ∧
      (∀ k, ∀ z ∈ Zs k, ∃ t : ℂ, t ≠ 0 ∧ Vs k z = t • Φint σ₀ s ((Λs k z : ℍ) : ℂ)) ∧ 0 < etain ∧
      (∀ j, ∀ z ∈ closedBall (c j) (ρ j), z ∈ Dom j →
        (∃ k, ∃ z' ∈ Zs k, Vs k z' = Φ j z ∧ D.pt (Λs k z') = D.pt (lift j z)) ∨
        (∀ w : ℂ, |w.re| ≤ Bx₀ → y₀₀ ≤ w.im → w.im ≤ Y₁₀ → ∀ hw : 0 < w.im,
          etain ≤ pchd (Φ j z) (Φint σ₀ s w))) ∧
      ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →

        (∀ j, ∀ z ∈ closedBall (c j) (ρ j), z ∈ Dom j → ∃ t : ℂ, t ≠ 0 ∧ Φ j z = t • Φint σ s ((lift j z : ℍ) : ℂ)) ∧

        (∀ τ : ℍ, ∃ j z, z ∈ closedBall (c j) (ρ j) ∧ z ∈ Dom j ∧ (∃ t : ℂ, t ≠ 0 ∧ Φ j z = t • Φint σ s (τ : ℂ)) ∧
          D.pt (lift j z) = D.pt τ) ∧

        (∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
          ∀ lam : ℝ, 0 < lam → ∀ (xh : Fin r → ℂ), xh ≠ 0 → ∀ eta : ℝ, 0 < eta →
          ∀ j, ∃ K : Set ℂ, IsClosed K ∧ K ⊆ closedBall (c j) (ρ j) ∧ (∀ z ∈ K, eta ≤ pchd (Φ j z) xh) ∧
            volume K ≤ ENNReal.ofReal (Cvol * (k + 1) / lam) ∧
            (∀ z ∈ closedBall (c j) (ρ j), z ∈ Dom j → z ∉ K → eta ≤ pchd (Φ j z) xh →
              PLB.supPsi D σ s k u - lam < PLB.psiU D σ s k u (lift j z))) := by
  classical
  have hr := r_pos N s hs
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩

  obtain ⟨S₀, hS₀⟩ := exists_coset_reps (N := N)
  have hwN : (0 : ℝ) < N := natCast_pos_of_neZero N
  have hΓN : ∀ g : SL(2, ℤ), (N : ℝ) ∈ (conjGamma0 N g).strictPeriods := fun g =>
    natCast_mem_strictPeriods_conjGamma0 N g
  choose Φc mc hΦcA hΦc0 hΦcVal Ac hAc hΦcV using fun g : SL(2, ℤ) => cusp_strong_Φint σ₀ s hs g hwN (hΓN g)

  have hball : ∀ g, ∃ Rg : ℝ, 0 < Rg ∧ Rg < 1 ∧ (∀ i, AnalyticOnNhd ℂ (fun q => Φc g q i) (ball 0 Rg)) ∧
      ∀ q ∈ ball (0 : ℂ) Rg, Φc g q ≠ 0 := by
    intro g
    have h1 : ∀ᶠ q in 𝓝 (0 : ℂ), ∀ i, AnalyticAt ℂ (fun q => Φc g q i) q :=
      Filter.eventually_all.2 fun i => (hΦcA g i).eventually_analyticAt
    have hc : ContinuousAt (Φc g) 0 := continuousAt_pi.2 fun i => (hΦcA g i).continuousAt
    have h2 : ∀ᶠ q in 𝓝 (0 : ℂ), Φc g q ≠ 0 := hc.eventually_ne (hΦc0 g)
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
    refine ⟨min ε (1/2), by positivity, by linarith [min_le_right ε (1/2)], fun i q hq => ?_, fun q hq => ?_⟩
    · exact (hεb q (ball_subset_ball (min_le_left _ _) hq)).1 i
    · exact (hεb q (ball_subset_ball (min_le_left _ _) hq)).2
  choose Rg hRg hRg1 hRgA hRgZ using hball

  set rc : SL(2, ℤ) → ℝ := fun g => min (Rg g / 8) (Real.exp (-2 * Real.pi * Ac g / N)) with hrc
  have hrcpos : ∀ g, 0 < rc g := fun g => lt_min (by linarith [hRg g]) (Real.exp_pos _)
  have hrcle : ∀ g, rc g ≤ Rg g / 8 := fun g => min_le_left _ _

  have hlift_im : ∀ g (q : ℂ), q ≠ 0 → ‖q‖ ≤ rc g → Ac g ≤ (Function.Periodic.invQParam (N : ℝ) q).im := by
    intro g q hq0 hq
    rw [Function.Periodic.im_invQParam]
    have hle : ‖q‖ ≤ Real.exp (-2 * Real.pi * Ac g / N) := hq.trans (min_le_right _ _)
    have hlog : Real.log ‖q‖ ≤ -2 * Real.pi * Ac g / N := by
      have := Real.log_le_log (norm_pos_iff.2 hq0) hle
      rwa [Real.log_exp] at this
    rw [show -N / (2 * Real.pi) * Real.log ‖q‖ = (-Real.log ‖q‖) * N / (2 * Real.pi) by ring,
      le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hwN] at hlog
    nlinarith [Real.pi_pos]
  choose A₁ hA₁ using fun g : SL(2, ℤ) => norm_qParam_le_of_le_im hwN (half_pos (hrcpos g))
  set Y : ℝ := (∑ g ∈ S₀, (|Ac g| + |A₁ g|)) + 1 with hY
  have hYg : ∀ g ∈ S₀, Ac g ≤ Y ∧ A₁ g ≤ Y := by
    intro g hg
    have h1 : |Ac g| + |A₁ g| ≤ ∑ g ∈ S₀, (|Ac g| + |A₁ g|) :=
      Finset.single_le_sum (f := fun g => |Ac g| + |A₁ g|) (fun _ _ => by positivity) hg
    constructor <;> linarith [le_abs_self (Ac g), le_abs_self (A₁ g), abs_nonneg (Ac g), abs_nonneg (A₁ g)]

  obtain ⟨S, Bx, y₀, Y₁, hy₀, hcov⟩ := ModularGroup.exists_finset_box_or_cusp (CongruenceSubgroup.Gamma0 N) Y
  have hKc : IsCompact {z : ℂ | |z.re| ≤ Bx ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁} := isCompact_box' Bx y₀ Y₁
  have hKim : ∀ z ∈ {z : ℂ | |z.re| ≤ Bx ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁}, 0 < z.im := fun z hz => hy₀.trans_le hz.2.1
  obtain ⟨T, hTim, hTcov, hTK⟩ := exists_finset_cover hKc hKim
  have hTbox : ∀ t ∈ T, |t.re| ≤ Bx ∧ y₀ ≤ t.im ∧ t.im ≤ Y₁ := fun t ht => hTK t ht

  obtain ⟨Cb, hCb0, hCb⟩ := hbox (Bx + Y₁) (y₀ / 2) (2 * Y₁) (by positivity)
  choose Cg hCg0 hCg using fun g : SL(2, ℤ) => hcusp g N hwN (hΓN g) (Rg g) (hRg g) (hRg1 g)
  set Cvol : ℝ := Cb + ∑ g ∈ S₀, Cg g with hCvol
  have hCvol0 : 0 ≤ Cvol := by
    have : 0 ≤ ∑ g ∈ S₀, Cg g := Finset.sum_nonneg fun g _ => hCg0 g
    rw [hCvol]; linarith
  have hCble : Cb ≤ Cvol := by
    have : 0 ≤ ∑ g ∈ S₀, Cg g := Finset.sum_nonneg fun g _ => hCg0 g
    rw [hCvol]; linarith
  have hCgle : ∀ g ∈ S₀, Cg g ≤ Cvol := fun g hg => by
    rw [hCvol]
    linarith [Finset.single_le_sum (f := Cg) (fun g _ => hCg0 g) hg]

  set Kbb : Set ℂ := {w : ℂ | |w.re| ≤ Bx₀ ∧ y₀₀ ≤ w.im ∧ w.im ≤ Y₁₀} with hKbb
  have hKbbc : IsCompact Kbb := isCompact_box' Bx₀ y₀₀ Y₁₀
  have hKbbim : ∀ w ∈ Kbb, 0 < w.im := fun w hw => hy₀₀.trans_le hw.2.1
  have hΦint_cont : ContinuousOn (Φint σ₀ s) {z : ℂ | 0 < z.im} := by
    intro z hz
    have hA := (interior_chart' D σ₀ s hs z hz).1
    have hz' : 0 < z.im := hz
    exact (continuousOn_pi.2 fun i => (hA i).continuousOn).continuousAt (ball_mem_nhds z (by linarith)) |>.continuousWithinAt
  have hΦint_ne : ∀ z : ℂ, 0 < z.im → Φint σ₀ s z ≠ 0 := fun z hz =>
    (interior_chart' D σ₀ s hs z hz).2.1 z (mem_ball_self (by linarith))

  have hinner : ∀ g, ∃ ρin mg : ℝ, 0 < ρin ∧ ρin ≤ rc g ∧ 0 < mg ∧
      ∀ q ∈ closedBall (0 : ℂ) (rc g), ‖q‖ < ρin → ∀ w ∈ Kbb, mg ≤ pchd (Φc g q) (Φint σ₀ s w) := by
    intro g
    have hΦcc : ContinuousOn (Φc g) (closedBall 0 (rc g)) :=
      continuousOn_pi.2 fun i => (hRgA g i).continuousOn.mono (closedBall_subset_ball (by linarith [hrcle g, hRg g]))
    have hP : ContinuousOn (fun x : ℂ × ℂ => pchd (Φc g x.1) (Φint σ₀ s x.2)) (closedBall (0:ℂ) (rc g) ×ˢ Kbb) := by
      unfold pchd
      refine ContinuousOn.div ?_ ?_ fun x hx => ?_
      · refine ContinuousOn.norm (continuousOn_pi.2 fun q => ?_)
        simp only [wedge]
        exact (((continuousOn_pi.1 hΦcc q.1).comp continuousOn_fst fun x hx => hx.1).mul
            ((continuousOn_pi.1 hΦint_cont q.2).comp continuousOn_snd fun x hx => hKbbim _ hx.2)).sub
          (((continuousOn_pi.1 hΦcc q.2).comp continuousOn_fst fun x hx => hx.1).mul
            ((continuousOn_pi.1 hΦint_cont q.1).comp continuousOn_snd fun x hx => hKbbim _ hx.2))
      · exact (hΦcc.comp continuousOn_fst fun x hx => hx.1).norm.mul
          ((hΦint_cont.comp continuousOn_snd fun x hx => hKbbim _ hx.2).norm)
      · exact mul_ne_zero (norm_ne_zero_iff.2 (hRgZ g _ (closedBall_subset_ball (by linarith [hrcle g, hRg g]) hx.1)))
          (norm_ne_zero_iff.2 (hΦint_ne _ (hKbbim _ hx.2)))

    have hpos0 : ∀ w ∈ Kbb, 0 < pchd (Φc g 0) (Φint σ₀ s w) := by
      intro w hw
      refine pchd_pos_of_not_prop (hΦc0 g) (hΦint_ne w (hKbbim w hw)) ?_
      rintro ⟨c₀, hc₀, hprop⟩
      obtain ⟨p, hpc, c₁, hc₁, hval⟩ := hΦcVal g
      apply PLBSEP.interior_ne_cusp_value D σ₀ s hs ⟨w, hKbbim w hw⟩ p hpc
      refine ⟨c₀⁻¹ * c₁, mul_ne_zero (inv_ne_zero hc₀) hc₁, ?_⟩
      show Φint σ₀ s w = (c₀⁻¹ * c₁) • (fun i => σ₀ (evalVec s p i))
      rw [mul_smul, ← hval, hprop, smul_smul, inv_mul_cancel₀ hc₀, one_smul]
    rcases Kbb.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨rc g, 1, hrcpos g, le_rfl, one_pos, fun q _ _ w hw => ?_⟩
      rw [hKe] at hw; exact hw.elim
    obtain ⟨w₀, hw₀, hmin⟩ := hKbbc.exists_isMinOn hKne
      ((hP.comp (continuousOn_const.prodMk continuousOn_id) fun w hw => ⟨mem_closedBall_self (hrcpos g).le, hw⟩))
    set mg : ℝ := pchd (Φc g 0) (Φint σ₀ s w₀) / 2 with hmg
    have hmgpos : 0 < mg := by rw [hmg]; exact half_pos (hpos0 w₀ hw₀)
    have hcpt : IsCompact (closedBall (0:ℂ) (rc g) ×ˢ Kbb) := (isCompact_closedBall _ _).prod hKbbc
    have huc := hcpt.uniformContinuousOn_of_continuous hP
    obtain ⟨δ, hδ, hδP⟩ := Metric.uniformContinuousOn_iff.1 huc mg hmgpos
    refine ⟨min δ (rc g), mg, lt_min hδ (hrcpos g), min_le_right _ _, hmgpos, fun q hq hqn w hw => ?_⟩
    have hd : dist (q, w) ((0:ℂ), w) < δ := by
      rw [Prod.dist_eq, dist_self, dist_zero_right]
      simp only [max_lt_iff]
      exact ⟨hqn.trans_le (min_le_left _ _), hδ⟩
    have h1 := hδP (q, w) ⟨hq, hw⟩ ((0:ℂ), w) ⟨mem_closedBall_self (hrcpos g).le, hw⟩ hd
    rw [Real.dist_eq] at h1
    have h2 : 2 * mg ≤ pchd (Φc g 0) (Φint σ₀ s w) := by
      have h0 : pchd (Φc g 0) (Φint σ₀ s w₀) ≤ pchd (Φc g 0) (Φint σ₀ s w) := by
        have := hmin hw; simpa [Function.comp] using this
      rw [hmg]; linarith
    have := (abs_lt.1 h1).1
    linarith
  choose ρin mg hρin hρinle hmgpos hinner' using hinner
  set etain : ℝ := (∑ g ∈ S₀, (mg g)⁻¹ + 1)⁻¹ with hetain
  have hetainpos : 0 < etain := by
    rw [hetain]; exact inv_pos.2 (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun g _ => (inv_pos.2 (hmgpos g)).le) one_pos)
  have hetainle : ∀ g ∈ S₀, etain ≤ mg g := by
    intro g hg
    rw [hetain, ← inv_inv (mg g)]
    refine inv_anti₀ (inv_pos.2 (hmgpos g)) ?_
    have : (mg g)⁻¹ ≤ ∑ g ∈ S₀, (mg g)⁻¹ :=
      Finset.single_le_sum (f := fun g => (mg g)⁻¹) (fun g _ => (inv_pos.2 (hmgpos g)).le) hg
    linarith

  set Ylo : SL(2, ℤ) → ℝ := fun g => -(N : ℝ) * Real.log (rc g) / (2 * Real.pi) with hYlo
  set Yhi : SL(2, ℤ) → ℝ := fun g => -(N : ℝ) * Real.log (ρin g) / (2 * Real.pi) with hYhi
  have hYloA : ∀ g, Ac g ≤ Ylo g := by
    intro g
    have h := hlift_im g (rc g) (by exact_mod_cast (hrcpos g).ne') (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hrcpos g)])
    rw [Function.Periodic.im_invQParam, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hrcpos g)] at h
    rw [hYlo]; convert h using 1; ring
  have hYlopos : ∀ g, 0 < Ylo g := fun g => (hAc g).trans_le (hYloA g)

  refine ⟨{t // t ∈ T} ⊕ {g // g ∈ S₀}, inferInstance,
    Sum.elim (fun t => t.1) (fun _ => 0),
    Sum.elim (fun t => t.1.im / 16) (fun g => rc g.1),
    Sum.elim (fun t => t.1.im / 8) (fun g => Rg g.1 / 4),
    Sum.elim (fun t => t.1.im / 2) (fun g => Rg g.1),
    Sum.elim (fun _ => Φint σ₀ s) (fun g => Φc g.1),
    Sum.elim (fun _ z => UpperHalfPlane.ofComplex z)
      (fun g q => ((g.1 • UpperHalfPlane.ofComplex (Function.Periodic.invQParam (N : ℝ) q) : ℍ))),
    Sum.elim (fun _ => {z : ℂ | 0 < z.im}) (fun _ => {q : ℂ | q ≠ 0}),
    Cvol,
    {t // t ∈ T} ⊕ {g // g ∈ S₀}, inferInstance,
    Sum.elim (fun t => closedBall t.1 (t.1.im / 16))
      (fun g => {z : ℂ | 0 ≤ z.re ∧ z.re ≤ N ∧ Ylo g.1 ≤ z.im ∧ z.im ≤ Yhi g.1}),
    Sum.elim (fun _ z => UpperHalfPlane.ofComplex z) (fun g z => ((g.1 • UpperHalfPlane.ofComplex z : ℍ))),
    Sum.elim (fun _ => Φint σ₀ s) (fun g z => Φc g.1 (Function.Periodic.qParam (N : ℝ) z)),
    etain, ?_, ?_, ?_, ?_, ?_, ?_, hCvol0, ?_, ?_, ?_, ?_, ?_, hetainpos, ?_, ?_⟩
  · rintro (⟨t, ht⟩ | ⟨g, hg⟩)
    · show 0 < t.im / 16; linarith [hTim t ht]
    · exact hrcpos g
  · rintro (⟨t, ht⟩ | ⟨g, hg⟩)
    · show t.im / 16 < t.im / 8; linarith [hTim t ht]
    · show rc g < Rg g / 4; linarith [hrcle g, hRg g]
  · rintro (⟨t, ht⟩ | ⟨g, hg⟩)
    · show t.im / 8 < t.im / 2; linarith [hTim t ht]
    · show Rg g / 4 < Rg g; linarith [hRg g]
  · rintro (⟨t, ht⟩ | ⟨g, hg⟩) i
    · exact (interior_chart' D σ₀ s hs t (hTim t ht)).1 i
    · exact hRgA g i
  · rintro (⟨t, ht⟩ | ⟨g, hg⟩) i
    · exact (interior_chart' D σ₀ s hs t (hTim t ht)).2.2.2 i (t.im / 8) (show t.im / 8 < t.im / 2 by linarith [hTim t ht])
    · exact lipschitzOn_of_analyticOnNhd (hRgA g i) (show Rg g / 4 < Rg g by linarith [hRg g])
  · rintro (⟨t, ht⟩ | ⟨g, hg⟩) z hz
    · exact (interior_chart' D σ₀ s hs t (hTim t ht)).2.1 z hz
    · exact hRgZ g z hz

  · rintro (⟨t, ht⟩ | ⟨g, hg⟩)
    · exact isCompact_closedBall _ _
    · show IsCompact {z : ℂ | 0 ≤ z.re ∧ z.re ≤ N ∧ Ylo g ≤ z.im ∧ z.im ≤ Yhi g}
      have : {z : ℂ | 0 ≤ z.re ∧ z.re ≤ N ∧ Ylo g ≤ z.im ∧ z.im ≤ Yhi g} = (Set.Icc 0 (N:ℝ)) ×ℂ (Set.Icc (Ylo g) (Yhi g)) := by
        ext z; simp only [Set.mem_setOf_eq, Complex.mem_reProdIm, Set.mem_Icc]; tauto
      rw [this]; exact isCompact_Icc.reProdIm isCompact_Icc
  · rintro (⟨t, ht⟩ | ⟨g, hg⟩)
    · intro z hz
      have hzim : 0 < z.im := by
        have h1 : |z.im - t.im| ≤ t.im / 16 := by
          have := mem_closedBall.1 hz; rw [dist_eq_norm] at this
          exact (Complex.abs_im_le_norm (z - t)).trans (by simpa using this)
        have := (abs_le.1 h1).1; linarith [hTim t ht]
      show ContinuousWithinAt (fun z => ((UpperHalfPlane.ofComplex z : ℍ) : ℂ)) _ z
      refine ContinuousAt.continuousWithinAt ?_
      have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
      exact (continuousAt_id.congr (by
        filter_upwards [hopen.mem_nhds hzim] with y hy
        exact (UpperHalfPlane.ofComplex_apply_of_im_pos hy).symm ▸ rfl))
    · intro z hz
      show ContinuousWithinAt (fun z => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)) _ z
      exact (differentiableAt_coe_smul_ofComplex g ((hYlopos g).trans_le hz.2.2.1)).continuousAt.continuousWithinAt
  · rintro (⟨t, ht⟩ | ⟨g, hg⟩)
    · show ContinuousOn (Φint σ₀ s) (closedBall t (t.im / 16))
      have hA := (interior_chart' D σ₀ s hs t (hTim t ht)).1
      exact continuousOn_pi.2 fun i => (hA i).continuousOn.mono (closedBall_subset_ball (by linarith [hTim t ht]))
    · show ContinuousOn (fun z => Φc g (Function.Periodic.qParam (N : ℝ) z)) _
      have hΦcc : ContinuousOn (Φc g) (ball 0 (Rg g)) := continuousOn_pi.2 fun i => (hRgA g i).continuousOn
      refine hΦcc.comp (Function.Periodic.differentiable_qParam.continuous.continuousOn) fun z hz => ?_
      rw [mem_ball, dist_zero_right, Function.Periodic.norm_qParam]
      have h1 : Real.exp (-2 * Real.pi * z.im / N) ≤ rc g := by
        have hz3 : Ylo g ≤ z.im := hz.2.2.1
        rw [hYlo] at hz3
        rw [← Real.exp_log (hrcpos g)]
        apply Real.exp_le_exp.2
        rw [div_le_iff₀ hwN]
        rw [div_le_iff₀ (by positivity)] at hz3
        nlinarith [Real.pi_pos]
      linarith [hrcle g, hRg g]
  · rintro (⟨t, ht⟩ | ⟨g, hg⟩) z hz
    · exact (interior_chart' D σ₀ s hs t (hTim t ht)).2.1 z (closedBall_subset_ball (by linarith [hTim t ht]) hz)
    · show Φc g (Function.Periodic.qParam (N : ℝ) z) ≠ 0
      refine hRgZ g _ ?_
      rw [mem_ball, dist_zero_right, Function.Periodic.norm_qParam]
      have h1 : Real.exp (-2 * Real.pi * z.im / N) ≤ rc g := by
        have hz3 : Ylo g ≤ z.im := hz.2.2.1
        rw [hYlo] at hz3
        rw [← Real.exp_log (hrcpos g)]
        apply Real.exp_le_exp.2
        rw [div_le_iff₀ hwN]
        rw [div_le_iff₀ (by positivity)] at hz3
        nlinarith [Real.pi_pos]
      linarith [hrcle g, hRg g]
  · rintro (⟨t, ht⟩ | ⟨g, hg⟩) z hz
    · refine ⟨1, one_ne_zero, ?_⟩
      have hzim : 0 < z.im := by
        have h1 : |z.im - t.im| ≤ t.im / 16 := by
          have := mem_closedBall.1 hz; rw [dist_eq_norm] at this
          exact (Complex.abs_im_le_norm (z - t)).trans (by simpa using this)
        have := (abs_le.1 h1).1; linarith [hTim t ht]
      show Φint σ₀ s z = (1:ℂ) • Φint σ₀ s ((UpperHalfPlane.ofComplex z : ℍ) : ℂ)
      rw [one_smul, UpperHalfPlane.ofComplex_apply_of_im_pos hzim]
    · have hzim : Ac g ≤ (UpperHalfPlane.ofComplex z).im := by
        have hz0 : 0 < z.im := (hYlopos g).trans_le hz.2.2.1
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz0]; exact (hYloA g).trans hz.2.2.1
      have hz0 : 0 < z.im := (hYlopos g).trans_le hz.2.2.1
      have hq0 : Function.Periodic.qParam (N : ℝ) z ≠ 0 := by
        first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]
      refine ⟨Function.Periodic.qParam (N : ℝ) z ^ mc g, zpow_ne_zero _ hq0, ?_⟩
      show Φc g (Function.Periodic.qParam (N : ℝ) z) =
        Function.Periodic.qParam (N : ℝ) z ^ mc g • Φint σ₀ s ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
      have := hΦcV g (UpperHalfPlane.ofComplex z) hzim
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz0] at this
      rw [this, UpperHalfPlane.ofComplex_apply_of_im_pos hz0]
  ·
    rintro (⟨t, ht⟩ | ⟨g, hg⟩) z hz hzD
    · left
      refine ⟨Sum.inl ⟨t, ht⟩, z, hz, rfl, rfl⟩
    · have hz0 : z ≠ 0 := hzD
      have hzn : ‖z‖ ≤ rc g := by simpa [mem_closedBall, dist_zero_right] using hz
      by_cases hin : ‖z‖ < ρin g
      · right
        intro w hw1 hw2 hw3 hw
        exact (hetainle g hg).trans (hinner' g z hz hin w ⟨hw1, hw2, hw3⟩)
      · left
        set z₀ : ℂ := Function.Periodic.invQParam (N : ℝ) z with hz₀
        set n : ℤ := -⌊z₀.re / N⌋ with hn
        set z' : ℂ := z₀ + n * ((N : ℝ) : ℂ) with hz'
        have him₀ : Ac g ≤ z₀.im := hlift_im g z hz0 hzn
        have hpos₀ : 0 < z₀.im := (hAc g).trans_le him₀
        have hre : 0 ≤ z'.re ∧ z'.re ≤ N := by
          have h1 := Int.floor_le (z₀.re / N)
          have h2 := Int.lt_floor_add_one (z₀.re / N)
          have e1 : z'.re = z₀.re + (n : ℝ) * N := by simp [z']
          rw [le_div_iff₀ hwN] at h1
          rw [div_lt_iff₀ hwN] at h2
          have e2 : (n : ℝ) = -(⌊z₀.re / N⌋ : ℝ) := by simp [n]
          rw [e1, e2]
          constructor <;> nlinarith
        have him' : z'.im = z₀.im := by simp [z']
        have hmem : z' ∈ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ N ∧ Ylo g ≤ z.im ∧ z.im ≤ Yhi g} := by
          refine ⟨hre.1, hre.2, ?_, ?_⟩
          · rw [him', hz₀, Function.Periodic.im_invQParam]
            show -(N : ℝ) * Real.log (rc g) / (2 * Real.pi) ≤ -(N : ℝ) / (2 * Real.pi) * Real.log ‖z‖
            have := Real.log_le_log (norm_pos_iff.2 hz0) hzn
            have hc : 0 ≤ (N : ℝ) / (2 * Real.pi) := by positivity
            have key := mul_le_mul_of_nonneg_left this hc
            have e1 : -(N : ℝ) * Real.log (rc g) / (2 * Real.pi) = -((N : ℝ) / (2 * Real.pi) * Real.log (rc g)) := by ring
            have e2 : -(N : ℝ) / (2 * Real.pi) * Real.log ‖z‖ = -((N : ℝ) / (2 * Real.pi) * Real.log ‖z‖) := by ring
            rw [e1, e2]; linarith
          · rw [him', hz₀, Function.Periodic.im_invQParam]
            show -(N : ℝ) / (2 * Real.pi) * Real.log ‖z‖ ≤ -(N : ℝ) * Real.log (ρin g) / (2 * Real.pi)
            have := Real.log_le_log (hρin g) (not_lt.1 hin)
            have hc : 0 ≤ (N : ℝ) / (2 * Real.pi) := by positivity
            have key := mul_le_mul_of_nonneg_left this hc
            have e1 : -(N : ℝ) * Real.log (ρin g) / (2 * Real.pi) = -((N : ℝ) / (2 * Real.pi) * Real.log (ρin g)) := by ring
            have e2 : -(N : ℝ) / (2 * Real.pi) * Real.log ‖z‖ = -((N : ℝ) / (2 * Real.pi) * Real.log ‖z‖) := by ring
            rw [e1, e2]; linarith
        refine ⟨Sum.inr ⟨g, hg⟩, z', hmem, ?_, ?_⟩
        · show Φc g (Function.Periodic.qParam (N : ℝ) z') = Φc g z
          rw [hz', qParam_add_int_mul' (N : ℝ) hwN.ne', hz₀, Function.Periodic.qParam_right_inv hwN.ne' hz0]
        · show D.pt (g • UpperHalfPlane.ofComplex z') = D.pt (g • UpperHalfPlane.ofComplex (Function.Periodic.invQParam (N : ℝ) z))
          rw [hz', ofComplex_add_int_mul_nat_eq z₀ hpos₀ n N, ← mul_smul,
            show g * ModularGroup.T ^ (n * (N : ℤ)) = (g * ModularGroup.T ^ (n * (N : ℤ)) * g⁻¹) * g by group,
            mul_smul, D.pt_smul ⟨_, conj_T_zpow_int_mul_mem N g n⟩]

  intro σ hσ
  have hΦ : Φint σ s = Φint σ₀ s := Φint_congr hσ
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro (⟨t, ht⟩ | ⟨g, hg⟩) z hz hzD
    · refine ⟨1, one_ne_zero, ?_⟩
      show Φint σ₀ s z = (1 : ℂ) • Φint σ s ((UpperHalfPlane.ofComplex z : ℍ) : ℂ)
      rw [one_smul, hΦ, UpperHalfPlane.ofComplex_apply_of_im_pos hzD]
    · have hz0 : z ≠ 0 := hzD
      have hzn : ‖z‖ ≤ rc g := by simpa [mem_closedBall, dist_zero_right] using hz
      have him := hlift_im g z hz0 hzn
      set τq : ℍ := UpperHalfPlane.ofComplex (Function.Periodic.invQParam (N : ℝ) z) with hτq
      have hτqim : Ac g ≤ τq.im := by
        have hpos : 0 < (Function.Periodic.invQParam (N : ℝ) z).im := (hAc g).trans_le him
        rw [hτq, UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
        exact him
      have hq : Function.Periodic.qParam (N : ℝ) (τq : ℂ) = z := by
        have hpos : 0 < (Function.Periodic.invQParam (N : ℝ) z).im := (hAc g).trans_le him
        rw [hτq, UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
        exact Function.Periodic.qParam_right_inv hwN.ne' hz0
      refine ⟨z ^ mc g, zpow_ne_zero _ hz0, ?_⟩
      show Φc g z = z ^ mc g • Φint σ s ((g • τq : ℍ) : ℂ)
      have := hΦcV g τq hτqim
      rw [hq] at this
      rw [this, hΦ]
  ·
    intro τ
    obtain ⟨γ, hγ, hcase⟩ := hcov τ
    have hinv : Φint σ s (((γ • τ : ℍ)) : ℂ) = Φint σ s (τ : ℂ) := Φint_smul D σ s hs ⟨γ, hγ⟩ τ
    rcases hcase with hbx | ⟨σ₁, hσ₁, zf, hzf, hYz, hγτ⟩
    · obtain ⟨t₀, ht₀, hmem⟩ := hTcov ((γ • τ : ℍ) : ℂ)
        (by first | simpa only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] using hbx | exact hbx)
      refine ⟨Sum.inl ⟨t₀, ht₀⟩, ((γ • τ : ℍ) : ℂ), hmem, (γ • τ).im_pos, ⟨1, one_ne_zero, ?_⟩, ?_⟩
      · show Φint σ₀ s ((γ • τ : ℍ) : ℂ) = (1 : ℂ) • Φint σ s (τ : ℂ)
        rw [one_smul, ← hΦ, hinv]
      · show D.pt (UpperHalfPlane.ofComplex ((γ • τ : ℍ) : ℂ)) = D.pt τ
        rw [UpperHalfPlane.ofComplex_apply, D.pt_smul ⟨γ, hγ⟩]
    · obtain ⟨γ', hγ', s₀, hs₀, hσ₁eq⟩ := hS₀ σ₁
      have hpt : (s₀ • zf : ℍ) = (γ'⁻¹ * γ) • τ := by
        rw [mul_smul, hγτ, hσ₁eq, mul_smul, inv_smul_smul]
      have hinv2 : Φint σ s (((s₀ • zf : ℍ)) : ℂ) = Φint σ s (τ : ℂ) := by
        rw [hpt]; exact Φint_smul D σ s hs ⟨γ'⁻¹ * γ, mul_mem (inv_mem hγ') hγ⟩ τ
      set q : ℂ := Function.Periodic.qParam (N : ℝ) (zf : ℂ) with hqdef
      have hq0 : q ≠ 0 := by
        rw [hqdef]; first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]
      have hYz' : Y ≤ zf.im := hYz.le
      have hqn : ‖q‖ ≤ rc s₀ / 2 := hA₁ s₀ zf (((hYg s₀ hs₀).2).trans hYz')
      have hqcore : q ∈ closedBall (0 : ℂ) (rc s₀) := by
        rw [mem_closedBall, dist_zero_right]; linarith [hrcpos s₀]
      have hΦq : Φc s₀ q = q ^ mc s₀ • Φint σ₀ s ((s₀ • zf : ℍ) : ℂ) :=
        hΦcV s₀ zf (((hYg s₀ hs₀).1).trans hYz')
      refine ⟨Sum.inr ⟨s₀, hs₀⟩, q, hqcore, hq0, ⟨q ^ mc s₀, zpow_ne_zero _ hq0, ?_⟩, ?_⟩
      · show Φc s₀ q = q ^ mc s₀ • Φint σ s (τ : ℂ)
        rw [hΦq, ← hΦ, hinv2]
      ·
        show D.pt (s₀ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam (N : ℝ) q)) = D.pt τ
        obtain ⟨m, hm⟩ := Function.Periodic.qParam_left_inv_mod_period hwN.ne' (zf : ℂ)
        have him' : 0 < ((zf : ℂ) + m * N).im := by simpa using zf.im_pos
        have hof : UpperHalfPlane.ofComplex (Function.Periodic.invQParam (N : ℝ) q) =
            (ModularGroup.T ^ ((m : ℤ) * N)) • zf := by
          rw [UpperHalfPlane.modular_T_zpow_smul, hqdef, hm]
          apply UpperHalfPlane.ext
          have him'' : 0 < ((zf : ℂ) + (m : ℂ) * ((N : ℝ) : ℂ)).im := by simpa using zf.im_pos
          rw [UpperHalfPlane.ofComplex_apply_of_im_pos him'', UpperHalfPlane.coe_vadd]
          push_cast
          ring
        have hmem : s₀ * ModularGroup.T ^ ((m : ℤ) * N) * s₀⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
          have h1 : MulAut.conj s₀ (ModularGroup.T ^ (N : ℤ)) ∈ CongruenceSubgroup.Gamma0 N := by
            rw [MulAut.conj_apply]; exact conj_T_zpow_mem_Gamma0 N s₀
          have h2 := Subgroup.zpow_mem _ h1 m
          rw [← map_zpow, ← zpow_mul, MulAut.conj_apply] at h2
          rwa [mul_comm (m : ℤ)]
        rw [hof, ← mul_smul,
          show s₀ * ModularGroup.T ^ ((m : ℤ) * N) = (s₀ * ModularGroup.T ^ ((m : ℤ) * N) * s₀⁻¹) * s₀ by group,
          mul_smul, D.pt_smul ⟨_, hmem⟩, hpt, D.pt_smul ⟨γ'⁻¹ * γ, mul_mem (inv_mem hγ') hγ⟩]
  ·
    intro k hk u hu huL lam hlam xh hxh eta heta
    set Sψ : ℝ := PLB.supPsi D σ s k u with hSψ
    have hSle : ∀ τ : ℍ, (D.pt τ).evalAt (phi N σ u) ≠ 0 → PLB.psiU D σ s k u τ ≤ Sψ :=
      fun τ hτ => by
        rw [hSψ]
        exact le_ciSup (hbdd σ k u hu huL) (⟨τ, hτ⟩ : PLB.Gen D σ u)
    set U : ℂ → ℂ := fun z => ATLINT.ext (N := N) (phi N σ u) z with hUdef
    rintro (⟨t, ht⟩ | ⟨g, hg⟩)
    ·
      have htim := hTim t ht
      have hcoreim : ∀ z ∈ closedBall t (t.im / 16), 0 < z.im := by
        intro z hz
        have h1 : |z.im - t.im| ≤ t.im / 16 := by
          have := mem_closedBall.1 hz
          rw [dist_eq_norm] at this
          exact (Complex.abs_im_le_norm (z - t)).trans (by simpa using this)
        have := (abs_le.1 h1).1
        linarith
      set K : Set ℂ := {z | z ∈ closedBall t (t.im / 16) ∧
        (Real.exp (Sψ - lam) * (⨆ i, ‖Φint σ s z i‖) ^ k - ‖U z‖ ∈ Set.Ici (0 : ℝ) ∧
         pchd (Φint σ₀ s z) xh - eta ∈ Set.Ici (0 : ℝ))} with hKdef
      have hcontU : ContinuousOn U (closedBall t (t.im / 16)) := continuousOn_ext_of_memL D σ huL hcoreim
      have hcontΦ : ContinuousOn (Φint σ₀ s) (closedBall t (t.im / 16)) := by
        have hA := (interior_chart' D σ₀ s hs t htim).1
        exact continuousOn_pi.2 fun i => (hA i).continuousOn.mono (closedBall_subset_ball (by linarith))
      have hΦne : ∀ z ∈ closedBall t (t.im / 16), Φint σ₀ s z ≠ 0 := fun z hz =>
        (interior_chart' D σ₀ s hs t htim).2.1 z (closedBall_subset_ball (by linarith) hz)
      have hKclosed : IsClosed K := by
        have h1 : ContinuousOn (fun z => (Real.exp (Sψ - lam) * (⨆ i, ‖Φint σ s z i‖) ^ k - ‖U z‖,
            pchd (Φint σ₀ s z) xh - eta)) (closedBall t (t.im / 16)) := by
          refine ContinuousOn.prodMk ?_ ((continuousOn_pchd_left hcontΦ hΦne hxh).sub continuousOn_const)
          refine ContinuousOn.sub (continuousOn_const.mul (ContinuousOn.pow ?_ k)) hcontU.norm
          have : (fun z => ⨆ i, ‖Φint σ s z i‖) = fun z => ‖Φint σ₀ s z‖ := by
            funext z; rw [pi_norm_eq_ciSup, hΦ]
          rw [this]
          exact hcontΦ.norm
        have := h1.preimage_isClosed_of_isClosed isClosed_closedBall ((isClosed_Ici (a := (0:ℝ))).prod (isClosed_Ici (a := (0:ℝ))))
        convert this using 1
        all_goals first | rfl | (ext z; simp only [hKdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod])
      refine ⟨K, hKclosed, fun z hz => hz.1, fun z hz => by
          show eta ≤ pchd (Φint σ₀ s z) xh
          have := hz.2.2; simp only [Set.mem_Ici] at this; linarith,
        ?_, ?_⟩
      ·
        have hbig := hCb σ hσ k hk u hu huL lam hlam
        refine le_trans (measure_mono ?_) (hbig.trans (ENNReal.ofReal_le_ofReal ?_))
        · rintro z ⟨hz, h1, -⟩
          simp only [Set.mem_Ici, sub_nonneg] at h1
          have htb := hTbox t ht
          have hd : ‖z - t‖ ≤ t.im / 16 := by simpa [dist_eq_norm] using mem_closedBall.1 hz
          have hre : |z.re - t.re| ≤ t.im / 16 := (Complex.abs_re_le_norm (z - t)).trans (by simpa using hd)
          have him : |z.im - t.im| ≤ t.im / 16 := (Complex.abs_im_le_norm (z - t)).trans (by simpa using hd)
          refine ⟨?_, ?_, ?_, h1⟩
          · have := abs_le.1 hre; have := abs_le.1 htb.1
            rw [abs_le]; constructor <;> linarith [htb.2.1, htb.2.2]
          · have := (abs_le.1 him).1; linarith [htb.2.1]
          · have := (abs_le.1 him).2; linarith [htb.2.2, htb.2.1]
        · have hk1 : (0:ℝ) < k + 1 := by positivity
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCble hk1.le) hlam.le
      ·
        intro z hz hzD hzK hfar
        have hnot : ¬ ‖U z‖ ≤ Real.exp (Sψ - lam) * (⨆ i, ‖Φint σ s z i‖) ^ k := by
          intro hle
          exact hzK ⟨hz, by simpa only [Set.mem_Ici, sub_nonneg] using hle,
            by simp only [Set.mem_Ici, sub_nonneg]; exact hfar⟩
        have hz' : ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := UpperHalfPlane.ofComplex_apply_of_im_pos hzD ▸ rfl
        show Sψ - lam < PLB.psiU D σ s k u (UpperHalfPlane.ofComplex z)
        refine psiU_gt_of_not_le D σ s hs huL _ ?_
        rwa [hz']
    ·
      have hΦcc : ContinuousOn (Φc g) (closedBall 0 (rc g)) :=
        continuousOn_pi.2 fun i => (hRgA g i).continuousOn.mono
          (closedBall_subset_ball (by linarith [hrcle g, hRg g]))
      obtain ⟨Ut, hUtc, hUt⟩ := utilde D σ s hs g (Nat.pos_of_ne_zero (NeZero.ne N)) (conj_T_zpow_mem_Gamma0 N g)
        (hAc g) (hrcpos g) (by linarith [hrcle g, hRg1 g]) hΦcc (hlift_im g)
        (fun τ hτ => (hA₁ g τ hτ).trans (by linarith [hrcpos g])) (fun τ hτ => by rw [hΦcV g τ hτ, hΦ]) hu huL hSle
      set K : Set ℂ := {q | q ∈ closedBall (0 : ℂ) (rc g) ∧
        (Real.exp (Sψ - lam) * (⨆ i, ‖Φc g q i‖) ^ k - ‖Ut q‖ ∈ Set.Ici (0 : ℝ) ∧
         pchd (Φc g q) xh - eta ∈ Set.Ici (0 : ℝ))} with hKdef
      have hΦne : ∀ q ∈ closedBall (0 : ℂ) (rc g), Φc g q ≠ 0 := fun q hq =>
        hRgZ g q (closedBall_subset_ball (by linarith [hrcle g, hRg g]) hq)
      have hKclosed : IsClosed K := by
        have h1 : ContinuousOn (fun q => (Real.exp (Sψ - lam) * (⨆ i, ‖Φc g q i‖) ^ k - ‖Ut q‖,
            pchd (Φc g q) xh - eta)) (closedBall 0 (rc g)) := by
          refine ContinuousOn.prodMk ?_ ((continuousOn_pchd_left hΦcc hΦne hxh).sub continuousOn_const)
          refine ContinuousOn.sub (continuousOn_const.mul (ContinuousOn.pow ?_ k)) hUtc.norm
          have : (fun q => ⨆ i, ‖Φc g q i‖) = fun q => ‖Φc g q‖ := by
            funext q; rw [pi_norm_eq_ciSup]
          rw [this]
          exact hΦcc.norm
        have := h1.preimage_isClosed_of_isClosed isClosed_closedBall ((isClosed_Ici (a := (0:ℝ))).prod (isClosed_Ici (a := (0:ℝ))))
        convert this using 1
        all_goals first | rfl | (ext z; simp only [hKdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod])
      refine ⟨K, hKclosed, fun q hq => hq.1, fun q hq => by
          show eta ≤ pchd (Φc g q) xh
          have := hq.2.2; simp only [Set.mem_Ici] at this; linarith,
        ?_, ?_⟩
      ·
        have hbig := hCg g σ hσ k hk u hu huL lam hlam
        have hsub : K \ {0} ⊆ {q : ℂ | q ∈ Metric.ball (0 : ℂ) (Rg g) ∧ q ≠ 0 ∧
            ‖ATLINT.ext (N := N) (phi N σ u)
                ((g • UpperHalfPlane.ofComplex (Function.Periodic.invQParam (N : ℝ) q) : ℍ) : ℂ)‖
              ≤ Real.exp (Sψ - lam)
                * (⨆ i, ‖Φint σ s ((g • UpperHalfPlane.ofComplex (Function.Periodic.invQParam (N : ℝ) q) : ℍ) : ℂ) i‖) ^ k} := by
          rintro q ⟨⟨hq, h1, -⟩, hq0⟩
          have hq0' : q ≠ 0 := hq0
          have hqn : ‖q‖ ≤ rc g := by simpa [mem_closedBall, dist_zero_right] using hq
          refine ⟨by rw [mem_ball, dist_zero_right]; linarith [hrcle g, hRg g], hq0', ?_⟩
          simp only [Set.mem_Ici, sub_nonneg] at h1

          set τq : ℍ := UpperHalfPlane.ofComplex (Function.Periodic.invQParam (N : ℝ) q) with hτq
          have him := hlift_im g q hq0' hqn
          have hpos : 0 < (Function.Periodic.invQParam (N : ℝ) q).im := (hAc g).trans_le him
          have hτqim : Ac g ≤ τq.im := by
            rw [hτq, UpperHalfPlane.ofComplex_apply_of_im_pos hpos]; exact him
          have hqq : Function.Periodic.qParam (N : ℝ) (τq : ℂ) = q := by
            rw [hτq, UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
            exact Function.Periodic.qParam_right_inv hwN.ne' hq0'
          have hΦq : Φc g q = q ^ mc g • Φint σ s ((g • τq : ℍ) : ℂ) := by
            have := hΦcV g τq hτqim; rw [hqq] at this; rw [this, hΦ]
          have hUq := hUt q hq0' hqn
          have htpos : 0 < ‖q ^ mc g‖ := norm_pos_iff.2 (zpow_ne_zero _ hq0')
          have hsup : (⨆ i, ‖Φc g q i‖) = ‖q ^ mc g‖ * ⨆ i, ‖Φint σ s ((g • τq : ℍ) : ℂ) i‖ := by
            rw [← pi_norm_eq_ciSup, ← pi_norm_eq_ciSup, hΦq, norm_smul]
          rw [hUq, hsup, norm_mul, norm_pow, mul_pow, ← mul_assoc, mul_comm (Real.exp _), mul_assoc] at h1
          exact le_of_mul_le_mul_left h1 (pow_pos htpos k)
        calc volume K ≤ volume ((K \ {0}) ∪ ({0} : Set ℂ)) := measure_mono (Set.subset_diff_union K {0})
          _ ≤ volume (K \ {0}) + volume ({0} : Set ℂ) := measure_union_le _ _
          _ ≤ ENNReal.ofReal (Cg g * (k + 1) / lam) + 0 := by
              gcongr
              · exact (measure_mono hsub).trans hbig
              · exact (measure_singleton (0 : ℂ)).le
          _ ≤ ENNReal.ofReal (Cvol * (k + 1) / lam) := by
              rw [add_zero]
              refine ENNReal.ofReal_le_ofReal ?_
              have hk1 : (0:ℝ) < k + 1 := by positivity
              exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCgle g hg) hk1.le) hlam.le
      ·
        intro q hq hqD hqK hfar
        have hq0' : q ≠ 0 := hqD
        have hqn : ‖q‖ ≤ rc g := by simpa [mem_closedBall, dist_zero_right] using hq
        have hnot : ¬ ‖Ut q‖ ≤ Real.exp (Sψ - lam) * (⨆ i, ‖Φc g q i‖) ^ k := by
          intro hle
          exact hqK ⟨hq, by simpa only [Set.mem_Ici, sub_nonneg] using hle,
            by simp only [Set.mem_Ici, sub_nonneg]; exact hfar⟩
        set τq : ℍ := UpperHalfPlane.ofComplex (Function.Periodic.invQParam (N : ℝ) q) with hτq
        have him := hlift_im g q hq0' hqn
        have hpos : 0 < (Function.Periodic.invQParam (N : ℝ) q).im := (hAc g).trans_le him
        have hτqim : Ac g ≤ τq.im := by
          rw [hτq, UpperHalfPlane.ofComplex_apply_of_im_pos hpos]; exact him
        have hqq : Function.Periodic.qParam (N : ℝ) (τq : ℂ) = q := by
          rw [hτq, UpperHalfPlane.ofComplex_apply_of_im_pos hpos]
          exact Function.Periodic.qParam_right_inv hwN.ne' hq0'
        have hΦq : Φc g q = q ^ mc g • Φint σ s ((g • τq : ℍ) : ℂ) := by
          have := hΦcV g τq hτqim; rw [hqq] at this; rw [this, hΦ]
        have hUq := hUt q hq0' hqn
        have htpos : 0 < ‖q ^ mc g‖ := norm_pos_iff.2 (zpow_ne_zero _ hq0')
        have hsup : (⨆ i, ‖Φc g q i‖) = ‖q ^ mc g‖ * ⨆ i, ‖Φint σ s ((g • τq : ℍ) : ℂ) i‖ := by
          rw [← pi_norm_eq_ciSup, ← pi_norm_eq_ciSup, hΦq, norm_smul]
        show Sψ - lam < PLB.psiU D σ s k u (g • τq)
        refine psiU_gt_of_not_le D σ s hs huL _ fun hle => hnot ?_
        rw [hUq, hsup, norm_mul, norm_pow, mul_pow, ← mul_assoc, mul_comm (Real.exp _), mul_assoc]
        exact mul_le_mul_of_nonneg_left hle (pow_pos htpos k).le

theorem off_box_lift (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (hs : IsEmbBasis N s) {Bx y₀ Y₁ Yb : ℝ} {Sb S₀ : Finset SL(2, ℤ)}
    (hcov : ∀ τ : ℍ, ∃ γ ∈ CongruenceSubgroup.Gamma0 N,
      (|(γ • τ).re| ≤ Bx ∧ y₀ ≤ (γ • τ).im ∧ (γ • τ).im ≤ Y₁) ∨
      (∃ σ₁ ∈ Sb, ∃ z ∈ ModularGroup.fd, Yb < z.im ∧ γ • τ = σ₁ • z))
    (hS₀ : ∀ g : SL(2, ℤ), ∃ γ ∈ CongruenceSubgroup.Gamma0 N, ∃ s₀ ∈ S₀, g = γ * s₀)
    (v : Place (AlgebraicClosure ℚ) (FB N)) (hj : jB N ∈ v.toValuationSubring)
    (hoff : ¬ ∃ τ : ℍ, v.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) ∧
      (|(τ : ℂ).re| ≤ Bx ∧ y₀ ≤ (τ : ℂ).im ∧ (τ : ℂ).im ≤ Y₁)) :
    ∃ s₀ ∈ S₀, ∃ z : ℍ, Yb < z.im ∧
      v.toValuationSubring = (D.pt (s₀ • z)).toValuationSubring.comap (phi N σ) ∧
      ∃ t : ℂ, t ≠ 0 ∧ (fun i => σ (evalVec s v i)) = t • Φint σ s ((s₀ • z : ℍ) : ℂ) := by
  obtain ⟨τv, hcomap, t, ht, hxv⟩ := place_proj' D σ s hs v hj
  obtain ⟨γ, hγ, hγτ⟩ := hcov τv
  have hpt : D.pt ((((⟨γ, hγ⟩ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • τv : ℍ)) = D.pt τv :=
    D.pt_smul ⟨γ, hγ⟩ τv
  have hΦ : Φint σ s (((((⟨γ, hγ⟩ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • τv : ℍ)) : ℂ) = Φint σ s (τv : ℂ) :=
    Φint_smul D σ s hs ⟨γ, hγ⟩ τv
  rcases hγτ with hbox | ⟨σ₁, hσ₁, z, -, hz, hγz⟩
  · exact absurd ⟨γ • τv, by rw [hcomap, ← hpt], hbox⟩ hoff
  · obtain ⟨γ₁, hγ₁, s₀, hs₀, rfl⟩ := hS₀ σ₁
    have hγz' : ((((⟨γ, hγ⟩ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • τv : ℍ)) =
        (((⟨γ₁, hγ₁⟩ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • (s₀ • z) : ℍ) := by
      rw [← mul_smul]; exact hγz
    refine ⟨s₀, hs₀, z, hz, ?_, t, ht, ?_⟩
    · rw [hcomap, ← hpt, hγz', D.pt_smul ⟨γ₁, hγ₁⟩ (s₀ • z)]
    · rw [hxv, ← hΦ, hγz', Φint_smul D σ s hs ⟨γ₁, hγ₁⟩ (s₀ • z)]

theorem cusp_rep (σ : AlgebraicClosure ℚ →+* ℂ) {S₀ : Finset SL(2, ℤ)}
    (hS₀ : ∀ g : SL(2, ℤ), ∃ γ ∈ CongruenceSubgroup.Gamma0 N, ∃ s₀ ∈ S₀, g = γ * s₀)
    (v : Place (AlgebraicClosure ℚ) (FB N)) (hj : jB N ∉ v.toValuationSubring) :
    ∃ s₀ ∈ S₀, cuspPl σ s₀ = v := by
  have hord : v.ord (jB N) < 0 := by
    by_contra h
    push_neg at h
    exact hj (v.mem_of_ord_nonneg jB_ne_zero h)
  obtain ⟨γ, hγv⟩ := exists_cuspPl_eq_of_ord_neg σ v hord
  obtain ⟨δ, hδ, s₀, hs₀, rfl⟩ := hS₀ γ
  have h10 : (1 : SL(2, ℤ)) 1 0 = 0 := by
    simp
  have hrel := cuspPl_rel (N := N) σ hδ s₀ 1 h10
  rw [mul_one] at hrel
  exact ⟨s₀, hs₀, by rw [← hγv, hrel]⟩

omit [NeZero N] in

theorem analyticOrderAt_sub_eq_one {f : ℂ → ℂ} {z₀ d : ℂ} (hf : AnalyticAt ℂ f z₀) (hd : HasDerivAt f d z₀)
    (hd0 : d ≠ 0) : analyticOrderAt (fun z => f z - f z₀) z₀ = 1 := by
  have hF : AnalyticAt ℂ (fun z => f z - f z₀) z₀ := hf.sub analyticAt_const
  have hFd : HasDerivAt (fun z => f z - f z₀) d z₀ := hd.sub_const (f z₀)
  refine analyticOrderAt_eq_one_of_divided (G := dslope (fun z => f z - f z₀) z₀) one_pos hF ?_ ?_ ?_
  · intro z _
    have h := sub_smul_dslope (fun z => f z - f z₀) z₀ z
    simp only [smul_eq_mul, sub_self, sub_zero] at h
    exact h.symm
  · exact continuousAt_dslope_same.2 hFd.differentiableAt
  · rw [dslope_same, hFd.deriv]; exact hd0

omit [NeZero N] in
theorem hasDerivAt_qParam' (w : ℝ) (z : ℂ) :
    HasDerivAt (Function.Periodic.qParam w)
      (Complex.exp (2 * Real.pi * Complex.I * z / w) * (2 * Real.pi * Complex.I / w)) z := by
  have h1 : HasDerivAt (fun z : ℂ => 2 * Real.pi * Complex.I * z / w) (2 * Real.pi * Complex.I / w) z := by
    have := ((hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I)).div_const (w : ℂ)
    simpa using this
  exact h1.cexp

omit [NeZero N] in

theorem analyticOrderAt_qParam_sub {w : ℝ} (hw : w ≠ 0) (z₀ : ℂ) :
    analyticOrderAt (fun z => Function.Periodic.qParam w z - Function.Periodic.qParam w z₀) z₀ = 1 := by
  have han : AnalyticAt ℂ (Function.Periodic.qParam w) z₀ := by
    have hd : Differentiable ℂ (Function.Periodic.qParam w) := fun z => (hasDerivAt_qParam' w z).differentiableAt
    exact hd.analyticAt z₀
  refine analyticOrderAt_sub_eq_one han (hasDerivAt_qParam' w z₀) ?_
  refine mul_ne_zero (Complex.exp_ne_zero _) (div_ne_zero ?_ (by exact_mod_cast hw))
  exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero

omit [NeZero N] in
theorem analyticAt_mob (γ : SL(2, ℤ)) (z : ℍ) : AnalyticAt ℂ (PLBCUSP.mob γ) (z : ℂ) := by
  unfold PLBCUSP.mob
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const) (PLBCUSP.denom_ne γ z)

omit [NeZero N] in
theorem analyticAt_qParam (w : ℝ) (z : ℂ) : AnalyticAt ℂ (Function.Periodic.qParam w) z :=
  (show Differentiable ℂ (Function.Periodic.qParam w) from
    fun z => (hasDerivAt_qParam' w z).differentiableAt).analyticAt z

omit [NeZero N] in

theorem analyticOrderAt_mob_sub (γ : SL(2, ℤ)) (z : ℍ) :
    analyticOrderAt (fun w => PLBCUSP.mob γ w - PLBCUSP.mob γ (z : ℂ)) (z : ℂ) = 1 := by
  have hden := PLBCUSP.denom_ne γ z
  have hnum : HasDerivAt (fun w : ℂ => ((γ 0 0 : ℤ) : ℂ) * w + ((γ 0 1 : ℤ) : ℂ)) ((γ 0 0 : ℤ) : ℂ) (z : ℂ) := by
    simpa using ((hasDerivAt_id (z : ℂ)).const_mul (((γ 0 0 : ℤ) : ℂ))).add_const (((γ 0 1 : ℤ) : ℂ))
  have hden' : HasDerivAt (fun w : ℂ => ((γ 1 0 : ℤ) : ℂ) * w + ((γ 1 1 : ℤ) : ℂ)) ((γ 1 0 : ℤ) : ℂ) (z : ℂ) := by
    simpa using ((hasDerivAt_id (z : ℂ)).const_mul (((γ 1 0 : ℤ) : ℂ))).add_const (((γ 1 1 : ℤ) : ℂ))
  have hdet : ((γ 0 0 : ℤ) : ℂ) * ((γ 1 1 : ℤ) : ℂ) - ((γ 0 1 : ℤ) : ℂ) * ((γ 1 0 : ℤ) : ℂ) = 1 := by
    have h := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
    rw [Matrix.SpecialLinearGroup.det_coe] at h
    exact_mod_cast h.symm
  have hder := hnum.div hden' hden
  refine analyticOrderAt_sub_eq_one (analyticAt_mob γ z) hder ?_
  rw [div_ne_zero_iff]
  refine ⟨?_, pow_ne_zero 2 hden⟩
  have e : ((γ 0 0 : ℤ) : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℂ)) -
      (((γ 0 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 0 1 : ℤ) : ℂ)) * ((γ 1 0 : ℤ) : ℂ) = 1 := by
    linear_combination hdet
  rw [e]; exact one_ne_zero

theorem linSec_single (s : Fin r → FB N) (i : Fin r) : linSec s (Pi.single i 1) = s i := by
  classical
  unfold linSec
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]

omit [NeZero N] in
theorem sum_mul_comb {R : Type*} [CommSemiring R] {n : ℕ} (c : Fin n → R) (i π : Fin n) (x : R) :
    ∑ j, c j * (Pi.single i 1 + x • Pi.single π 1 : Fin n → R) j = c i + x * c π := by
  classical
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_add, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

omit [NeZero N] in
theorem sum_comb_mul {R : Type*} [CommSemiring R] {n : ℕ} (c : Fin n → R) (i π : Fin n) (x : R) :
    ∑ j, (Pi.single i 1 + x • Pi.single π 1 : Fin n → R) j * c j = c i + x * c π := by
  rw [← sum_mul_comb c i π x]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem cusp_chart_orders (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (hs : IsEmbBasis N s) (g : SL(2, ℤ))
    {Φe : ℂ → (Fin r → ℂ)} {me : ℤ} {Ae : ℝ}
    (hA : ∀ i, AnalyticAt ℂ (fun q => Φe q i) 0) (h0 : Φe 0 ≠ 0)
    (hV : ∀ τ : ℍ, Ae ≤ τ.im →
      Φe (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) =
        Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me •
          Φint σ s ((g • τ : ℍ) : ℂ)) :
    me = embDivisor N (cuspPl σ g) ∧
    ∀ a : Fin r → AlgebraicClosure ℚ, linSec s a ≠ 0 →
      0 ≤ me + (cuspPl σ g).ord (linSec s a) ∧
      analyticOrderAt (fun q => ∑ i, σ (a i) * Φe q i) 0 = (((me + (cuspPl σ g).ord (linSec s a)).toNat : ℕ) : ℕ∞) := by
  classical
  have hw : 0 < Subgroup.strictWidthInfty (conjGamma0 N g) := strictWidthInfty_conjGamma0_pos g
  have hΓ : Subgroup.strictWidthInfty (conjGamma0 N g) ∈ (conjGamma0 N g).strictPeriods :=
    Subgroup.strictWidthInfty_mem_strictPeriods _
  have hr := r_pos N s hs

  have key : ∀ a : Fin r → AlgebraicClosure ℚ, linSec s a ≠ 0 →
      0 ≤ me + (cuspPl σ g).ord (linSec s a) ∧
      analyticOrderAt (fun q => ∑ i, σ (a i) * Φe q i) 0 =
        (((me + (cuspPl σ g).ord (linSec s a)).toNat : ℕ) : ℕ∞) := by
    intro a ha
    have hy0 : phi N σ (linSec s a) ≠ 0 := phi_ne_zero σ ha
    have hyeq : phi N σ (linSec s a) = ∑ i, σ (a i) • phi N σ (s i) := phi_linSec s σ a
    have hyreg : ∀ τ : ℍ, phi N σ (linSec s a) ∈ (D.pt τ).toValuationSubring := fun τ => by
      rw [hyeq]; exact linComb_mem D σ s hs _ τ
    obtain ⟨Φy, A, hApos, hΦyan, hΦy0, -, hexp⟩ := PLB.ext_cusp_expansion (D := D) hy0 hyreg g hw hΓ
    have hθ : (cuspExpHomW g hw hΓ (phi N σ (linSec s a))).order = (cuspPl σ g).ord (linSec s a) :=
      order_thetaX_eq_ord σ g ha
    have hHan : AnalyticAt ℂ (fun q => ∑ i, σ (a i) * Φe q i) 0 := by
      have := Finset.univ.analyticAt_sum (c := (0:ℂ)) (f := fun i => fun q => σ (a i) * Φe q i)
        (fun i _ => analyticAt_const.mul (hA i))
      exact this.congr (Filter.Eventually.of_forall fun q => by simp [Finset.sum_apply])
    have hHq : ∀ τ : ℍ, max Ae A ≤ τ.im →
        (∑ i, σ (a i) * Φe (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) i) =
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^
              (me + (cuspPl σ g).ord (linSec s a)) *
            Φy (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) := by
      intro τ hτ
      have hq0 : Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ≠ 0 := by
        simp only [Function.Periodic.qParam]; exact Complex.exp_ne_zero _
      have h1 := hV τ ((le_max_left _ _).trans hτ)
      have h2 := hexp τ ((le_max_right _ _).trans hτ)
      rw [hθ] at h2
      have h3 : ∑ i, σ (a i) * Φint σ s ((g • τ : ℍ) : ℂ) i =
          ATLINT.ext (N := N) (phi N σ (linSec s a)) ((g • τ : ℍ) : ℂ) := by
        rw [hyeq, ATLINT.ext_linComb D Finset.univ (fun i => σ (a i)) (fun i => phi N σ (s i)) (g • τ)
          (fun i _ => (interiorInputs D σ s hs).reg _ i)]
        rfl
      calc ∑ i, σ (a i) * Φe (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) i
          = ∑ i, σ (a i) * (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me *
              Φint σ s ((g • τ : ℍ) : ℂ) i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [h1]; rfl
        _ = Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me *
              ∑ i, σ (a i) * Φint σ s ((g • τ : ℍ) : ℂ) i := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = _ := by rw [h3, h2, ← mul_assoc, ← zpow_add₀ hq0]
    have hev : ∀ᶠ Q in 𝓝[≠] (0 : ℂ), (∑ i, σ (a i) * Φe Q i) =
        Q ^ (me + (cuspPl σ g).ord (linSec s a)) * Φy Q :=
      eventually_nhdsNE_of_forall_qParam hw
        (P := fun Q => (∑ i, σ (a i) * Φe Q i) = Q ^ (me + (cuspPl σ g).ord (linSec s a)) * Φy Q) hHq
    obtain ⟨hn, -, -, hord⟩ := zpow_chart_exponent hHan hΦyan hΦy0 hev
    exact ⟨hn, hord⟩

  have hcoord : ∀ i, 0 ≤ me + (cuspPl σ g).ord (s i) ∧
      analyticOrderAt (fun q => Φe q i) 0 = (((me + (cuspPl σ g).ord (s i)).toNat : ℕ) : ℕ∞) := by
    intro i
    have hne : linSec s (Pi.single i 1) ≠ 0 := by rw [linSec_single]; exact s_ne_zero N s hs i
    obtain ⟨h1, h2⟩ := key _ hne
    rw [linSec_single] at h1 h2
    refine ⟨h1, ?_⟩
    rw [← h2]
    congr 1
    funext q
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (fun h => absurd (Finset.mem_univ i) h)]
    simp
  have hme : me = embDivisor N (cuspPl σ g) := by
    obtain ⟨i, hi⟩ : ∃ i, Φe 0 i ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact h0 (funext hall)
    have hzero : me + (cuspPl σ g).ord (s i) = 0 := by
      obtain ⟨h1, h2⟩ := hcoord i
      have h3 : analyticOrderAt (fun q => Φe q i) 0 = 0 := (hA i).analyticOrderAt_eq_zero.2 hi
      rw [h3] at h2
      have h4 : (me + (cuspPl σ g).ord (s i)).toNat = 0 := by exact_mod_cast h2.symm
      have := Int.toNat_of_nonneg h1
      omega
    have hπ := ord_pivotIndex_le' s (cuspPl σ g) hr i
    have hπ0 := (hcoord (pivotIndex s (cuspPl σ g) hr)).1
    have h5 : me + (cuspPl σ g).ord (s (pivotIndex s (cuspPl σ g) hr)) = 0 := by omega
    rw [ord_pivot N s hs (cuspPl σ g) hr] at h5
    omega
  exact ⟨hme, key⟩

theorem cusp_centre_prop (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (hs : IsEmbBasis N s) (g : SL(2, ℤ))
    {Φe : ℂ → (Fin r → ℂ)} {me : ℤ} {Ae : ℝ}
    (hA : ∀ i, AnalyticAt ℂ (fun q => Φe q i) 0) (h0 : Φe 0 ≠ 0)
    (hV : ∀ τ : ℍ, Ae ≤ τ.im →
      Φe (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) =
        Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me •
          Φint σ s ((g • τ : ℍ) : ℂ)) :
    ∃ c : ℂ, c ≠ 0 ∧ Φe 0 = c • (fun i => σ (evalVec s (cuspPl σ g) i)) := by
  classical
  obtain ⟨hme, key⟩ := cusp_chart_orders D σ s hs g hA h0 hV
  have hr := r_pos N s hs
  haveI hcurve : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar N

  have hcoordval : ∀ i, Φe 0 i = σ (evalVec s (cuspPl σ g) i) * Φe 0 (pivotIndex s (cuspPl σ g) hr) := by
    intro i
    by_cases hiπ : i = pivotIndex s (cuspPl σ g) hr
    · rw [hiπ, evalVec_pivotIndex s (cuspPl σ g) hr (s_ne_zero N s hs _), map_one, one_mul]
    set x : AlgebraicClosure ℚ := evalVec s (cuspPl σ g) i with hxdef
    set a : Fin r → AlgebraicClosure ℚ := Pi.single i 1 + (-x) • Pi.single (pivotIndex s (cuspPl σ g) hr) 1 with hadef
    have ha0 : linSec s a ≠ 0 := by
      intro h0'
      have h1 := Fintype.linearIndependent_iff.mp hs.1 a h0' i
      rw [hadef] at h1
      simp [Pi.single_apply, hiπ] at h1
    obtain ⟨hnn, hord⟩ := key a ha0

    have hsum : ∑ j, evalVec s (cuspPl σ g) j * a j = 0 := by
      rw [hadef, sum_mul_comb, evalVec_pivotIndex s (cuspPl σ g) hr (s_ne_zero N s hs _)]
      ring
    have hZa : 1 ≤ (cuspPl σ g).ord (linSec s a) + embDivisor N (cuspPl σ g) := by
      obtain ⟨Da, hDa, -⟩ := hcurve.toHasPrincipalDivisors.exists_divisor _ ha0
      obtain ⟨hnonneg, hiff⟩ := hypSec_facts N s hs a ha0 (Da + embDivisor N)
        (fun w => by rw [Finsupp.add_apply, hDa]) (cuspPl σ g)
      have hne : (Da + embDivisor N) (cuspPl σ g) ≠ 0 := fun h => (hiff.mp h) hsum
      rw [Finsupp.add_apply, hDa] at hnonneg hne
      omega

    have hval0 : (∑ j, σ (a j) * Φe 0 j) = 0 := by
      by_contra hne
      have hH : AnalyticAt ℂ (fun q => ∑ j, σ (a j) * Φe q j) 0 := by
        have := Finset.univ.analyticAt_sum (c := (0:ℂ)) (f := fun j => fun q => σ (a j) * Φe q j)
          (fun j _ => analyticAt_const.mul (hA j))
        exact this.congr (Filter.Eventually.of_forall fun q => by simp [Finset.sum_apply])
      have h0' := hH.analyticOrderAt_eq_zero.2 hne
      rw [hord] at h0'
      have h6 : (me + (cuspPl σ g).ord (linSec s a)).toNat = 0 := by exact_mod_cast h0'
      have := Int.toNat_of_nonneg hnn
      omega
    have hσa : (fun j => σ (a j)) = (Pi.single i 1 + (σ (-x)) • Pi.single (pivotIndex s (cuspPl σ g) hr) 1 : Fin r → ℂ) := by
      funext j
      rw [hadef]
      simp [Pi.single_apply, apply_ite σ]
    have h7 : ∑ j, σ (a j) * Φe 0 j = Φe 0 i + σ (-x) * Φe 0 (pivotIndex s (cuspPl σ g) hr) := by
      have := sum_comb_mul (fun j => Φe 0 j) i (pivotIndex s (cuspPl σ g) hr) (σ (-x))
      rw [← hσa] at this
      exact this
    rw [h7, map_neg] at hval0
    linear_combination hval0
  have hπ0 : Φe 0 (pivotIndex s (cuspPl σ g) hr) ≠ 0 := by
    intro h
    apply h0
    funext i
    rw [hcoordval i, h, mul_zero]
    rfl
  refine ⟨Φe 0 (pivotIndex s (cuspPl σ g) hr), hπ0, funext fun i => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hcoordval i, mul_comm]

theorem analyticOrderAt_pencil_eq_one (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (v : Place (AlgebraicClosure ℚ) (FB N)) {F : ℂ → (Fin r → ℂ)} {zb : ℂ}
    (hA : ∀ i, AnalyticAt ℂ (fun u => F u i) zb) (p : Fin r) (hbp : F zb p ≠ 0)
    {xh : Fin r → ℂ} (hxh : xh = fun i => σ (evalVec s v i * (evalVec s v p)⁻¹)) (hxw : F zb = (F zb p) • xh)
    {ρ₁ L : ℝ} (hρ₁ : 0 < ρ₁) (hL : 0 ≤ L) {Ψb : ℂ → (Fin r × Fin r → ℂ)}
    (hId : ∀ z ∈ closedBall zb ρ₁, ∀ q : Fin r × Fin r, F zb q.1 * F z q.2 - F zb q.2 * F z q.1 = (z - zb) * Ψb z q)
    (hLip : ∀ z ∈ closedBall zb ρ₁, ∀ z' ∈ closedBall zb ρ₁, ‖Ψb z - Ψb z'‖ ≤ L * ‖z - z'‖)
    (e : Fin r → AlgebraicClosure ℚ)
    (hgood : ∀ z ∈ closedBall zb ρ₁, ∑ i, σ (e i) * Ψb z (p, i) ≠ 0) :
    analyticOrderAt (fun z => ∑ i, σ (pencilAlg s v p e i) * F z i) zb = 1 := by
  classical
  set a := pencilAlg s v p e with ha
  set b : Fin r → ℂ := fun i => σ (e i) with hb
  have hFG : ∀ z ∈ closedBall zb ρ₁, (∑ i, σ (a i) * F z i) = (z - zb) * ((F zb p)⁻¹ * ∑ i, b i * Ψb z (p, i)) := by
    intro z hz
    have h1 : ∑ i, σ (a i) * F z i = ∑ i, F z i * pencilCov xh p b i :=
      Finset.sum_congr rfl fun i _ => by rw [ha, sigma_pencilAlg, ← hxh, mul_comm]
    rw [h1, pencilCov_chart, chord_eq_divided' (S := closedBall zb ρ₁) hId p hxw hbp b hz]
    ring
  have hFan : AnalyticAt ℂ (fun z => ∑ i, σ (a i) * F z i) zb := by
    have := Finset.univ.analyticAt_sum (c := zb) (f := fun i => fun z => σ (a i) * F z i)
      (fun i _ => analyticAt_const.mul (hA i))
    exact this.congr (Filter.Eventually.of_forall fun z => by simp [Finset.sum_apply])
  have hGc : ContinuousAt (fun z => (F zb p)⁻¹ * ∑ i, b i * Ψb z (p, i)) zb := by
    have hΨc : ContinuousAt Ψb zb := by
      refine Metric.continuousAt_iff.2 fun ε hε => ⟨min ρ₁ (ε / (L + 1)), by positivity, fun z hz => ?_⟩
      have hz1 : z ∈ closedBall zb ρ₁ := mem_closedBall.2 (hz.le.trans (min_le_left _ _))
      rw [dist_eq_norm]
      have h := hLip z hz1 zb (mem_closedBall_self hρ₁.le)
      have hd : ‖z - zb‖ < ε / (L + 1) := by
        have := hz; rw [dist_eq_norm] at this; exact this.trans_le (min_le_right _ _)
      calc ‖Ψb z - Ψb zb‖ ≤ L * ‖z - zb‖ := h
        _ ≤ (L + 1) * ‖z - zb‖ := by nlinarith [norm_nonneg (z - zb)]
        _ < (L + 1) * (ε / (L + 1)) := mul_lt_mul_of_pos_left hd (by linarith)
        _ = ε := mul_div_cancel₀ _ (by linarith)
    refine continuousAt_const.mul ?_
    exact tendsto_finset_sum _ fun i _ => (continuousAt_const.mul ((continuousAt_apply (p, i) _).comp hΨc)).tendsto
  have hG0 : (F zb p)⁻¹ * ∑ i, b i * Ψb zb (p, i) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hbp) (hgood zb (mem_closedBall_self hρ₁.le))
  exact analyticOrderAt_eq_one_of_divided hρ₁ hFan hFG hGc hG0

theorem simple_cusp0 (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (hs : IsEmbBasis N s) (g : SL(2, ℤ))
    {Φe : ℂ → (Fin r → ℂ)} {me : ℤ} {Ae : ℝ}
    (hA : ∀ i, AnalyticAt ℂ (fun q => Φe q i) 0) (h0 : Φe 0 ≠ 0)
    (hV : ∀ τ : ℍ, Ae ≤ τ.im →
      Φe (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) =
        Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me •
          Φint σ s ((g • τ : ℍ) : ℂ))
    (v : Place (AlgebraicClosure ℚ) (FB N)) (hv : cuspPl σ g = v)
    (p : Fin r) (hbp : Φe 0 p ≠ 0)
    {xh : Fin r → ℂ} (hxh : xh = fun i => σ (evalVec s v i * (evalVec s v p)⁻¹)) (hxw : Φe 0 = (Φe 0 p) • xh)
    {ρ₁ L : ℝ} (hρ₁ : 0 < ρ₁) (hL : 0 ≤ L) {Ψb : ℂ → (Fin r × Fin r → ℂ)}
    (hId : ∀ z ∈ closedBall (0 : ℂ) ρ₁, ∀ q : Fin r × Fin r, Φe 0 q.1 * Φe z q.2 - Φe 0 q.2 * Φe z q.1 = (z - 0) * Ψb z q)
    (hLip : ∀ z ∈ closedBall (0 : ℂ) ρ₁, ∀ z' ∈ closedBall (0 : ℂ) ρ₁, ‖Ψb z - Ψb z'‖ ≤ L * ‖z - z'‖)
    (e : Fin r → AlgebraicClosure ℚ) (ha0 : linSec s (pencilAlg s v p e) ≠ 0)
    (hgood : ∀ z ∈ closedBall (0 : ℂ) ρ₁, ∑ i, σ (e i) * Ψb z (p, i) ≠ 0) :
    v.ord (linSec s (pencilAlg s v p e)) + embDivisor N v = 1 := by
  subst hv
  have h1 := analyticOrderAt_pencil_eq_one σ s (cuspPl σ g) hA p hbp hxh hxw hρ₁ hL hId hLip e hgood
  obtain ⟨hme, key⟩ := cusp_chart_orders D σ s hs g hA h0 hV
  obtain ⟨hnn, hord⟩ := key _ ha0
  rw [h1] at hord
  have h2 : (me + (cuspPl σ g).ord (linSec s (pencilAlg s (cuspPl σ g) p e))).toNat = 1 := by
    exact_mod_cast hord.symm
  have := Int.toNat_of_nonneg hnn
  omega

theorem simple_high (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)
    (hs : IsEmbBasis N s) (g : SL(2, ℤ))
    {Φe : ℂ → (Fin r → ℂ)} {me : ℤ} {Ae Re w : ℝ} (hw : 0 < w) (hAe : 0 ≤ Ae)
    (hA : ∀ i, AnalyticOnNhd ℂ (fun q => Φe q i) (ball 0 Re))
    (hV : ∀ τ : ℍ, Ae ≤ τ.im →
      Φe (Function.Periodic.qParam w (τ : ℂ)) = Function.Periodic.qParam w (τ : ℂ) ^ me • Φint σ s ((g • τ : ℍ) : ℂ))
    (zτ : ℍ) (hzτ : Ae < zτ.im) (hzb1 : Function.Periodic.qParam w (zτ : ℂ) ∈ ball (0 : ℂ) Re)
    (v : Place (AlgebraicClosure ℚ) (FB N))
    (hv : v.toValuationSubring = (D.pt (g • zτ)).toValuationSubring.comap (phi N σ))
    (p : Fin r) (hbp : Φe (Function.Periodic.qParam w (zτ : ℂ)) p ≠ 0)
    {xh : Fin r → ℂ} (hxh : xh = fun i => σ (evalVec s v i * (evalVec s v p)⁻¹))
    (hxw : Φe (Function.Periodic.qParam w (zτ : ℂ)) = (Φe (Function.Periodic.qParam w (zτ : ℂ)) p) • xh)
    {ρ₁ L : ℝ} (hρ₁ : 0 < ρ₁) (hL : 0 ≤ L) {Ψb : ℂ → (Fin r × Fin r → ℂ)}
    (hId : ∀ z ∈ closedBall (Function.Periodic.qParam w (zτ : ℂ)) ρ₁, ∀ q : Fin r × Fin r,
      Φe (Function.Periodic.qParam w (zτ : ℂ)) q.1 * Φe z q.2 - Φe (Function.Periodic.qParam w (zτ : ℂ)) q.2 * Φe z q.1
        = (z - Function.Periodic.qParam w (zτ : ℂ)) * Ψb z q)
    (hLip : ∀ z ∈ closedBall (Function.Periodic.qParam w (zτ : ℂ)) ρ₁,
      ∀ z' ∈ closedBall (Function.Periodic.qParam w (zτ : ℂ)) ρ₁, ‖Ψb z - Ψb z'‖ ≤ L * ‖z - z'‖)
    (e : Fin r → AlgebraicClosure ℚ) (ha0 : linSec s (pencilAlg s v p e) ≠ 0)
    (hgood : ∀ z ∈ closedBall (Function.Periodic.qParam w (zτ : ℂ)) ρ₁, ∑ i, σ (e i) * Ψb z (p, i) ≠ 0) :
    v.ord (linSec s (pencilAlg s v p e)) + embDivisor N v = 1 := by
  classical
  set zb : ℂ := Function.Periodic.qParam w (zτ : ℂ) with hzbdef
  set a := pencilAlg s v p e with hadef
  have h1 : analyticOrderAt (fun z => ∑ i, σ (a i) * Φe z i) zb = 1 :=
    analyticOrderAt_pencil_eq_one σ s v (fun i => hA i zb hzb1) p hbp hxh hxw hρ₁ hL hId hLip e hgood
  set b : Fin r → ℂ := fun i => σ (a i) with hbdef
  have hfeq : (∑ i, b i • phi N σ (s i)) = phi N σ (linSec s a) := by rw [phi_linSec]
  have hb : (∑ i, b i • phi N σ (s i)) ≠ 0 := by rw [hfeq]; exact phi_ne_zero σ ha0
  obtain ⟨hord0, hF₂⟩ := ATLINT.analyticOrderAt_linComb D σ s hs b hb (g • zτ)
  have hq0 : ∀ τ' : ℂ, Function.Periodic.qParam w τ' ≠ 0 := fun τ' => by
    simp only [Function.Periodic.qParam]; exact Complex.exp_ne_zero _

  have hopen : IsOpen {τ' : ℂ | Ae < τ'.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : (fun τ' : ℂ => ∑ i, σ (a i) * Φe (Function.Periodic.qParam w τ') i) =ᶠ[𝓝 (zτ : ℂ)]
      fun τ' => Function.Periodic.qParam w τ' ^ me * ∑ i, b i * Φint σ s (PLBCUSP.mob g τ') i := by
    filter_upwards [hopen.mem_nhds (show Ae < (zτ : ℂ).im from hzτ)] with τ' hτ'
    have him : 0 < τ'.im := hAe.trans_lt hτ'
    have hc : ((ofComplex τ' : ℍ) : ℂ) = τ' := by rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]; try rfl
    have h2 := hV (ofComplex τ') (by rw [← UpperHalfPlane.coe_im, hc]; exact hτ'.le)
    have hmob : ((g • ofComplex τ' : ℍ) : ℂ) = PLBCUSP.mob g τ' := by rw [PLBCUSP.coe_smul_eq, hc]
    rw [hc, hmob] at h2
    rw [h2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

  have hmobz : PLBCUSP.mob g (zτ : ℂ) = ((g • zτ : ℍ) : ℂ) := (PLBCUSP.coe_smul_eq g zτ).symm
  have hF₂an : AnalyticAt ℂ (fun z => ∑ i, b i * Φint σ s z i) (PLBCUSP.mob g (zτ : ℂ)) := by
    rw [hmobz]; exact ATLINT.analyticAt_linComb D σ s hs b (g • zτ).im_pos
  have hmoban : AnalyticAt ℂ (PLBCUSP.mob g) (zτ : ℂ) := analyticAt_mob g zτ
  have hcomp : analyticOrderAt (fun τ' => ∑ i, b i * Φint σ s (PLBCUSP.mob g τ') i) (zτ : ℂ)
      = analyticOrderAt (fun z => ∑ i, b i * Φint σ s z i) (PLBCUSP.mob g (zτ : ℂ)) := by
    have := Cay.analyticOrderAt_comp (f := fun z => ∑ i, b i * Φint σ s z i) (g := PLBCUSP.mob g) (m := 1)
      hF₂an hmoban (by exact_mod_cast analyticOrderAt_mob_sub g zτ)
    simpa using this
  have hzpow : AnalyticAt ℂ (fun τ' : ℂ => Function.Periodic.qParam w τ' ^ me) (zτ : ℂ) :=
    (show Differentiable ℂ (fun τ' : ℂ => Function.Periodic.qParam w τ' ^ me) from
      fun z => (hasDerivAt_qParam' w z).differentiableAt.zpow (Or.inl (hq0 z))).analyticAt _
  have hcompan : AnalyticAt ℂ (fun τ' => ∑ i, b i * Φint σ s (PLBCUSP.mob g τ') i) (zτ : ℂ) := hF₂an.comp hmoban
  have hzpow0 : analyticOrderAt (fun τ' : ℂ => Function.Periodic.qParam w τ' ^ me) (zτ : ℂ) = 0 :=
    hzpow.analyticOrderAt_eq_zero.2 (zpow_ne_zero _ (hq0 _))
  have hRHS : analyticOrderAt (fun τ' => Function.Periodic.qParam w τ' ^ me *
      ∑ i, b i * Φint σ s (PLBCUSP.mob g τ') i) (zτ : ℂ)
      = analyticOrderAt (fun z => ∑ i, b i * Φint σ s z i) (PLBCUSP.mob g (zτ : ℂ)) := by
    rw [show (fun τ' => Function.Periodic.qParam w τ' ^ me * ∑ i, b i * Φint σ s (PLBCUSP.mob g τ') i)
        = (fun τ' : ℂ => Function.Periodic.qParam w τ' ^ me) * (fun τ' => ∑ i, b i * Φint σ s (PLBCUSP.mob g τ') i)
        from rfl]
    rw [analyticOrderAt_mul hzpow hcompan, hzpow0, zero_add, hcomp]

  have hLHS : analyticOrderAt (fun τ' : ℂ => ∑ i, σ (a i) * Φe (Function.Periodic.qParam w τ') i) (zτ : ℂ) = 1 := by
    have hHan : AnalyticAt ℂ (fun z => ∑ i, σ (a i) * Φe z i) (Function.Periodic.qParam w (zτ : ℂ)) := by
      have := Finset.univ.analyticAt_sum (c := zb) (f := fun i => fun z => σ (a i) * Φe z i)
        (fun i _ => analyticAt_const.mul (hA i zb hzb1))
      exact this.congr (Filter.Eventually.of_forall fun z => by simp [Finset.sum_apply])
    have := Cay.analyticOrderAt_comp (f := fun z => ∑ i, σ (a i) * Φe z i) (g := Function.Periodic.qParam w)
      (m := 1) hHan (analyticAt_qParam w _) (by exact_mod_cast analyticOrderAt_qParam_sub hw.ne' (zτ : ℂ))
    rw [h1] at this
    simpa using this
  rw [analyticOrderAt_congr hev, hRHS, hmobz, hF₂] at hLHS

  have hram : 0 < D.ramification (g • zτ) := D.ramification_pos _
  have h3 : ((D.ramification (g • zτ) : ℤ) * (D.pt (g • zτ)).ord (∑ i, b i • phi N σ (s i))).toNat = 1 := by
    exact_mod_cast hLHS
  have hprod_nn : 0 ≤ (D.ramification (g • zτ) : ℤ) * (D.pt (g • zτ)).ord (∑ i, b i • phi N σ (s i)) := by
    positivity
  have hprod : (D.ramification (g • zτ) : ℤ) * (D.pt (g • zτ)).ord (∑ i, b i • phi N σ (s i)) = 1 := by
    have := Int.toNat_of_nonneg hprod_nn; omega
  have hordw : (D.pt (g • zτ)).ord (∑ i, b i • phi N σ (s i)) = 1 := Int.eq_one_of_mul_eq_one_left hord0 hprod
  rw [PLB.embDivisor_eq_zero_of_comap D σ v (g • zτ) hv, add_zero, ← CUSPATLAS.ord_eq_of_comap_eq σ v (D.pt (g • zτ)) hv,
    ← hfeq, hordw]

theorem cusp_chart_imm₂ (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N) (hs : IsEmbBasis N s) (g : SL(2, ℤ))
    {Φ : ℂ → (Fin r → ℂ)} {m : ℤ} {A₀ : ℝ}
    (hA : ∀ i, AnalyticAt ℂ (fun q => Φ q i) 0) (h0 : Φ 0 ≠ 0)
    (hΦ : ∀ τ : ℍ, A₀ ≤ τ.im → ∀ i, Φ (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) i =
      Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ m *
        realize N ((phi N σ (s i) : FC N) : LaurentSeries ℂ) (g • τ)) :
    ∃ q : Fin r × Fin r, Φ 0 q.1 * deriv (fun z => Φ z q.2) 0 - Φ 0 q.2 * deriv (fun z => Φ z q.1) 0 ≠ 0 := by
  classical
  have hw : 0 < Subgroup.strictWidthInfty (conjGamma0 N g) := strictWidthInfty_conjGamma0_pos g
  have hΓ : Subgroup.strictWidthInfty (conjGamma0 N g) ∈ (conjGamma0 N g).strictPeriods :=
    Subgroup.strictWidthInfty_mem_strictPeriods _
  obtain ⟨piv, hpiv⟩ : ∃ i, Φ 0 i ≠ 0 := by
    by_contra h
    push_neg at h
    exact h0 (funext h)
  have hRR : ∃ f ∈ riemannRochSpace (embDivisor N), f ≠ 0 ∧ (cuspPl (N := N) σ g).ord f + embDivisor N (cuspPl σ g) = 1 := by
    obtain ⟨f, hf0, hfL, hf1⟩ := PLBALG.exists_mem_riemannRochSpace_ord_add_eq_one N (cuspPl (N := N) σ g)
    exact ⟨f, hfL, hf0, hf1⟩
  obtain ⟨Ψ, hΨan, hfac, i₀, hi₀⟩ :=
    cusp_chart_factor g hw hΓ σ s hs (cuspPl_spec (N := N) σ g) hRR Φ m hA hΦ piv hpiv
  rw [cuspIdx_eq_one (cuspPl_spec (N := N) σ g)] at hfac
  refine ⟨(piv, i₀), ?_⟩

  have hmin : HasDerivAt (fun Q => Φ Q i₀ * Φ 0 piv - Φ Q piv * Φ 0 i₀) (Ψ 0 i₀) 0 := by
    have h1 : (fun Q => Q * Ψ Q i₀) =ᶠ[𝓝 (0 : ℂ)] (fun Q => Φ Q i₀ * Φ 0 piv - Φ Q piv * Φ 0 i₀) :=
      hfac.mono fun Q hQ => by
        show Q * Ψ Q i₀ = Φ Q i₀ * Φ 0 piv - Φ Q piv * Φ 0 i₀
        rw [hQ i₀, pow_one]
    refine HasDerivAt.congr_of_eventuallyEq ?_ h1.symm
    have hΨd : HasDerivAt (fun Q => Ψ Q i₀) (deriv (fun Q => Ψ Q i₀) 0) 0 := (hΨan i₀).differentiableAt.hasDerivAt
    have := (hasDerivAt_id (0 : ℂ)).mul hΨd
    first
      | simpa using this
      | (have h' := this; simp at h'; exact h')
      | (simp; exact this)
      | exact this
  have hd₁ : HasDerivAt (fun z => Φ z i₀) (deriv (fun z => Φ z i₀) 0) 0 := (hA i₀).differentiableAt.hasDerivAt
  have hd₂ : HasDerivAt (fun z => Φ z piv) (deriv (fun z => Φ z piv) 0) 0 := (hA piv).differentiableAt.hasDerivAt
  have hmin' : HasDerivAt (fun Q => Φ Q i₀ * Φ 0 piv - Φ Q piv * Φ 0 i₀)
      (deriv (fun z => Φ z i₀) 0 * Φ 0 piv - deriv (fun z => Φ z piv) 0 * Φ 0 i₀) 0 :=
    (hd₁.mul_const _).sub (hd₂.mul_const _)
  have heq := hmin.unique hmin'
  show Φ 0 piv * deriv (fun z => Φ z i₀) 0 - Φ 0 i₀ * deriv (fun z => Φ z piv) 0 ≠ 0
  rw [show Φ 0 piv * deriv (fun z => Φ z i₀) 0 - Φ 0 i₀ * deriv (fun z => Φ z piv) 0 = Ψ 0 i₀ by rw [heq]; ring]
  exact hi₀

theorem off_charts₂ (D : ComplexPlaceDictionary N) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (σ₀ : AlgebraicClosure ℚ →+* ℂ) :
    ∃ (Φe : SL(2, ℤ) → ℂ → (Fin r → ℂ)) (me : SL(2, ℤ) → ℤ)
      (Re Ae ρe ρ₁e Le mme Yr : SL(2, ℤ) → ℝ) (ce : SL(2, ℤ) → ℂ),
      ∀ g, 0 < Re g ∧ Re g < 1 ∧ 0 < Ae g ∧
        (∀ i, AnalyticOnNhd ℂ (fun q => Φe g q i) (ball 0 (Re g))) ∧ (∀ q ∈ ball (0 : ℂ) (Re g), Φe g q ≠ 0) ∧
        (∀ τ : ℍ, Ae g ≤ τ.im →
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ∈ ball (0 : ℂ) (Re g) ∧
          Φe g (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) =
            Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me g •
              Φint σ₀ s ((g • τ : ℍ) : ℂ)) ∧
        ce g ≠ 0 ∧ Φe g 0 = ce g • (fun i => σ₀ (evalVec s (cuspPl σ₀ g) i)) ∧
        0 < ρe g ∧ ρe g < Re g ∧ 0 < ρ₁e g ∧ 0 ≤ Le g ∧ 0 < mme g ∧
        (∀ w ∈ closedBall (0 : ℂ) (ρe g), closedBall w (ρ₁e g) ⊆ ball (0 : ℂ) (Re g) ∧
          ∃ Ψw : ℂ → (Fin r × Fin r → ℂ),
            (∀ z ∈ closedBall w (ρ₁e g), ∀ q : Fin r × Fin r,
              Φe g w q.1 * Φe g z q.2 - Φe g w q.2 * Φe g z q.1 = (z - w) * Ψw z q) ∧
            (∀ z ∈ closedBall w (ρ₁e g), ∀ z' ∈ closedBall w (ρ₁e g), ‖Ψw z - Ψw z'‖ ≤ Le g * ‖z - z'‖) ∧
            (∀ p : Fin r, ‖Φe g w p‖ = ‖Φe g w‖ → mme g ≤ ‖fun i => Ψw w (p, i)‖)) ∧
        Ae g ≤ Yr g ∧
        Real.exp (-2 * Real.pi * Yr g / Subgroup.strictWidthInfty (conjGamma0 N g)) ≤ ρe g / 2 ∧
        (∀ τ τ' : ℍ, Yr g ≤ τ.im → Yr g ≤ τ'.im → ∀ δ ∈ CongruenceSubgroup.Gamma0 N, δ • g • τ = g • τ' →
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) =
            Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ' : ℂ)) := by
  classical
  have key : ∀ g : SL(2, ℤ), ∃ (Φe : ℂ → (Fin r → ℂ)) (me : ℤ) (Re Ae ρe ρ₁e Le mme Yr : ℝ) (ce : ℂ),
      0 < Re ∧ Re < 1 ∧ 0 < Ae ∧
        (∀ i, AnalyticOnNhd ℂ (fun q => Φe q i) (ball 0 Re)) ∧ (∀ q ∈ ball (0 : ℂ) Re, Φe q ≠ 0) ∧
        (∀ τ : ℍ, Ae ≤ τ.im →
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ∈ ball (0 : ℂ) Re ∧
          Φe (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) =
            Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me •
              Φint σ₀ s ((g • τ : ℍ) : ℂ)) ∧
        ce ≠ 0 ∧ Φe 0 = ce • (fun i => σ₀ (evalVec s (cuspPl σ₀ g) i)) ∧
        0 < ρe ∧ ρe < Re ∧ 0 < ρ₁e ∧ 0 ≤ Le ∧ 0 < mme ∧
        (∀ w ∈ closedBall (0 : ℂ) ρe, closedBall w ρ₁e ⊆ ball (0 : ℂ) Re ∧
          ∃ Ψw : ℂ → (Fin r × Fin r → ℂ),
            (∀ z ∈ closedBall w ρ₁e, ∀ q : Fin r × Fin r,
              Φe w q.1 * Φe z q.2 - Φe w q.2 * Φe z q.1 = (z - w) * Ψw z q) ∧
            (∀ z ∈ closedBall w ρ₁e, ∀ z' ∈ closedBall w ρ₁e, ‖Ψw z - Ψw z'‖ ≤ Le * ‖z - z'‖) ∧
            (∀ p : Fin r, ‖Φe w p‖ = ‖Φe w‖ → mme ≤ ‖fun i => Ψw w (p, i)‖)) ∧
        Ae ≤ Yr ∧ Real.exp (-2 * Real.pi * Yr / Subgroup.strictWidthInfty (conjGamma0 N g)) ≤ ρe / 2 ∧
        (∀ τ τ' : ℍ, Yr ≤ τ.im → Yr ≤ τ'.im → ∀ δ ∈ CongruenceSubgroup.Gamma0 N, δ • g • τ = g • τ' →
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) =
            Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ' : ℂ)) := by
    intro g
    have hw : 0 < Subgroup.strictWidthInfty (conjGamma0 N g) := strictWidthInfty_conjGamma0_pos g
    have hΓ : Subgroup.strictWidthInfty (conjGamma0 N g) ∈ (conjGamma0 N g).strictPeriods :=
      Subgroup.strictWidthInfty_mem_strictPeriods _

    obtain ⟨Φe, me, hΦA, hΦ0, -, A₀, hA₀, hVr⟩ := cusp_strong σ₀ s hs g hw hΓ
    have hV : ∀ τ : ℍ, A₀ ≤ τ.im →
        Φe (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) =
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me •
            Φint σ₀ s ((g • τ : ℍ) : ℂ) := fun τ hτ => by
      obtain ⟨hcont, hΦ⟩ := hVr τ hτ
      funext i
      rw [hΦ i, Pi.smul_apply, smul_eq_mul, Φint_eq_realize σ₀ s (g • τ) i (hcont i)]
    obtain ⟨ce, hce, hval⟩ := cusp_centre_prop D σ₀ s hs g hΦA hΦ0 hV

    have h1 : ∀ᶠ q in 𝓝 (0 : ℂ), ∀ i, AnalyticAt ℂ (fun q => Φe q i) q :=
      Filter.eventually_all.2 fun i => (hΦA i).eventually_analyticAt
    have hc : ContinuousAt Φe 0 := continuousAt_pi.2 fun i => (hΦA i).continuousAt
    have h2 : ∀ᶠ q in 𝓝 (0 : ℂ), Φe q ≠ 0 := hc.eventually_ne hΦ0
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
    set Re : ℝ := min ε (1/2) with hRe
    have hRe0 : 0 < Re := by positivity
    have hRe1 : Re < 1 := by have := min_le_right ε (1/2); rw [hRe]; linarith
    have hReA : ∀ i, AnalyticOnNhd ℂ (fun q => Φe q i) (ball 0 Re) := fun i q hq =>
      (hεb q (ball_subset_ball (min_le_left _ _) hq)).1 i
    have hReZ : ∀ q ∈ ball (0 : ℂ) Re, Φe q ≠ 0 := fun q hq => (hεb q (ball_subset_ball (min_le_left _ _) hq)).2

    have himm0 := cusp_chart_imm₂ σ₀ s hs g hΦA hΦ0 (fun τ hτ => (hVr τ hτ).2)
    obtain ⟨ρe, hρe, hρeR, himm⟩ := exists_ball_minor_ne_zero hRe0 hReA himm0
    obtain ⟨ρ₁e, Le, mme, hρ₁e, hLe, hmme, hnear⟩ := near_package isOpen_ball (fun i => (hReA i).differentiableOn)
      (isCompact_closedBall 0 ρe) (closedBall_subset_ball hρeR) (fun w hw' => hReZ w (closedBall_subset_ball hρeR hw')) himm

    obtain ⟨A₁, hA₁⟩ := norm_qParam_le_of_le_im hw (half_pos hRe0)
    obtain ⟨Y₀, hY₀⟩ := cusp_chart_inj (N := N) g
    set A₂ : ℝ := -(Subgroup.strictWidthInfty (conjGamma0 N g) * Real.log (ρe / 2)) / (2 * Real.pi) with hA₂
    set Ae : ℝ := max A₀ A₁ + 1 with hAe
    set Yr : ℝ := max (max Ae A₂) (Y₀ + 1) with hYr
    have hAeYr : Ae ≤ Yr := (le_max_left _ _).trans (le_max_left _ _)
    have hA₂Yr : A₂ ≤ Yr := (le_max_right _ _).trans (le_max_left _ _)
    have hY₀Yr : Y₀ < Yr := by have := le_max_right (max Ae A₂) (Y₀ + 1); rw [hYr]; linarith
    have hexpYr : Real.exp (-2 * Real.pi * Yr / Subgroup.strictWidthInfty (conjGamma0 N g)) ≤ ρe / 2 := by
      rw [← Real.exp_log (half_pos hρe), Real.exp_le_exp, div_le_iff₀ hw]
      have h3 := hA₂Yr
      rw [hA₂, div_le_iff₀ (by positivity)] at h3
      nlinarith [Real.pi_pos]
    refine ⟨Φe, me, Re, Ae, ρe, ρ₁e, Le, mme, Yr, ce, hRe0, hRe1, by positivity, hReA, hReZ,
      fun τ hτ => ⟨?_, hV τ ?_⟩, hce, hval, hρe, hρeR, hρ₁e, hLe, hmme, hnear, hAeYr, hexpYr,
      fun τ τ' hτ hτ' δ hδ heq => hY₀ τ τ' (hY₀Yr.trans_le hτ) (hY₀Yr.trans_le hτ') δ hδ heq⟩
    · rw [mem_ball, dist_zero_right]
      have := hA₁ τ (by rw [hAe] at hτ; linarith [le_max_right A₀ A₁])
      linarith
    · rw [hAe] at hτ; linarith [le_max_left A₀ A₁]
  choose Φe me Re Ae ρe ρ₁e Le mme Yr ce hkey using key
  exact ⟨Φe, me, Re, Ae, ρe, ρ₁e, Le, mme, Yr, ce, hkey⟩

theorem pchd_smul_right {t : ℂ} (ht : t ≠ 0) (y x : Fin r → ℂ) : pchd y (t • x) = pchd y x := by
  unfold pchd
  have : wedge y (t • x) = t • wedge y x := by
    funext q; simp only [wedge, Pi.smul_apply, smul_eq_mul]; ring
  rw [this, norm_smul, norm_smul, mul_left_comm, mul_div_mul_left _ _ (norm_ne_zero_iff.2 ht)]

omit [NeZero N] in

theorem exists_pos_le_of_isCompact {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {f : X → ℝ} (hf : ContinuousOn f S) (hpos : ∀ x ∈ S, 0 < f x) : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ S, m ≤ f x := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, fun x hx => by rw [h] at hx; exact hx.elim⟩
  · obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn h hf
    exact ⟨f x₀, hpos x₀ hx₀, fun x hx => isMinOn_iff.mp hmin x hx⟩

omit [NeZero N] in
theorem continuousOn_pchd' {X : Type*} [TopologicalSpace X] {S : Set X} {f g : X → (Fin r → ℂ)}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S) (hf0 : ∀ x ∈ S, f x ≠ 0) (hg0 : ∀ x ∈ S, g x ≠ 0) :
    ContinuousOn (fun x => pchd (f x) (g x)) S := by
  unfold pchd
  refine ContinuousOn.div ?_ (hf.norm.mul hg.norm) fun x hx =>
    mul_ne_zero (norm_ne_zero_iff.2 (hf0 x hx)) (norm_ne_zero_iff.2 (hg0 x hx))
  refine ContinuousOn.norm (continuousOn_pi.2 fun q => ?_)
  simp only [wedge]
  exact ((continuousOn_pi.1 hf q.1).mul (continuousOn_pi.1 hg q.2)).sub
    ((continuousOn_pi.1 hf q.2).mul (continuousOn_pi.1 hg q.1))

omit [NeZero N] in

theorem sep_small_base {K : Set ℂ} (hK : IsCompact K) {F : ℂ → (Fin r → ℂ)} (hF : ContinuousOn F K)
    (hF0 : ∀ z ∈ K, F z ≠ 0) {B : ℂ → (Fin r → ℂ)} {rb : ℝ} (hrb : 0 ≤ rb)
    (hB : ContinuousOn B (closedBall 0 rb)) (hB0 : ∀ u ∈ closedBall (0 : ℂ) rb, B u ≠ 0)
    (hpos : ∀ z ∈ K, 0 < pchd (F z) (B 0)) :
    ∃ rK mK : ℝ, 0 < rK ∧ 0 < mK ∧ ∀ z ∈ K, ∀ u ∈ closedBall (0 : ℂ) rb, ‖u‖ < rK → mK ≤ pchd (F z) (B u) := by
  have hP : ContinuousOn (fun x : ℂ × ℂ => pchd (F x.1) (B x.2)) (K ×ˢ closedBall (0 : ℂ) rb) :=
    continuousOn_pchd' (f := fun x : ℂ × ℂ => F x.1) (g := fun x : ℂ × ℂ => B x.2)
      (hF.comp continuousOn_fst fun x hx => hx.1) (hB.comp continuousOn_snd fun x hx => hx.2)
      (fun x hx => hF0 _ hx.1) (fun x hx => hB0 _ hx.2)
  have hP0 : ContinuousOn (fun z => pchd (F z) (B 0)) K :=
    continuousOn_pchd' (f := F) (g := fun _ => B 0) hF continuousOn_const hF0
      (fun _ _ => hB0 0 (mem_closedBall_self hrb))
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_isCompact hK hP0 hpos
  have hcpt : IsCompact (K ×ˢ closedBall (0 : ℂ) rb) := hK.prod (isCompact_closedBall _ _)
  obtain ⟨δ, hδ, hδP⟩ := Metric.uniformContinuousOn_iff.1 (hcpt.uniformContinuousOn_of_continuous hP) (m / 2) (half_pos hm)
  refine ⟨δ, m / 2, hδ, half_pos hm, fun z hz u hu hun => ?_⟩
  have hd : dist (z, u) (z, (0 : ℂ)) < δ := by
    rw [Prod.dist_eq, dist_self, dist_zero_right]
    exact max_lt hδ hun
  have h1 : dist (pchd (F z) (B u)) (pchd (F z) (B 0)) < m / 2 :=
    hδP (z, u) ⟨hz, hu⟩ (z, 0) ⟨hz, mem_closedBall_self hrb⟩ hd
  rw [Real.dist_eq, abs_lt] at h1
  have h2 : m ≤ pchd (F z) (B 0) := hmle z hz
  linarith [h1.1]

def CuspRel (N : ℕ) (s₁ s₀ : SL(2, ℤ)) : Prop :=
  ∃ δ ∈ CongruenceSubgroup.Gamma0 N, ∃ M : SL(2, ℤ), M 1 0 = 0 ∧ s₁ = δ * s₀ * M

theorem place_eq_of_prop (s : Fin r → FB N) (hs : IsEmbBasis N s) (σ : AlgebraicClosure ℚ →+* ℂ)
    (v w : Place (AlgebraicClosure ℚ) (FB N)) {c : ℂ}
    (h : (fun i => σ (evalVec s v i)) = c • (fun i => σ (evalVec s w i))) : v = w := by
  by_contra hvw
  apply ModularCurve.JZero.chordVec_ne_zero_of_ne N s hs v w hvw
  funext q
  have h1 := congrFun h q.1
  have h2 := congrFun h q.2
  simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
  apply σ.injective
  simp only [chordVec, Pi.zero_apply, map_sub, map_mul, map_zero, h1, h2]
  ring

theorem sep_core (D : ComplexPlaceDictionary N) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (σ₀ : AlgebraicClosure ℚ →+* ℂ) {Bx y₀ Y₁ Yb : ℝ} (hy₀ : 0 < y₀) (hYb1 : 1 < Yb) {Sb S₀ : Finset SL(2, ℤ)}
    (hcov : ∀ τ : ℍ, ∃ γ ∈ CongruenceSubgroup.Gamma0 N,
      (|(γ • τ).re| ≤ Bx ∧ y₀ ≤ (γ • τ).im ∧ (γ • τ).im ≤ Y₁) ∨
      (∃ σ₁ ∈ Sb, ∃ z ∈ ModularGroup.fd, Yb < z.im ∧ γ • τ = σ₁ • z))
    (hS₀ : ∀ g : SL(2, ℤ), ∃ γ ∈ CongruenceSubgroup.Gamma0 N, ∃ s₀ ∈ S₀, g = γ * s₀)
    (Φe : SL(2, ℤ) → ℂ → (Fin r → ℂ)) (me : SL(2, ℤ) → ℤ) (Re Ae ρe ρ₁e Le mme Yr : SL(2, ℤ) → ℝ) (ce : SL(2, ℤ) → ℂ)
    (hoffc : ∀ g, 0 < Re g ∧ Re g < 1 ∧ 0 < Ae g ∧
        (∀ i, AnalyticOnNhd ℂ (fun q => Φe g q i) (ball 0 (Re g))) ∧ (∀ q ∈ ball (0 : ℂ) (Re g), Φe g q ≠ 0) ∧
        (∀ τ : ℍ, Ae g ≤ τ.im →
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ∈ ball (0 : ℂ) (Re g) ∧
          Φe g (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) =
            Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me g •
              Φint σ₀ s ((g • τ : ℍ) : ℂ)) ∧
        ce g ≠ 0 ∧ Φe g 0 = ce g • (fun i => σ₀ (evalVec s (cuspPl σ₀ g) i)) ∧
        0 < ρe g ∧ ρe g < Re g ∧ 0 < ρ₁e g ∧ 0 ≤ Le g ∧ 0 < mme g ∧
        (∀ w ∈ closedBall (0 : ℂ) (ρe g), closedBall w (ρ₁e g) ⊆ ball (0 : ℂ) (Re g) ∧
          ∃ Ψw : ℂ → (Fin r × Fin r → ℂ),
            (∀ z ∈ closedBall w (ρ₁e g), ∀ q : Fin r × Fin r,
              Φe g w q.1 * Φe g z q.2 - Φe g w q.2 * Φe g z q.1 = (z - w) * Ψw z q) ∧
            (∀ z ∈ closedBall w (ρ₁e g), ∀ z' ∈ closedBall w (ρ₁e g), ‖Ψw z - Ψw z'‖ ≤ Le g * ‖z - z'‖) ∧
            (∀ p : Fin r, ‖Φe g w p‖ = ‖Φe g w‖ → mme g ≤ ‖fun i => Ψw w (p, i)‖)) ∧
        Ae g ≤ Yr g ∧
        Real.exp (-2 * Real.pi * Yr g / Subgroup.strictWidthInfty (conjGamma0 N g)) ≤ ρe g / 2 ∧
        (∀ τ τ' : ℍ, Yr g ≤ τ.im → Yr g ≤ τ'.im → ∀ δ ∈ CongruenceSubgroup.Gamma0 N, δ • g • τ = g • τ' →
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) =
            Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ' : ℂ)))
    (hYb : ∀ g ∈ S₀, Yr g + 1 ≤ Yb)
    (hinj : ∀ {γ₁ γ₂ : SL(2, ℤ)}, cuspPl (N := N) σ₀ γ₁ = cuspPl σ₀ γ₂ →
      ∃ δ ∈ CongruenceSubgroup.Gamma0 N, ∃ M : SL(2, ℤ), M 1 0 = 0 ∧ γ₂ = δ * γ₁ * M)
    (s₀ : SL(2, ℤ)) (hs₀ : s₀ ∈ S₀) {ρ₁' : ℝ} (hρ₁' : 0 < ρ₁')
    (hρ₁'R : Real.exp (-2 * Real.pi * Yb / Subgroup.strictWidthInfty (conjGamma0 N s₀)) + ρ₁' ≤
      Real.exp (-2 * Real.pi * Ae s₀ / Subgroup.strictWidthInfty (conjGamma0 N s₀))) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ u : ℂ, ‖u‖ ≤ Real.exp (-2 * Real.pi * Yb / Subgroup.strictWidthInfty (conjGamma0 N s₀)) →
      ∀ τ : ℍ, pchd (Φint σ₀ s (τ : ℂ)) (Φe s₀ u) < eta →
        (u ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ Φint σ₀ s (τ : ℂ) = c • Φe s₀ u) ∨
        (∃ z' ∈ closedBall u ρ₁', z' ≠ u ∧ ∃ t : ℂ, t ≠ 0 ∧ Φint σ₀ s (τ : ℂ) = t • Φe s₀ z') := by
  classical

  have hw : ∀ g : SL(2, ℤ), 0 < Subgroup.strictWidthInfty (conjGamma0 N g) := fun g => strictWidthInfty_conjGamma0_pos g
  set rb : SL(2, ℤ) → ℝ := fun g => Real.exp (-2 * Real.pi * Yb / Subgroup.strictWidthInfty (conjGamma0 N g)) with hrbdef
  have hrbpos : ∀ g, 0 < rb g := fun g => Real.exp_pos _
  have hYb0 : 0 < Yb := by linarith
  have hYrYb : ∀ g ∈ S₀, Yr g ≤ Yb := fun g hg => by linarith [hYb g hg]
  have hAeYb : ∀ g ∈ S₀, Ae g ≤ Yb := fun g hg => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAeYr, -, -⟩ := hoffc g
    exact hAeYr.trans (hYrYb g hg)
  have hnormq' : ∀ (g : SL(2, ℤ)) (τ : ℍ) (Y : ℝ), Y < τ.im →
      ‖Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)‖ <
        Real.exp (-2 * Real.pi * Y / Subgroup.strictWidthInfty (conjGamma0 N g)) := by
    intro g τ Y hY
    rw [Function.Periodic.norm_qParam, Real.exp_lt_exp, UpperHalfPlane.coe_im, div_lt_div_iff_of_pos_right (hw g)]
    nlinarith [Real.pi_pos]
  have hheight : ∀ (g : SL(2, ℤ)) (τ : ℍ) (Y : ℝ),
      ‖Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)‖ ≤
        Real.exp (-2 * Real.pi * Y / Subgroup.strictWidthInfty (conjGamma0 N g)) → Y ≤ τ.im := by
    intro g τ Y h
    rw [Function.Periodic.norm_qParam, Real.exp_le_exp, UpperHalfPlane.coe_im, div_le_div_iff_of_pos_right (hw g)] at h
    nlinarith [Real.pi_pos]
  have hqne : ∀ (g : SL(2, ℤ)) (z : ℂ), Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) z ≠ 0 :=
    fun g z => by simp only [Function.Periodic.qParam]; exact Complex.exp_ne_zero _

  have hlift : ∀ (g : SL(2, ℤ)) (u : ℂ), u ≠ 0 → ‖u‖ ≤ rb g →
      ∃ τu : ℍ, Yb ≤ τu.im ∧ Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τu : ℂ) = u := by
    intro g u hu0 hu
    set z₀ : ℂ := Function.Periodic.invQParam (Subgroup.strictWidthInfty (conjGamma0 N g)) u with hz₀
    have him : Yb ≤ z₀.im := by
      rw [hz₀, Function.Periodic.im_invQParam]
      have hlog : Real.log ‖u‖ ≤ -2 * Real.pi * Yb / Subgroup.strictWidthInfty (conjGamma0 N g) := by
        have := Real.log_le_log (norm_pos_iff.2 hu0) hu
        rwa [Real.log_exp] at this
      rw [le_div_iff₀ (hw g)] at hlog
      rw [show -Subgroup.strictWidthInfty (conjGamma0 N g) / (2 * Real.pi) * Real.log ‖u‖ =
          (-Real.log ‖u‖) * Subgroup.strictWidthInfty (conjGamma0 N g) / (2 * Real.pi) by ring, le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    have hpos : 0 < z₀.im := hYb0.trans_le him
    refine ⟨⟨z₀, hpos⟩, him, ?_⟩
    show Function.Periodic.qParam _ z₀ = u
    rw [hz₀]; exact Function.Periodic.qParam_right_inv (hw g).ne' hu0

  have hVal : ∀ g ∈ S₀, ∀ τ : ℍ, Ae g ≤ τ.im →
      Φe g (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) =
        Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me g • Φint σ₀ s ((g • τ : ℍ) : ℂ) := by
    intro g hg τ hτ
    obtain ⟨-, -, -, -, -, hV, -⟩ := hoffc g
    exact (hV τ hτ).2
  have hVal' : ∀ g ∈ S₀, ∀ τ : ℍ, Ae g ≤ τ.im →
      Φint σ₀ s ((g • τ : ℍ) : ℂ) =
        (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ (-me g)) •
          Φe g (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) := by
    intro g hg τ hτ
    rw [hVal g hg τ hτ, smul_smul, zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hqne g _)), one_smul]

  have hcuspidal : ∀ g : SL(2, ℤ), jB N ∉ (cuspPl (N := N) σ₀ g).toValuationSubring := by
    intro g hmem
    have h1 := (cuspPl (N := N) σ₀ g).ord_nonneg_of_mem hmem
    linarith [ord_jB_cuspPl_neg (N := N) σ₀ g]
  have hcusp_int : ∀ (g : SL(2, ℤ)) (τ : ℍ), ¬ ∃ c : ℂ, c ≠ 0 ∧ Φint σ₀ s (τ : ℂ) = c • Φe g 0 := by
    rintro g τ ⟨c, hc, h⟩
    obtain ⟨-, -, -, -, -, -, hce, hval, -⟩ := hoffc g
    exact PLBSEP.interior_ne_cusp_value D σ₀ s hs τ (cuspPl σ₀ g) (hcuspidal g)
      ⟨c * ce g, mul_ne_zero hc hce, by rw [h, hval, smul_smul]⟩
  have hint_cusp : ∀ (g : SL(2, ℤ)) (τ : ℍ), ¬ ∃ c : ℂ, c ≠ 0 ∧ Φe g 0 = c • Φint σ₀ s (τ : ℂ) := by
    rintro g τ ⟨c, hc, h⟩
    exact hcusp_int g τ ⟨c⁻¹, inv_ne_zero hc, by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩

  have hrbρe : ∀ g ∈ S₀, rb g ≤ ρe g / 2 := fun g hg => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hexpYr, -⟩ := hoffc g
    refine le_trans ?_ hexpYr
    show Real.exp _ ≤ Real.exp _
    rw [Real.exp_le_exp, div_le_div_iff_of_pos_right (hw g)]
    nlinarith [Real.pi_pos, hYrYb g hg]
  have hball : ∀ g ∈ S₀, closedBall (0 : ℂ) (rb g) ⊆ ball 0 (Re g) := fun g hg => by
    obtain ⟨-, -, -, -, -, -, -, -, hρe, hρeR, -⟩ := hoffc g
    exact (closedBall_subset_closedBall (by linarith [hrbρe g hg])).trans (closedBall_subset_ball hρeR)
  have hBc : ∀ g ∈ S₀, ContinuousOn (Φe g) (closedBall 0 (rb g)) := fun g hg => by
    obtain ⟨-, -, -, hReA, -⟩ := hoffc g
    exact continuousOn_pi.2 fun i => (hReA i).continuousOn.mono (hball g hg)
  have hB0 : ∀ g ∈ S₀, ∀ u ∈ closedBall (0 : ℂ) (rb g), Φe g u ≠ 0 := fun g hg u hu => by
    obtain ⟨-, -, -, -, hReZ, -⟩ := hoffc g
    exact hReZ u (hball g hg hu)
  have hmemrb : ∀ (g : SL(2, ℤ)) (u : ℂ), ‖u‖ ≤ rb g ↔ u ∈ closedBall (0 : ℂ) (rb g) := fun g u => by
    rw [mem_closedBall, dist_zero_right]

  have hprop_pts : ∀ g₁ ∈ S₀, ∀ g₀ ∈ S₀, ∀ τ₁ τ₀ : ℍ, Yb ≤ τ₁.im → Yb ≤ τ₀.im →
      (∃ c : ℂ, c ≠ 0 ∧ Φe g₁ (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g₁)) (τ₁ : ℂ)) =
        c • Φe g₀ (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g₀)) (τ₀ : ℂ))) →
      ∃ δ : CongruenceSubgroup.Gamma0 N, ((δ : SL(2, ℤ)) • (g₁ • τ₁) : ℍ) = g₀ • τ₀ := by
    rintro g₁ hg₁ g₀ hg₀ τ₁ τ₀ hτ₁ hτ₀ ⟨c, hc, hprop⟩
    refine (ComplexPlaceDictionary.pt_eq_pt_iff D (g₁ • τ₁) (g₀ • τ₀)).1 (PLBSEP.inj_all D σ₀ s hs _ _ ?_)
    refine ⟨Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g₁)) (τ₁ : ℂ) ^ (-me g₁) * c *
        Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g₀)) (τ₀ : ℂ) ^ (me g₀),
      mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (hqne g₁ _)) hc) (zpow_ne_zero _ (hqne g₀ _)), ?_⟩
    rw [hVal' g₁ hg₁ τ₁ ((hAeYb g₁ hg₁).trans hτ₁), hprop, hVal g₀ hg₀ τ₀ ((hAeYb g₀ hg₀).trans hτ₀), smul_smul, smul_smul]

  have hsame : ∀ τ₁ τ₀ : ℍ, Yb ≤ τ₁.im → Yb ≤ τ₀.im →
      (∃ c : ℂ, c ≠ 0 ∧ Φe s₀ (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ₁ : ℂ)) =
        c • Φe s₀ (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ₀ : ℂ))) →
      Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ₁ : ℂ) =
        Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ₀ : ℂ) := by
    intro τ₁ τ₀ hτ₁ hτ₀ h
    obtain ⟨δ, hδ⟩ := hprop_pts s₀ hs₀ s₀ hs₀ τ₁ τ₀ hτ₁ hτ₀ h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hINJ⟩ := hoffc s₀
    exact hINJ τ₁ τ₀ ((hYrYb s₀ hs₀).trans hτ₁) ((hYrYb s₀ hs₀).trans hτ₀) δ δ.2 hδ

  have hdiff : ∀ g₁ ∈ S₀, ∀ τ₁ τ₀ : ℍ, Yb ≤ τ₁.im → Yb ≤ τ₀.im →
      (∃ c : ℂ, c ≠ 0 ∧ Φe g₁ (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g₁)) (τ₁ : ℂ)) =
        c • Φe s₀ (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ₀ : ℂ))) →
      CuspRel N g₁ s₀ := by
    intro g₁ hg₁ τ₁ τ₀ hτ₁ hτ₀ h
    obtain ⟨δ, hδ⟩ := hprop_pts g₁ hg₁ s₀ hs₀ τ₁ τ₀ hτ₁ hτ₀ h
    set M : SL(2, ℤ) := s₀⁻¹ * (δ : SL(2, ℤ)) * g₁ with hMdef
    have hMτ : M • τ₁ = τ₀ := by
      rw [hMdef, mul_smul, mul_smul, hδ, inv_smul_smul]
    have hM : M 1 0 = 0 :=
      apply_one_zero_eq_zero_of_im_gt M τ₁ (hYb1.trans_le hτ₁) (by rw [hMτ]; exact hYb1.trans_le hτ₀)
    refine ⟨((δ⁻¹ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)), (δ⁻¹).2, M, hM, ?_⟩
    rw [hMdef, Subgroup.coe_inv]
    group

  set K : Set ℂ := {z : ℂ | |z.re| ≤ Bx ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁} with hK
  have hKc : IsCompact K := isCompact_box' Bx y₀ Y₁
  have hKim : ∀ z ∈ K, 0 < z.im := fun z hz => hy₀.trans_le hz.2.1
  have hFc : ContinuousOn (Φint σ₀ s) K := by
    intro z hz
    have hA := (interior_chart' D σ₀ s hs z (hKim z hz)).1
    exact ((continuousOn_pi.2 fun i => (hA i).continuousOn).continuousAt (ball_mem_nhds z (by linarith [hKim z hz]))).continuousWithinAt
  have hF0 : ∀ z ∈ K, Φint σ₀ s z ≠ 0 := fun z hz =>
    (interior_chart' D σ₀ s hs z (hKim z hz)).2.1 z (mem_ball_self (by linarith [hKim z hz]))
  have hposK : ∀ z ∈ K, 0 < pchd (Φint σ₀ s z) (Φe s₀ 0) := by
    intro z hz
    refine pchd_pos_of_not_prop (hF0 z hz) (hB0 s₀ hs₀ 0 (mem_closedBall_self (hrbpos s₀).le)) ?_
    exact hcusp_int s₀ ⟨z, hKim z hz⟩
  obtain ⟨rK, mK, hrK, hmK, hsmall⟩ := sep_small_base hKc hFc hF0 (hrbpos s₀).le (hBc s₀ hs₀) (hB0 s₀ hs₀) hposK

  set Wann : Set ℂ := {u : ℂ | rK ≤ ‖u‖ ∧ ‖u‖ ≤ rb s₀} with hWann
  have hWc : IsCompact Wann := by
    have : Wann = closedBall (0 : ℂ) (rb s₀) ∩ {u | rK ≤ ‖u‖} := by
      ext u; simp only [hWann, Set.mem_setOf_eq, Set.mem_inter_iff, mem_closedBall, dist_zero_right]; tauto
    rw [this]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hWsub : Wann ⊆ closedBall 0 (rb s₀) := fun u hu => (hmemrb s₀ u).1 hu.2
  set κ : ℍ → ℂ := fun τ => Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (((s₀⁻¹ • τ : ℍ)) : ℂ)
    with hκ
  have hκc : Continuous κ :=
    Function.Periodic.differentiable_qParam.continuous.comp
      (UpperHalfPlane.continuous_coe.comp (PLBSEP.continuous_smul_SL s₀⁻¹))
  have hBΦ : ∀ u ∈ Wann, ∃ w : ℍ, κ w = u ∧ ∃ c : ℂ, c ≠ 0 ∧ Φe s₀ u = c • Φint σ₀ s (w : ℂ) := by
    intro u hu
    have hu0 : u ≠ 0 := fun h => by have h1 := hu.1; rw [h, norm_zero] at h1; linarith
    obtain ⟨τu, hτu, hqu⟩ := hlift s₀ u hu0 hu.2
    refine ⟨s₀ • τu, ?_, _, zpow_ne_zero (me s₀) hu0, ?_⟩
    · show Function.Periodic.qParam _ (((s₀⁻¹ • (s₀ • τu) : ℍ)) : ℂ) = u
      rw [inv_smul_smul]; exact hqu
    · have := hVal s₀ hs₀ τu ((hAeYb s₀ hs₀).trans hτu)
      rw [hqu] at this
      exact this
  have hΛc : ContinuousOn (fun z => ((UpperHalfPlane.ofComplex z : ℍ) : ℂ)) K := by
    intro z hz
    refine ContinuousAt.continuousWithinAt ?_
    have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    exact continuousAt_id.congr (by
      filter_upwards [hopen.mem_nhds (hKim z hz)] with y hy
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hy]; try rfl)
  have hcoeK : ∀ z ∈ K, ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hKim z hz)]; try rfl
  obtain ⟨eta₂, heta₂, hengine⟩ := PLBSEP.unifsep_core D σ₀ s hs (fun _ : Unit => K) (fun _ => hKc)
    (fun _ z => UpperHalfPlane.ofComplex z) (fun _ => hΛc)
    (fun _ => Φint σ₀ s) (fun _ => hFc) (fun _ => hF0)
    (fun _ z hz => ⟨1, one_ne_zero, by rw [one_smul, hcoeK z hz]⟩)
    Wann hWc (Φe s₀) ((hBc s₀ hs₀).mono hWsub) (fun u hu => hB0 s₀ hs₀ u (hWsub hu)) κ hκc hBΦ hρ₁'

  set P : Set (ℂ × ℂ) := {x | ‖x.1‖ ≤ rb s₀ ∧ ‖x.2‖ ≤ rb s₀ ∧ ρ₁' ≤ ‖x.1 - x.2‖} with hP
  have hPc : IsCompact P := by
    have : P = (closedBall (0 : ℂ) (rb s₀) ×ˢ closedBall (0 : ℂ) (rb s₀)) ∩ {x | ρ₁' ≤ ‖x.1 - x.2‖} := by
      ext x
      simp only [hP, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, mem_closedBall, dist_zero_right]
      tauto
    rw [this]
    exact ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right
      (isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm)
  have hPcont : ContinuousOn (fun x : ℂ × ℂ => pchd (Φe s₀ x.1) (Φe s₀ x.2)) P :=
    continuousOn_pchd' (f := fun x : ℂ × ℂ => Φe s₀ x.1) (g := fun x : ℂ × ℂ => Φe s₀ x.2)
      ((hBc s₀ hs₀).comp continuousOn_fst fun x hx => (hmemrb s₀ _).1 hx.1)
      ((hBc s₀ hs₀).comp continuousOn_snd fun x hx => (hmemrb s₀ _).1 hx.2.1)
      (fun x hx => hB0 s₀ hs₀ _ ((hmemrb s₀ _).1 hx.1)) (fun x hx => hB0 s₀ hs₀ _ ((hmemrb s₀ _).1 hx.2.1))

  have hpos_own : ∀ q u : ℂ, ‖q‖ ≤ rb s₀ → ‖u‖ ≤ rb s₀ → q ≠ u → 0 < pchd (Φe s₀ q) (Φe s₀ u) := by
    intro q u hq hu hne
    refine pchd_pos_of_not_prop (hB0 s₀ hs₀ q ((hmemrb s₀ q).1 hq)) (hB0 s₀ hs₀ u ((hmemrb s₀ u).1 hu)) ?_
    rintro ⟨c, hc, hprop⟩
    by_cases hq0 : q = 0
    · by_cases hu0 : u = 0
      · exact hne (hq0.trans hu0.symm)
      · obtain ⟨τu, hτu, hqτ⟩ := hlift s₀ u hu0 hu
        apply hint_cusp s₀ (s₀ • τu)
        have hVu := hVal s₀ hs₀ τu ((hAeYb s₀ hs₀).trans hτu)
        rw [hqτ] at hVu
        refine ⟨c * u ^ me s₀, mul_ne_zero hc (zpow_ne_zero _ hu0), ?_⟩
        rw [← hq0, hprop, hVu, smul_smul]
    · by_cases hu0 : u = 0
      · obtain ⟨τq, hτq, hqτ⟩ := hlift s₀ q hq0 hq
        apply hint_cusp s₀ (s₀ • τq)
        have hVq := hVal s₀ hs₀ τq ((hAeYb s₀ hs₀).trans hτq)
        rw [hqτ] at hVq
        refine ⟨c⁻¹ * q ^ me s₀, mul_ne_zero (inv_ne_zero hc) (zpow_ne_zero _ hq0), ?_⟩
        rw [← hu0, ← smul_smul, ← hVq, hprop, smul_smul, inv_mul_cancel₀ hc, one_smul]
      · obtain ⟨τq, hτq, hqτ⟩ := hlift s₀ q hq0 hq
        obtain ⟨τu, hτu, huτ⟩ := hlift s₀ u hu0 hu
        apply hne
        rw [← hqτ, ← huτ]
        refine hsame τq τu hτq hτu ⟨c, hc, ?_⟩
        rw [hqτ, huτ]; exact hprop
  obtain ⟨m₃, hm₃, hm₃le⟩ := exists_pos_le_of_isCompact hPc hPcont (by
    rintro ⟨q, u⟩ ⟨hq, hu, hqu⟩
    refine hpos_own q u hq hu fun h => ?_
    rw [h, sub_self, norm_zero] at hqu
    linarith)

  have hpos_other : ∀ g₁ ∈ S₀, ¬ CuspRel N g₁ s₀ → ∀ q u : ℂ, ‖q‖ ≤ rb g₁ → ‖u‖ ≤ rb s₀ →
      0 < pchd (Φe g₁ q) (Φe s₀ u) := by
    intro g₁ hg₁ hrel q u hq hu
    refine pchd_pos_of_not_prop (hB0 g₁ hg₁ q ((hmemrb g₁ q).1 hq)) (hB0 s₀ hs₀ u ((hmemrb s₀ u).1 hu)) ?_
    rintro ⟨c, hc, hprop⟩
    by_cases hq0 : q = 0
    · by_cases hu0 : u = 0
      ·
        obtain ⟨-, -, -, -, -, -, hce₁, hval₁, -⟩ := hoffc g₁
        obtain ⟨-, -, -, -, -, -, hce₀, hval₀, -⟩ := hoffc s₀
        rw [hq0, hu0, hval₁, hval₀, smul_smul] at hprop
        have hpl : cuspPl (N := N) σ₀ g₁ = cuspPl σ₀ s₀ := by
          refine place_eq_of_prop s hs σ₀ _ _ (c := (ce g₁)⁻¹ * (c * ce s₀)) ?_
          rw [← smul_smul, ← hprop, smul_smul, inv_mul_cancel₀ hce₁, one_smul]
        obtain ⟨δ, hδ, M, hM, hg⟩ := hinj hpl.symm
        exact hrel ⟨δ, hδ, M, hM, hg⟩
      · obtain ⟨τu, hτu, hqτ⟩ := hlift s₀ u hu0 hu
        apply hint_cusp g₁ (s₀ • τu)
        have hVu := hVal s₀ hs₀ τu ((hAeYb s₀ hs₀).trans hτu)
        rw [hqτ] at hVu
        refine ⟨c * u ^ me s₀, mul_ne_zero hc (zpow_ne_zero _ hu0), ?_⟩
        rw [← hq0, hprop, hVu, smul_smul]
    · by_cases hu0 : u = 0
      · obtain ⟨τq, hτq, hqτ⟩ := hlift g₁ q hq0 hq
        apply hint_cusp s₀ (g₁ • τq)
        have hVq := hVal g₁ hg₁ τq ((hAeYb g₁ hg₁).trans hτq)
        rw [hqτ] at hVq
        refine ⟨c⁻¹ * q ^ me g₁, mul_ne_zero (inv_ne_zero hc) (zpow_ne_zero _ hq0), ?_⟩
        rw [← hu0, ← smul_smul, ← hVq, hprop, smul_smul, inv_mul_cancel₀ hc, one_smul]
      · obtain ⟨τq, hτq, hqτ⟩ := hlift g₁ q hq0 hq
        obtain ⟨τu, hτu, huτ⟩ := hlift s₀ u hu0 hu
        refine hrel (hdiff g₁ hg₁ τq τu hτq hτu ⟨c, hc, ?_⟩)
        rw [hqτ, huτ]; exact hprop
  have h4 : ∀ g₁ : SL(2, ℤ), ∃ m : ℝ, 0 < m ∧ (g₁ ∈ S₀ → ¬ CuspRel N g₁ s₀ →
      ∀ q u : ℂ, ‖q‖ ≤ rb g₁ → ‖u‖ ≤ rb s₀ → m ≤ pchd (Φe g₁ q) (Φe s₀ u)) := by
    intro g₁
    by_cases h : g₁ ∈ S₀ ∧ ¬ CuspRel N g₁ s₀
    · have hQc : IsCompact (closedBall (0 : ℂ) (rb g₁) ×ˢ closedBall (0 : ℂ) (rb s₀)) :=
        (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
      have hQcont : ContinuousOn (fun x : ℂ × ℂ => pchd (Φe g₁ x.1) (Φe s₀ x.2))
          (closedBall (0 : ℂ) (rb g₁) ×ˢ closedBall (0 : ℂ) (rb s₀)) :=
        continuousOn_pchd' (f := fun x : ℂ × ℂ => Φe g₁ x.1) (g := fun x : ℂ × ℂ => Φe s₀ x.2)
          ((hBc g₁ h.1).comp continuousOn_fst fun x hx => hx.1)
          ((hBc s₀ hs₀).comp continuousOn_snd fun x hx => hx.2)
          (fun x hx => hB0 g₁ h.1 _ hx.1) (fun x hx => hB0 s₀ hs₀ _ hx.2)
      obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_isCompact hQc hQcont (by
        rintro ⟨q, u⟩ ⟨hq, hu⟩
        exact hpos_other g₁ h.1 h.2 q u ((hmemrb g₁ q).2 hq) ((hmemrb s₀ u).2 hu))
      exact ⟨m, hm, fun _ _ q u hq hu => hmle (q, u) ⟨(hmemrb g₁ q).1 hq, (hmemrb s₀ u).1 hu⟩⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose m₄ hm₄ hm₄le using h4

  set eta : ℝ := min (min mK eta₂) (min m₃ (∑ g ∈ S₀, (m₄ g)⁻¹ + 1)⁻¹) with heta
  have heta4pos : 0 < (∑ g ∈ S₀, (m₄ g)⁻¹ + 1)⁻¹ :=
    inv_pos.2 (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun g _ => (inv_pos.2 (hm₄ g)).le) one_pos)
  have hetapos : 0 < eta := lt_min (lt_min hmK heta₂) (lt_min hm₃ heta4pos)
  have hetaK : eta ≤ mK := (min_le_left _ _).trans (min_le_left _ _)
  have heta2 : eta ≤ eta₂ := (min_le_left _ _).trans (min_le_right _ _)
  have heta3 : eta ≤ m₃ := (min_le_right _ _).trans (min_le_left _ _)
  have heta4 : ∀ g ∈ S₀, eta ≤ m₄ g := by
    intro g hg
    refine ((min_le_right _ _).trans (min_le_right _ _)).trans ?_
    rw [← inv_inv (m₄ g)]
    refine inv_anti₀ (inv_pos.2 (hm₄ g)) ?_
    have : (m₄ g)⁻¹ ≤ ∑ g ∈ S₀, (m₄ g)⁻¹ :=
      Finset.single_le_sum (f := fun g => (m₄ g)⁻¹) (fun g _ => (inv_pos.2 (hm₄ g)).le) hg
    linarith
  refine ⟨eta, hetapos, fun u hu τ hlt => ?_⟩
  have hu' : u ∈ closedBall (0 : ℂ) (rb s₀) := (hmemrb s₀ u).1 hu

  obtain ⟨γ, hγ, hγτ⟩ := hcov τ
  have hΦγ : Φint σ₀ s (τ : ℂ) = Φint σ₀ s (((((⟨γ, hγ⟩ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • τ : ℍ)) : ℂ) :=
    (Φint_smul D σ₀ s hs ⟨γ, hγ⟩ τ).symm
  rw [hΦγ] at hlt ⊢
  rcases hγτ with hbox | ⟨σ₁, hσ₁, z₁, -, hz₁, hγz⟩
  ·
    set z : ℂ := ((((⟨γ, hγ⟩ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • τ : ℍ) : ℂ) with hzdef
    have hzK : z ∈ K := hbox
    by_cases hun : ‖u‖ < rK
    · exfalso
      have := hsmall z hzK u hu' hun
      linarith
    · push_neg at hun
      have huW : u ∈ Wann := ⟨hun, hu⟩
      have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hun; linarith
      obtain ⟨γ', hγ'⟩ := hengine () z hzK u huW (hlt.trans_le heta2)

      set τ' : ℍ := s₀⁻¹ • (((γ' : SL(2, ℤ)) • UpperHalfPlane.ofComplex z : ℍ)) with hτ'
      have hz' : κ (((γ' : SL(2, ℤ)) • UpperHalfPlane.ofComplex z : ℍ)) =
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ' : ℂ) := rfl
      rw [hz'] at hγ'
      set z' : ℂ := Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ' : ℂ) with hz'def
      have hz'norm : ‖z'‖ ≤ Real.exp (-2 * Real.pi * Ae s₀ / Subgroup.strictWidthInfty (conjGamma0 N s₀)) := by
        have h1 : ‖z'‖ ≤ ‖u‖ + dist z' u := by
          have := norm_le_norm_add_norm_sub' z' u
          rwa [← dist_eq_norm] at this
        linarith [hγ'.le]
      have hAeτ' : Ae s₀ ≤ τ'.im := hheight s₀ τ' (Ae s₀) hz'norm
      have hval' : Φint σ₀ s z = (z' ^ (-me s₀)) • Φe s₀ z' := by
        have := hVal' s₀ hs₀ τ' hAeτ'
        rw [hτ', smul_inv_smul, Φint_smul D σ₀ s hs γ', hcoeK z hzK] at this
        exact this
      by_cases hzu : z' = u
      · left
        refine ⟨hu0, z' ^ (-me s₀), zpow_ne_zero _ (hqne s₀ _), ?_⟩
        rw [← hzu]; exact hval'
      · right
        exact ⟨z', mem_closedBall.2 hγ'.le, hzu, z' ^ (-me s₀), zpow_ne_zero _ (hqne s₀ _), hval'⟩
  ·
    obtain ⟨γ₁, hγ₁, g₁, hg₁, rfl⟩ := hS₀ σ₁
    have hΦ1 : Φint σ₀ s (((((⟨γ, hγ⟩ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • τ : ℍ)) : ℂ) =
        Φint σ₀ s ((g₁ • z₁ : ℍ) : ℂ) := by
      have : ((((⟨γ, hγ⟩ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • τ : ℍ)) =
          (((⟨γ₁, hγ₁⟩ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • (g₁ • z₁) : ℍ) := by
        rw [← mul_smul]; exact hγz
      rw [this, Φint_smul D σ₀ s hs ⟨γ₁, hγ₁⟩ (g₁ • z₁)]
    rw [hΦ1] at hlt ⊢
    by_cases hrel : CuspRel N g₁ s₀
    ·
      obtain ⟨δ, hδ, M, hM, hg₁eq⟩ := hrel
      set z₂ : ℍ := M • z₁ with hz₂
      have hz₂im : Yb < z₂.im := by rw [hz₂, im_smul_of_apply_one_zero_eq_zero M hM z₁]; exact hz₁
      have hΦ2 : Φint σ₀ s ((g₁ • z₁ : ℍ) : ℂ) = Φint σ₀ s ((s₀ • z₂ : ℍ) : ℂ) := by
        have : (g₁ • z₁ : ℍ) = (((⟨δ, hδ⟩ : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) • (s₀ • z₂) : ℍ) := by
          rw [hg₁eq, mul_smul, mul_smul]
        rw [this, Φint_smul D σ₀ s hs ⟨δ, hδ⟩ (s₀ • z₂)]
      rw [hΦ2] at hlt ⊢
      set q : ℂ := Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (z₂ : ℂ) with hqdef
      have hqn : ‖q‖ < rb s₀ := hnormq' s₀ z₂ Yb hz₂im
      have hq0 : q ≠ 0 := hqne s₀ _
      have hvq : Φint σ₀ s ((s₀ • z₂ : ℍ) : ℂ) = (q ^ (-me s₀)) • Φe s₀ q :=
        hVal' s₀ hs₀ z₂ ((hAeYb s₀ hs₀).trans hz₂im.le)
      by_cases hd : ρ₁' ≤ ‖q - u‖
      · exfalso
        have h1 := hm₃le (q, u) ⟨hqn.le, hu, hd⟩
        rw [hvq, pchd_smul_left (zpow_ne_zero _ hq0)] at hlt
        dsimp only at h1
        linarith
      · push_neg at hd
        by_cases hqu : q = u
        · left
          refine ⟨hqu ▸ hq0, q ^ (-me s₀), zpow_ne_zero _ hq0, ?_⟩
          rw [← hqu]; exact hvq
        · right
          refine ⟨q, ?_, hqu, q ^ (-me s₀), zpow_ne_zero _ hq0, hvq⟩
          rw [mem_closedBall, dist_eq_norm]; exact hd.le
    ·
      exfalso
      set q : ℂ := Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g₁)) (z₁ : ℂ) with hqdef
      have hqn : ‖q‖ < rb g₁ := hnormq' g₁ z₁ Yb hz₁
      have hq0 : q ≠ 0 := hqne g₁ _
      have hvq : Φint σ₀ s ((g₁ • z₁ : ℍ) : ℂ) = (q ^ (-me g₁)) • Φe g₁ q :=
        hVal' g₁ hg₁ z₁ ((hAeYb g₁ hg₁).trans hz₁.le)
      have h1 := hm₄le g₁ hg₁ hrel q u hqn.le hu
      rw [hvq, pchd_smul_left (zpow_ne_zero _ hq0)] at hlt
      linarith [heta4 g₁ hg₁]

theorem base_off_box₂ (D : ComplexPlaceDictionary N) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (σ₀ : AlgebraicClosure ℚ →+* ℂ)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (ρ R : ι → ℝ) (Φ : ι → ℂ → (Fin r → ℂ)) (lift : ι → ℂ → ℍ) (Dom : ι → Set ℂ)
    (hA : ∀ j i, AnalyticOnNhd ℂ (fun z => Φ j z i) (ball (c j) (R j)))
    (hZ : ∀ j, ∀ z ∈ ball (c j) (R j), Φ j z ≠ 0) (hρR : ∀ j, ρ j < R j)
    (hrep : ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ j, ∀ z ∈ closedBall (c j) (ρ j), z ∈ Dom j → ∃ t : ℂ, t ≠ 0 ∧ Φ j z = t • Φint σ s ((lift j z : ℍ) : ℂ))
    (Bx y₀ Y₁ Yb : ℝ) (hy₀ : 0 < y₀) (hYb1 : 1 < Yb) {Sb : Finset SL(2, ℤ)}
    (hcov : ∀ τ : ℍ, ∃ γ ∈ CongruenceSubgroup.Gamma0 N,
      (|(γ • τ).re| ≤ Bx ∧ y₀ ≤ (γ • τ).im ∧ (γ • τ).im ≤ Y₁) ∨
      (∃ σ₁ ∈ Sb, ∃ z ∈ ModularGroup.fd, Yb < z.im ∧ γ • τ = σ₁ • z))
    {S₀ : Finset SL(2, ℤ)} (hS₀ : ∀ g : SL(2, ℤ), ∃ γ ∈ CongruenceSubgroup.Gamma0 N, ∃ s₀ ∈ S₀, g = γ * s₀)
    (Φe : SL(2, ℤ) → ℂ → (Fin r → ℂ)) (me : SL(2, ℤ) → ℤ) (Re Ae ρe ρ₁e Le mme Yr : SL(2, ℤ) → ℝ) (ce : SL(2, ℤ) → ℂ)
    (hoffc : ∀ g, 0 < Re g ∧ Re g < 1 ∧ 0 < Ae g ∧
        (∀ i, AnalyticOnNhd ℂ (fun q => Φe g q i) (ball 0 (Re g))) ∧ (∀ q ∈ ball (0 : ℂ) (Re g), Φe g q ≠ 0) ∧
        (∀ τ : ℍ, Ae g ≤ τ.im →
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ∈ ball (0 : ℂ) (Re g) ∧
          Φe g (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)) =
            Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) ^ me g •
              Φint σ₀ s ((g • τ : ℍ) : ℂ)) ∧
        ce g ≠ 0 ∧ Φe g 0 = ce g • (fun i => σ₀ (evalVec s (cuspPl σ₀ g) i)) ∧
        0 < ρe g ∧ ρe g < Re g ∧ 0 < ρ₁e g ∧ 0 ≤ Le g ∧ 0 < mme g ∧
        (∀ w ∈ closedBall (0 : ℂ) (ρe g), closedBall w (ρ₁e g) ⊆ ball (0 : ℂ) (Re g) ∧
          ∃ Ψw : ℂ → (Fin r × Fin r → ℂ),
            (∀ z ∈ closedBall w (ρ₁e g), ∀ q : Fin r × Fin r,
              Φe g w q.1 * Φe g z q.2 - Φe g w q.2 * Φe g z q.1 = (z - w) * Ψw z q) ∧
            (∀ z ∈ closedBall w (ρ₁e g), ∀ z' ∈ closedBall w (ρ₁e g), ‖Ψw z - Ψw z'‖ ≤ Le g * ‖z - z'‖) ∧
            (∀ p : Fin r, ‖Φe g w p‖ = ‖Φe g w‖ → mme g ≤ ‖fun i => Ψw w (p, i)‖)) ∧
        Ae g ≤ Yr g ∧
        Real.exp (-2 * Real.pi * Yr g / Subgroup.strictWidthInfty (conjGamma0 N g)) ≤ ρe g / 2 ∧
        (∀ τ τ' : ℍ, Yr g ≤ τ.im → Yr g ≤ τ'.im → ∀ δ ∈ CongruenceSubgroup.Gamma0 N, δ • g • τ = g • τ' →
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ) =
            Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ' : ℂ)))
    (hYb : ∀ g ∈ S₀, Yr g + 1 ≤ Yb) :
    ∃ (ρ₁ L m₀ : ℝ), 0 < ρ₁ ∧ 0 ≤ L ∧ 0 < m₀ ∧
    ∀ ρ₁' : ℝ, 0 < ρ₁' → ρ₁' ≤ ρ₁ → ∃ eta : ℝ, 0 < eta ∧
    ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
    ∀ v : Place (AlgebraicClosure ℚ) (FB N),
      (¬ ∃ τ : ℍ, v.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) ∧
          (|(τ : ℂ).re| ≤ Bx ∧ y₀ ≤ (τ : ℂ).im ∧ (τ : ℂ).im ≤ Y₁)) →
      ∃ (Φb : ℂ → (Fin r → ℂ)) (zb : ℂ) (Ψb : ℂ → (Fin r × Fin r → ℂ)) (p : Fin r) (tb : ℂ),
        tb ≠ 0 ∧ Φb zb = tb • (fun i => σ (evalVec s v i)) ∧ ‖Φb zb p‖ = ‖Φb zb‖ ∧
        (∀ z ∈ closedBall zb ρ₁, ∀ q : Fin r × Fin r,
          Φb zb q.1 * Φb z q.2 - Φb zb q.2 * Φb z q.1 = (z - zb) * Ψb z q) ∧
        (∀ z ∈ closedBall zb ρ₁, ∀ z' ∈ closedBall zb ρ₁, ‖Ψb z - Ψb z'‖ ≤ L * ‖z - z'‖) ∧
        m₀ ≤ ‖fun i => Ψb zb (p, i)‖ ∧
        (∀ e : Fin r → AlgebraicClosure ℚ, linSec s (pencilAlg s v p e) ≠ 0 →
          (∀ z ∈ closedBall zb ρ₁', ∑ i, σ (e i) * Ψb z (p, i) ≠ 0) →
          v.ord (linSec s (pencilAlg s v p e)) + embDivisor N v = 1) ∧
        (∀ j, ∀ z ∈ closedBall (c j) (ρ j), z ∈ Dom j → pchd (Φ j z) (Φb zb) < eta →
          v.toValuationSubring = (D.pt (lift j z)).toValuationSubring.comap (phi N σ) ∨
          ∃ z' ∈ closedBall zb ρ₁', z' ≠ zb ∧ ∃ t : ℂ, t ≠ 0 ∧ Φ j z = t • Φb z') := by
  classical
  have hr := r_pos N s hs
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hw : ∀ g : SL(2, ℤ), 0 < Subgroup.strictWidthInfty (conjGamma0 N g) := fun g => strictWidthInfty_conjGamma0_pos g
  set rb : SL(2, ℤ) → ℝ := fun g => Real.exp (-2 * Real.pi * Yb / Subgroup.strictWidthInfty (conjGamma0 N g)) with hrbdef
  set RA : SL(2, ℤ) → ℝ := fun g => Real.exp (-2 * Real.pi * Ae g / Subgroup.strictWidthInfty (conjGamma0 N g)) with hRAdef
  have hqne : ∀ (g : SL(2, ℤ)) (z : ℂ), Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) z ≠ 0 :=
    fun g z => by simp only [Function.Periodic.qParam]; exact Complex.exp_ne_zero _
  have hYrYb : ∀ g ∈ S₀, Yr g < Yb := fun g hg => by linarith [hYb g hg]
  have hmargin : ∀ g ∈ S₀, 0 < RA g - rb g := fun g hg => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAeYr, -, -⟩ := hoffc g
    have : rb g < RA g := by
      show Real.exp _ < Real.exp _
      rw [Real.exp_lt_exp, div_lt_div_iff_of_pos_right (hw g)]
      nlinarith [Real.pi_pos, hYrYb g hg]
    linarith
  have hrbρe : ∀ g ∈ S₀, rb g ≤ ρe g / 2 := fun g hg => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hexpYr, -⟩ := hoffc g
    refine le_trans ?_ hexpYr
    show Real.exp _ ≤ Real.exp _
    rw [Real.exp_le_exp, div_le_div_iff_of_pos_right (hw g)]
    nlinarith [Real.pi_pos, hYrYb g hg]
  have hnormq' : ∀ (g : SL(2, ℤ)) (τ : ℍ) (Y : ℝ), Y < τ.im →
      ‖Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N g)) (τ : ℂ)‖ <
        Real.exp (-2 * Real.pi * Y / Subgroup.strictWidthInfty (conjGamma0 N g)) := by
    intro g τ Y hY
    rw [Function.Periodic.norm_qParam, Real.exp_lt_exp, UpperHalfPlane.coe_im, div_lt_div_iff_of_pos_right (hw g)]
    nlinarith [Real.pi_pos]

  set ρ₁ : ℝ := min (∑ g ∈ S₀, (ρ₁e g)⁻¹ + 1)⁻¹ (∑ g ∈ S₀, (RA g - rb g)⁻¹ + 1)⁻¹ with hρ₁def
  have hpos1 : 0 < (∑ g ∈ S₀, (ρ₁e g)⁻¹ + 1)⁻¹ := by
    refine inv_pos.2 (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun g _ => ?_) one_pos)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hρ₁e, -⟩ := hoffc g
    exact (inv_pos.2 hρ₁e).le
  have hpos2 : 0 < (∑ g ∈ S₀, (RA g - rb g)⁻¹ + 1)⁻¹ :=
    inv_pos.2 (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun g hg => (inv_pos.2 (hmargin g hg)).le) one_pos)
  have hρ₁pos : 0 < ρ₁ := lt_min hpos1 hpos2
  have hρ₁le : ∀ g ∈ S₀, ρ₁ ≤ ρ₁e g := by
    intro g hg
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hρ₁e, -⟩ := hoffc g
    refine (min_le_left _ _).trans ?_
    rw [← inv_inv (ρ₁e g)]
    refine inv_anti₀ (inv_pos.2 hρ₁e) ?_
    have : (ρ₁e g)⁻¹ ≤ ∑ g ∈ S₀, (ρ₁e g)⁻¹ :=
      Finset.single_le_sum (f := fun g => (ρ₁e g)⁻¹) (fun g _ => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, hρ₁e', -⟩ := hoffc g
        exact (inv_pos.2 hρ₁e').le) hg
    linarith
  have hρ₁R : ∀ g ∈ S₀, ρ₁ ≤ RA g - rb g := by
    intro g hg
    refine (min_le_right _ _).trans ?_
    rw [← inv_inv (RA g - rb g)]
    refine inv_anti₀ (inv_pos.2 (hmargin g hg)) ?_
    have : (RA g - rb g)⁻¹ ≤ ∑ g ∈ S₀, (RA g - rb g)⁻¹ :=
      Finset.single_le_sum (f := fun g => (RA g - rb g)⁻¹) (fun g hg' => (inv_pos.2 (hmargin g hg')).le) hg
    linarith
  set L : ℝ := ∑ g ∈ S₀, Le g with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun g _ => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hLe, -⟩ := hoffc g
    exact hLe
  have hLle : ∀ g ∈ S₀, Le g ≤ L := fun g hg =>
    Finset.single_le_sum (f := Le) (fun g _ => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hLe, -⟩ := hoffc g
      exact hLe) hg
  set m₀ : ℝ := (∑ g ∈ S₀, (mme g)⁻¹ + 1)⁻¹ with hm₀def
  have hm₀pos : 0 < m₀ := by
    refine inv_pos.2 (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun g _ => ?_) one_pos)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmme, -⟩ := hoffc g
    exact (inv_pos.2 hmme).le
  have hm₀le : ∀ g ∈ S₀, m₀ ≤ mme g := by
    intro g hg
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmme, -⟩ := hoffc g
    rw [hm₀def, ← inv_inv (mme g)]
    refine inv_anti₀ (inv_pos.2 hmme) ?_
    have : (mme g)⁻¹ ≤ ∑ g ∈ S₀, (mme g)⁻¹ :=
      Finset.single_le_sum (f := fun g => (mme g)⁻¹) (fun g _ => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmme', -⟩ := hoffc g
        exact (inv_pos.2 hmme').le) hg
    linarith
  refine ⟨ρ₁, L, m₀, hρ₁pos, hL0, hm₀pos, fun ρ₁' hρ₁' hρ₁'le => ?_⟩

  have hsep : ∀ s₀ : SL(2, ℤ), ∃ eta : ℝ, 0 < eta ∧ (s₀ ∈ S₀ →
      ∀ u : ℂ, ‖u‖ ≤ rb s₀ → ∀ τ : ℍ, pchd (Φint σ₀ s (τ : ℂ)) (Φe s₀ u) < eta →
        (u ≠ 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ Φint σ₀ s (τ : ℂ) = c • Φe s₀ u) ∨
        (∃ z' ∈ closedBall u ρ₁', z' ≠ u ∧ ∃ t : ℂ, t ≠ 0 ∧ Φint σ₀ s (τ : ℂ) = t • Φe s₀ z')) := by
    intro s₀
    by_cases hs₀ : s₀ ∈ S₀
    · obtain ⟨eta, heta, h⟩ := sep_core D s hs σ₀ hy₀ hYb1 hcov hS₀ Φe me Re Ae ρe ρ₁e Le mme Yr ce hoffc hYb
        (fun h => cuspPl_inj σ₀ h) s₀ hs₀ hρ₁' (by
          have := hρ₁R s₀ hs₀
          show rb s₀ + ρ₁' ≤ RA s₀
          linarith)
      exact ⟨eta, heta, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hs₀⟩
  choose etaS hetaS hsepS using hsep
  set eta : ℝ := (∑ g ∈ S₀, (etaS g)⁻¹ + 1)⁻¹ with hetadef
  have hetapos : 0 < eta :=
    inv_pos.2 (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun g _ => (inv_pos.2 (hetaS g)).le) one_pos)
  have hetale : ∀ g ∈ S₀, eta ≤ etaS g := by
    intro g hg
    rw [hetadef, ← inv_inv (etaS g)]
    refine inv_anti₀ (inv_pos.2 (hetaS g)) ?_
    have : (etaS g)⁻¹ ≤ ∑ g ∈ S₀, (etaS g)⁻¹ :=
      Finset.single_le_sum (f := fun g => (etaS g)⁻¹) (fun g _ => (inv_pos.2 (hetaS g)).le) hg
    linarith
  refine ⟨eta, hetapos, fun σ hσ v hvoff => ?_⟩
  have hΦ : Φint σ s = Φint σ₀ s := Φint_congr hσ
  by_cases hj : jB N ∈ v.toValuationSubring
  ·
    obtain ⟨s₀, hs₀, zτ, hzτ, hv, t, ht, hxv⟩ := off_box_lift D σ s hs hcov hS₀ v hj hvoff
    obtain ⟨hRe0, hRe1, hAe0, hReA, hReZ, hV, hce, hval, hρe, hρeR, hρ₁e, hLe, hmme, hnear, hAeYr, hexpYr, hINJ⟩ :=
      hoffc s₀
    have hVσ : ∀ τ : ℍ, Ae s₀ ≤ τ.im →
        Φe s₀ (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ : ℂ)) =
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ : ℂ) ^ me s₀ •
            Φint σ s ((s₀ • τ : ℍ) : ℂ) := fun τ hτ => by rw [hΦ]; exact (hV τ hτ).2
    have hAezτ : Ae s₀ < zτ.im := by linarith [hYrYb s₀ hs₀]
    set zb : ℂ := Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (zτ : ℂ) with hzbdef
    have hzb0 : zb ≠ 0 := hqne s₀ _
    have hzbn : ‖zb‖ ≤ rb s₀ := (hnormq' s₀ zτ Yb hzτ).le
    have hzbρe : zb ∈ closedBall (0 : ℂ) (ρe s₀) := by
      rw [mem_closedBall, dist_zero_right]; linarith [hrbρe s₀ hs₀]
    have hzb1 : zb ∈ ball (0 : ℂ) (Re s₀) := (hV zτ hAezτ.le).1
    obtain ⟨-, Ψw, hId, hLipw, hfloorw⟩ := hnear zb hzbρe

    have hΦbzb : Φe s₀ zb = (zb ^ me s₀ * t⁻¹) • (fun i => σ (evalVec s v i)) := by
      rw [hVσ zτ hAezτ.le, ← smul_smul, hxv, smul_smul t⁻¹ t, inv_mul_cancel₀ ht, one_smul]
    have htb : zb ^ me s₀ * t⁻¹ ≠ 0 := mul_ne_zero (zpow_ne_zero _ hzb0) (inv_ne_zero ht)

    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun i => ‖Φe s₀ zb i‖) Finset.univ_nonempty
    have hpn : ‖Φe s₀ zb p‖ = ‖Φe s₀ zb‖ := by
      apply le_antisymm (norm_le_pi_norm _ _)
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hp i (Finset.mem_univ i)
    have hb0 : Φe s₀ zb ≠ 0 := hReZ zb hzb1
    have hbp : Φe s₀ zb p ≠ 0 := by
      intro h; rw [h, norm_zero] at hpn; exact hb0 (norm_eq_zero.1 hpn.symm)
    have hvp : evalVec s v p ≠ 0 := by
      intro h; apply hbp
      have := congrFun hΦbzb p
      simp only [Pi.smul_apply, smul_eq_mul, h, map_zero, mul_zero] at this
      exact this
    have hxw : Φe s₀ zb = (Φe s₀ zb p) • (fun i => σ (evalVec s v i * (evalVec s v p)⁻¹)) := by
      funext i
      have hi := congrFun hΦbzb i
      have hpp := congrFun hΦbzb p
      simp only [Pi.smul_apply, smul_eq_mul] at hi hpp ⊢
      rw [hi, hpp, map_mul, map_inv₀]
      have hσvp : σ (evalVec s v p) ≠ 0 := (map_ne_zero σ).2 hvp
      field_simp
    have hρ₁e' : ρ₁ ≤ ρ₁e s₀ := hρ₁le s₀ hs₀
    refine ⟨Φe s₀, zb, Ψw, p, zb ^ me s₀ * t⁻¹, htb, hΦbzb, hpn,
      fun z hz q => hId z (closedBall_subset_closedBall hρ₁e' hz) q,
      fun z hz z' hz' => (hLipw z (closedBall_subset_closedBall hρ₁e' hz) z'
        (closedBall_subset_closedBall hρ₁e' hz')).trans (mul_le_mul_of_nonneg_right (hLle s₀ hs₀) (norm_nonneg _)),
      (hm₀le s₀ hs₀).trans (hfloorw p hpn), ?_, ?_⟩
    ·
      intro e ha0 hgood
      exact simple_high D σ s hs s₀ (hw s₀) hAe0.le hReA hVσ zτ hAezτ hzb1 v hv p hbp rfl hxw hρ₁' hL0
        (fun z hz q => hId z (closedBall_subset_closedBall (hρ₁'le.trans hρ₁e') hz) q)
        (fun z hz z' hz' => (hLipw z (closedBall_subset_closedBall (hρ₁'le.trans hρ₁e') hz) z'
          (closedBall_subset_closedBall (hρ₁'le.trans hρ₁e') hz')).trans
          (mul_le_mul_of_nonneg_right (hLle s₀ hs₀) (norm_nonneg _)))
        e ha0 hgood
    ·
      intro j z hz hzD hlt
      obtain ⟨t', ht', hrepz⟩ := hrep σ hσ j z hz hzD
      rw [hrepz, pchd_smul_left ht', hΦ] at hlt
      rcases hsepS s₀ hs₀ zb hzbn (lift j z) (hlt.trans_le (hetale s₀ hs₀)) with ⟨-, c', hc', hcz⟩ | ⟨z', hz', hne, t₂, ht₂, h2⟩
      · left
        have hpt : D.pt (lift j z) = D.pt (s₀ • zτ) := by
          refine PLBSEP.inj_all D σ₀ s hs _ _ ⟨c' * zb ^ me s₀, mul_ne_zero hc' (zpow_ne_zero _ hzb0), ?_⟩
          rw [hcz, (hV zτ hAezτ.le).2, smul_smul]
        rw [hv, hpt]
      · right
        exact ⟨z', hz', hne, t' * t₂, mul_ne_zero ht' ht₂, by rw [hrepz, hΦ, h2, smul_smul]⟩
  ·
    obtain ⟨s₀, hs₀, hvpl⟩ := cusp_rep σ hS₀ v hj
    obtain ⟨hRe0, hRe1, hAe0, hReA, hReZ, hV, hce, hval, hρe, hρeR, hρ₁e, hLe, hmme, hnear, hAeYr, hexpYr, hINJ⟩ :=
      hoffc s₀
    have hVσ : ∀ τ : ℍ, Ae s₀ ≤ τ.im →
        Φe s₀ (Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ : ℂ)) =
          Function.Periodic.qParam (Subgroup.strictWidthInfty (conjGamma0 N s₀)) (τ : ℂ) ^ me s₀ •
            Φint σ s ((s₀ • τ : ℍ) : ℂ) := fun τ hτ => by rw [hΦ]; exact (hV τ hτ).2
    have hA0 : ∀ i, AnalyticAt ℂ (fun q => Φe s₀ q i) 0 := fun i => hReA i 0 (mem_ball_self hRe0)
    have hb0 : Φe s₀ 0 ≠ 0 := hReZ 0 (mem_ball_self hRe0)
    obtain ⟨tb, htb, hΦb0⟩ := cusp_centre_prop D σ s hs s₀ hA0 hb0 hVσ
    rw [hvpl] at hΦb0
    obtain ⟨-, Ψw, hId, hLipw, hfloorw⟩ := hnear 0 (mem_closedBall_self hρe.le)
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun i => ‖Φe s₀ 0 i‖) Finset.univ_nonempty
    have hpn : ‖Φe s₀ 0 p‖ = ‖Φe s₀ 0‖ := by
      apply le_antisymm (norm_le_pi_norm _ _)
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hp i (Finset.mem_univ i)
    have hbp : Φe s₀ 0 p ≠ 0 := by
      intro h; rw [h, norm_zero] at hpn; exact hb0 (norm_eq_zero.1 hpn.symm)
    have hvp : evalVec s v p ≠ 0 := by
      intro h; apply hbp
      have := congrFun hΦb0 p
      simp only [Pi.smul_apply, smul_eq_mul, h, map_zero, mul_zero] at this
      exact this
    have hxw : Φe s₀ 0 = (Φe s₀ 0 p) • (fun i => σ (evalVec s v i * (evalVec s v p)⁻¹)) := by
      funext i
      have hi := congrFun hΦb0 i
      have hpp := congrFun hΦb0 p
      simp only [Pi.smul_apply, smul_eq_mul] at hi hpp ⊢
      rw [hi, hpp, map_mul, map_inv₀]
      have hσvp : σ (evalVec s v p) ≠ 0 := (map_ne_zero σ).2 hvp
      field_simp
    have hρ₁e' : ρ₁ ≤ ρ₁e s₀ := hρ₁le s₀ hs₀
    refine ⟨Φe s₀, 0, Ψw, p, tb, htb, hΦb0, hpn,
      fun z hz q => hId z (closedBall_subset_closedBall hρ₁e' hz) q,
      fun z hz z' hz' => (hLipw z (closedBall_subset_closedBall hρ₁e' hz) z'
        (closedBall_subset_closedBall hρ₁e' hz')).trans (mul_le_mul_of_nonneg_right (hLle s₀ hs₀) (norm_nonneg _)),
      (hm₀le s₀ hs₀).trans (hfloorw p hpn), ?_, ?_⟩
    ·
      intro e ha0 hgood
      exact simple_cusp0 D σ s hs s₀ hA0 hb0 hVσ v hvpl p hbp rfl hxw hρ₁' hL0
        (fun z hz q => hId z (closedBall_subset_closedBall (hρ₁'le.trans hρ₁e') hz) q)
        (fun z hz z' hz' => (hLipw z (closedBall_subset_closedBall (hρ₁'le.trans hρ₁e') hz) z'
          (closedBall_subset_closedBall (hρ₁'le.trans hρ₁e') hz')).trans
          (mul_le_mul_of_nonneg_right (hLle s₀ hs₀) (norm_nonneg _)))
        e ha0 hgood
    ·
      intro j z hz hzD hlt
      obtain ⟨t', ht', hrepz⟩ := hrep σ hσ j z hz hzD
      rw [hrepz, pchd_smul_left ht', hΦ] at hlt
      have h0n : ‖(0 : ℂ)‖ ≤ rb s₀ := by rw [norm_zero]; exact (Real.exp_pos _).le
      rcases hsepS s₀ hs₀ 0 h0n (lift j z) (hlt.trans_le (hetale s₀ hs₀)) with ⟨h00, -⟩ | ⟨z', hz', hne, t₂, ht₂, h2⟩
      · exact absurd rfl h00
      · right
        exact ⟨z', hz', hne, t' * t₂, mul_ne_zero ht' ht₂, by rw [hrepz, hΦ, h2, smul_smul]⟩

theorem base_pkg (D : ComplexPlaceDictionary N) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (σ₀ : AlgebraicClosure ℚ →+* ℂ)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (ρ R : ι → ℝ) (Φ : ι → ℂ → (Fin r → ℂ)) (lift : ι → ℂ → ℍ) (Dom : ι → Set ℂ)
    (hA : ∀ j i, AnalyticOnNhd ℂ (fun z => Φ j z i) (ball (c j) (R j)))
    (hZ : ∀ j, ∀ z ∈ ball (c j) (R j), Φ j z ≠ 0) (hρR : ∀ j, ρ j < R j)
    (hrep : ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ j, ∀ z ∈ closedBall (c j) (ρ j), z ∈ Dom j → ∃ t : ℂ, t ≠ 0 ∧ Φ j z = t • Φint σ s ((lift j z : ℍ) : ℂ))

    (Bx y₀ Y₁ : ℝ) (hy₀ : 0 < y₀)

    {κs : Type} [Fintype κs] (Zs : κs → Set ℂ) (Λs : κs → ℂ → ℍ) (Vs : κs → ℂ → (Fin r → ℂ)) {etain : ℝ}
    (hZs : ∀ k, IsCompact (Zs k)) (hΛs : ∀ k, ContinuousOn (fun z => ((Λs k z : ℍ) : ℂ)) (Zs k))
    (hVs : ∀ k, ContinuousOn (Vs k) (Zs k)) (hVs0 : ∀ k, ∀ z ∈ Zs k, Vs k z ≠ 0)
    (hVsΦ : ∀ k, ∀ z ∈ Zs k, ∃ t : ℂ, t ≠ 0 ∧ Vs k z = t • Φint σ₀ s ((Λs k z : ℍ) : ℂ)) (hetain : 0 < etain)
    (hcovS : ∀ j, ∀ z ∈ closedBall (c j) (ρ j), z ∈ Dom j →
        (∃ k, ∃ z' ∈ Zs k, Vs k z' = Φ j z ∧ D.pt (Λs k z') = D.pt (lift j z)) ∨
        (∀ w : ℂ, |w.re| ≤ Bx → y₀ ≤ w.im → w.im ≤ Y₁ → ∀ hw : 0 < w.im, etain ≤ pchd (Φ j z) (Φint σ₀ s w)))

    (hoff :
    ∃ (ρ₁ L m₀ : ℝ), 0 < ρ₁ ∧ 0 ≤ L ∧ 0 < m₀ ∧
    ∀ ρ₁' : ℝ, 0 < ρ₁' → ρ₁' ≤ ρ₁ → ∃ eta : ℝ, 0 < eta ∧
    ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
    ∀ v : Place (AlgebraicClosure ℚ) (FB N),
      (¬ ∃ τ : ℍ, v.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) ∧
          (|(τ : ℂ).re| ≤ Bx ∧ y₀ ≤ (τ : ℂ).im ∧ (τ : ℂ).im ≤ Y₁)) →
      ∃ (Φb : ℂ → (Fin r → ℂ)) (zb : ℂ) (Ψb : ℂ → (Fin r × Fin r → ℂ)) (p : Fin r) (tb : ℂ),
        tb ≠ 0 ∧ Φb zb = tb • (fun i => σ (evalVec s v i)) ∧ ‖Φb zb p‖ = ‖Φb zb‖ ∧
        (∀ z ∈ closedBall zb ρ₁, ∀ q : Fin r × Fin r,
          Φb zb q.1 * Φb z q.2 - Φb zb q.2 * Φb z q.1 = (z - zb) * Ψb z q) ∧
        (∀ z ∈ closedBall zb ρ₁, ∀ z' ∈ closedBall zb ρ₁, ‖Ψb z - Ψb z'‖ ≤ L * ‖z - z'‖) ∧
        m₀ ≤ ‖fun i => Ψb zb (p, i)‖ ∧
        (∀ e : Fin r → AlgebraicClosure ℚ, linSec s (pencilAlg s v p e) ≠ 0 →
          (∀ z ∈ closedBall zb ρ₁', ∑ i, σ (e i) * Ψb z (p, i) ≠ 0) →
          v.ord (linSec s (pencilAlg s v p e)) + embDivisor N v = 1) ∧
        (∀ j, ∀ z ∈ closedBall (c j) (ρ j), z ∈ Dom j → pchd (Φ j z) (Φb zb) < eta →
          v.toValuationSubring = (D.pt (lift j z)).toValuationSubring.comap (phi N σ) ∨
          ∃ z' ∈ closedBall zb ρ₁', z' ≠ zb ∧ ∃ t : ℂ, t ≠ 0 ∧ Φ j z = t • Φb z')) :
    ∃ (ρ₁ L m₀ eta : ℝ), 0 < ρ₁ ∧ 0 ≤ L ∧ 0 < m₀ ∧ 0 < eta ∧ (r * (L * ρ₁) / m₀) ^ 2 ≤ 1 / 8 ∧
    ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
    ∀ v : Place (AlgebraicClosure ℚ) (FB N),
      ∃ (Φb : ℂ → (Fin r → ℂ)) (zb : ℂ) (Ψb : ℂ → (Fin r × Fin r → ℂ)) (p : Fin r) (tb : ℂ),
        tb ≠ 0 ∧ Φb zb = tb • (fun i => σ (evalVec s v i)) ∧ ‖Φb zb p‖ = ‖Φb zb‖ ∧
        (∀ z ∈ closedBall zb ρ₁, ∀ q : Fin r × Fin r,
          Φb zb q.1 * Φb z q.2 - Φb zb q.2 * Φb z q.1 = (z - zb) * Ψb z q) ∧
        (∀ z ∈ closedBall zb ρ₁, ∀ z' ∈ closedBall zb ρ₁, ‖Ψb z - Ψb z'‖ ≤ L * ‖z - z'‖) ∧
        m₀ ≤ ‖fun i => Ψb zb (p, i)‖ ∧

        (∀ e : Fin r → AlgebraicClosure ℚ,
          linSec s (fun i => e i - (∑ j, evalVec s v j * (evalVec s v p)⁻¹ * e j) * (if i = p then 1 else 0)) ≠ 0 →
          (∀ z ∈ closedBall zb ρ₁, ∑ i, σ (e i) * Ψb z (p, i) ≠ 0) →
          v.ord (linSec s (fun i => e i - (∑ j, evalVec s v j * (evalVec s v p)⁻¹ * e j) * (if i = p then 1 else 0)))
            + embDivisor N v = 1) ∧

        (∀ j, ∀ z ∈ closedBall (c j) (ρ j), z ∈ Dom j → pchd (Φ j z) ((Φb zb p)⁻¹ • Φb zb) < eta →
          v.toValuationSubring = (D.pt (lift j z)).toValuationSubring.comap (phi N σ) ∨
          ∃ z' ∈ closedBall zb ρ₁, z' ≠ zb ∧ ∃ t : ℂ, t ≠ 0 ∧ Φ j z = t • Φb z') := by
  classical
  have hr := r_pos N s hs
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr

  have hKc : IsCompact {z : ℂ | |z.re| ≤ Bx ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁} := isCompact_box' Bx y₀ Y₁
  have hKim : ∀ z ∈ {z : ℂ | |z.re| ≤ Bx ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁}, 0 < z.im := fun z hz => hy₀.trans_le hz.2.1

  have hell : ∀ t : ℂ, ∃ (F : ℂ → (Fin r → ℂ)) (ρt ρ₁t Lt mt : ℝ),
      0 < ρt ∧ ρt < 1 ∧ 0 < ρ₁t ∧ 0 ≤ Lt ∧ 0 < mt ∧
      (∀ i, AnalyticOnNhd ℂ (fun u => F u i) (ball 0 1)) ∧ (∀ u ∈ ball (0 : ℂ) 1, F u ≠ 0) ∧
      (∀ z : ℂ, 0 < z.im →
        F (Cay.cay (UpperHalfPlane.ofComplex t) z ^ D.ramification (UpperHalfPlane.ofComplex t)) = Φint σ₀ s z) ∧
      (∀ b : Fin r → ℂ, (∑ i, b i • phi N σ₀ (s i)) ≠ 0 →
        analyticOrderAt (fun u => ∑ i, b i * F u i) 0
          = ((((D.pt (UpperHalfPlane.ofComplex t)).ord (∑ i, b i • phi N σ₀ (s i))).toNat : ℕ) : ℕ∞)) ∧
      (∀ b : Fin r → ℂ, (∑ i, b i • phi N σ₀ (s i)) ≠ 0 → ∀ z : ℂ, ∀ hz : 0 < z.im,
        Cay.cay (UpperHalfPlane.ofComplex t) z ≠ 0 →
        analyticOrderAt (fun u => ∑ i, b i * F u i)
            (Cay.cay (UpperHalfPlane.ofComplex t) z ^ D.ramification (UpperHalfPlane.ofComplex t))
          = ((((D.ramification ⟨z, hz⟩ : ℤ) * (D.pt ⟨z, hz⟩).ord (∑ i, b i • phi N σ₀ (s i))).toNat : ℕ) : ℕ∞)) ∧
      (∀ w ∈ closedBall (0 : ℂ) ρt, closedBall w ρ₁t ⊆ ball (0 : ℂ) 1 ∧ ∃ Ψw : ℂ → (Fin r × Fin r → ℂ),
        (∀ z ∈ closedBall w ρ₁t, ∀ q : Fin r × Fin r, F w q.1 * F z q.2 - F w q.2 * F z q.1 = (z - w) * Ψw z q) ∧
        (∀ z ∈ closedBall w ρ₁t, ∀ z' ∈ closedBall w ρ₁t, ‖Ψw z - Ψw z'‖ ≤ Lt * ‖z - z'‖) ∧
        (∀ p : Fin r, ‖F w p‖ = ‖F w‖ → mt ≤ ‖fun i => Ψw w (p, i)‖)) := by
    intro t
    obtain ⟨F, hFA, hV0, -, hZ, hORD0, hORD, -⟩ := ATLINT.elliptic_chart D σ₀ s hs (UpperHalfPlane.ofComplex t)
    obtain ⟨b, -, hb1⟩ := GLUE.exists_analyticOrderAt_eq_one D σ₀ s hs (UpperHalfPlane.ofComplex t) hORD0
    have hmin := exists_minor_ne_zero_of_order_one (fun i => hFA i 0 (mem_ball_self one_pos))
      (hZ 0 (mem_ball_self one_pos)) hb1
    obtain ⟨ρt, hρt, hρt1, himm⟩ := exists_ball_minor_ne_zero one_pos hFA hmin
    obtain ⟨ρ₁t, Lt, mt, hρ₁t, hLt, hmt, hnear⟩ := near_package isOpen_ball (fun i => (hFA i).differentiableOn)
      (isCompact_closedBall 0 ρt) (closedBall_subset_ball hρt1) (fun w hw => hZ w (closedBall_subset_ball hρt1 hw)) himm
    exact ⟨F, ρt, ρ₁t, Lt, mt, hρt, hρt1, hρ₁t, hLt, hmt, hFA, hZ, hV0, hORD0, hORD, hnear⟩
  choose F ρt ρ₁t Lt mt hρt hρt1 hρ₁t hLt hmt hFA hFZ hFV hFORD0 hFORD hFnear using hell

  have hcaycont : ∀ t : ℂ, ContinuousOn (fun z : ℂ => Cay.cay (UpperHalfPlane.ofComplex t) z) {z : ℂ | 0 < z.im} := by
    intro t z hz
    refine ContinuousAt.continuousWithinAt ?_
    simp only [Cay.cay]
    exact (continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const)
      (Cay.sub_conj_ne_zero _ (le_of_lt hz))
  have hopen_im : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hU : ∀ t ∈ {z : ℂ | |z.re| ≤ Bx ∧ y₀ ≤ z.im ∧ z.im ≤ Y₁},
      {z : ℂ | 0 < z.im ∧ ‖Cay.cay (UpperHalfPlane.ofComplex t) z ^ D.ramification (UpperHalfPlane.ofComplex t)‖ < ρt t / 2}
        ∈ 𝓝 t := by
    intro t ht
    have htim := hKim t ht
    refine IsOpen.mem_nhds ?_ ⟨htim, ?_⟩
    · have := ((hcaycont t).pow (D.ramification (UpperHalfPlane.ofComplex t))).norm.isOpen_inter_preimage hopen_im
        (isOpen_Iio (a := ρt t / 2))
      convert this using 1
      all_goals first | rfl | (ext z; simp)
    · have h0 : Cay.cay (UpperHalfPlane.ofComplex t) t = 0 := by
        have := Cay.cay_self (UpperHalfPlane.ofComplex t)
        rwa [UpperHalfPlane.ofComplex_apply_of_im_pos htim] at this ⊢
      rw [h0, zero_pow (D.ramification_pos _).ne', norm_zero]
      exact half_pos (hρt t)
  obtain ⟨Tb, hTbK, hTbcov⟩ := hKc.elim_nhds_subcover _ hU
  have hTbim : ∀ t ∈ Tb, 0 < t.im := fun t ht => hKim t (hTbK t ht)

  set Lb : ℝ := ∑ t ∈ Tb, Lt t with hLb
  have hLb0 : 0 ≤ Lb := Finset.sum_nonneg fun t _ => hLt t
  have hLtle : ∀ t ∈ Tb, Lt t ≤ Lb := fun t ht => Finset.single_le_sum (fun t _ => hLt t) ht
  set mb : ℝ := (∑ t ∈ Tb, (mt t)⁻¹ + 1)⁻¹ with hmb
  have hmbpos : 0 < mb := by
    rw [hmb]; exact inv_pos.2 (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun t _ => (inv_pos.2 (hmt t)).le) one_pos)
  have hmble : ∀ t ∈ Tb, mb ≤ mt t := by
    intro t ht
    rw [hmb, ← inv_inv (mt t)]
    refine inv_anti₀ (inv_pos.2 (hmt t)) ?_
    have : (mt t)⁻¹ ≤ ∑ t ∈ Tb, (mt t)⁻¹ :=
      Finset.single_le_sum (f := fun t => (mt t)⁻¹) (fun t _ => (inv_pos.2 (hmt t)).le) ht
    linarith
  set ρb : ℝ := (∑ t ∈ Tb, (ρ₁t t)⁻¹ + 1)⁻¹ with hρb
  have hρbpos : 0 < ρb := by
    rw [hρb]; exact inv_pos.2 (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun t _ => (inv_pos.2 (hρ₁t t)).le) one_pos)
  have hρble : ∀ t ∈ Tb, ρb ≤ ρ₁t t := by
    intro t ht
    rw [hρb, ← inv_inv (ρ₁t t)]
    refine inv_anti₀ (inv_pos.2 (hρ₁t t)) ?_
    have : (ρ₁t t)⁻¹ ≤ ∑ t ∈ Tb, (ρ₁t t)⁻¹ :=
      Finset.single_le_sum (f := fun t => (ρ₁t t)⁻¹) (fun t _ => (inv_pos.2 (hρ₁t t)).le) ht
    linarith

  obtain ⟨ρo, Lo, mo, hρo, hLo, hmo, hoff⟩ := hoff
  set L : ℝ := Lb + Lo with hLdef
  have hL0 : 0 ≤ L := by positivity
  set m₀ : ℝ := min mb mo with hm₀
  have hm₀pos : 0 < m₀ := lt_min hmbpos hmo
  set ρ₁ : ℝ := min (min ρb ρo) (m₀ / (8 * r * (L + 1))) with hρ₁def
  have hρ₁pos : 0 < ρ₁ := by positivity
  have hρ₁b : ρ₁ ≤ ρb := (min_le_left _ _).trans (min_le_left _ _)
  have hρ₁o : ρ₁ ≤ ρo := (min_le_left _ _).trans (min_le_right _ _)
  have hsmall : (r * (L * ρ₁) / m₀) ^ 2 ≤ 1 / 8 := by
    have h1 : ρ₁ ≤ m₀ / (8 * r * (L + 1)) := min_le_right _ _
    have h2 : r * (L * ρ₁) / m₀ ≤ 1 / 8 := by
      rw [div_le_iff₀ hm₀pos]
      have : r * (L * ρ₁) ≤ r * (L * (m₀ / (8 * r * (L + 1)))) := by gcongr
      refine this.trans ?_
      rw [show r * (L * (m₀ / (8 * r * (L + 1)))) = (L / (L + 1)) * (1 / 8 * m₀) by field_simp]
      have hL1 : L / (L + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
      nlinarith
    have h3 : 0 ≤ r * (L * ρ₁) / m₀ := by positivity
    nlinarith
  obtain ⟨etao, hetao, hoffσ⟩ := hoff ρ₁ hρ₁pos hρ₁o

  have hsep_t : ∀ t : ℂ, ∃ etat : ℝ, 0 < etat ∧ ∀ k, ∀ z ∈ Zs k, ∀ u ∈ closedBall (0:ℂ) (ρt t / 2),
      pchd (Vs k z) (F t u) < etat → ∃ γ : CongruenceSubgroup.Gamma0 N,
        dist (Cay.cay (UpperHalfPlane.ofComplex t) (((γ : SL(2, ℤ)) • Λs k z : ℍ) : ℂ)
          ^ D.ramification (UpperHalfPlane.ofComplex t)) u < ρ₁ := by
    intro t
    have hW : IsCompact (closedBall (0:ℂ) (ρt t / 2)) := isCompact_closedBall _ _
    have hWsub : closedBall (0:ℂ) (ρt t / 2) ⊆ ball 0 1 :=
      closedBall_subset_ball (by linarith [hρt1 t, hρt t])
    have hB : ContinuousOn (F t) (closedBall (0:ℂ) (ρt t / 2)) :=
      continuousOn_pi.2 fun i => (hFA t i).continuousOn.mono hWsub
    have hκ : Continuous fun w : ℍ => Cay.cay (UpperHalfPlane.ofComplex t) (w : ℂ) ^ D.ramification (UpperHalfPlane.ofComplex t) := by
      refine Continuous.pow ?_ _
      have : Continuous fun w : ℍ => (w : ℂ) := UpperHalfPlane.continuous_coe
      exact (hcaycont t).comp_continuous this fun w => w.im_pos
    have hBΦ : ∀ u ∈ closedBall (0:ℂ) (ρt t / 2), ∃ w : ℍ,
        Cay.cay (UpperHalfPlane.ofComplex t) (w : ℂ) ^ D.ramification (UpperHalfPlane.ofComplex t) = u ∧
        ∃ c : ℂ, c ≠ 0 ∧ F t u = c • Φint σ₀ s (w : ℂ) := by
      intro u hu
      obtain ⟨w, hwim, hw, -⟩ := Cay.exists_cay_pow_eq (UpperHalfPlane.ofComplex t)
        (D.ramification_pos (UpperHalfPlane.ofComplex t)) (show ‖u‖ < 1 by simpa [mem_ball, dist_zero_right] using hWsub hu)
      refine ⟨⟨w, hwim⟩, hw, 1, one_ne_zero, ?_⟩
      rw [one_smul, ← hw, hFV t w hwim]
    exact PLBSEP.unifsep_core D σ₀ s hs Zs hZs Λs hΛs Vs hVs hVs0 hVsΦ _ hW (F t) hB
      (fun u hu => hFZ t u (hWsub hu)) _ hκ hBΦ hρ₁pos
  choose etat hetat hsep_t' using hsep_t
  set etab : ℝ := min etain (∑ t ∈ Tb, (etat t)⁻¹ + 1)⁻¹ with hetab
  have hetabpos : 0 < etab := by
    rw [hetab]
    exact lt_min hetain (inv_pos.2 (add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun t _ => (inv_pos.2 (hetat t)).le) one_pos))
  have hetable : ∀ t ∈ Tb, etab ≤ etat t := by
    intro t ht
    rw [hetab]
    refine (min_le_right _ _).trans ?_
    rw [← inv_inv (etat t)]
    refine inv_anti₀ (inv_pos.2 (hetat t)) ?_
    have : (etat t)⁻¹ ≤ ∑ t ∈ Tb, (etat t)⁻¹ :=
      Finset.single_le_sum (f := fun t => (etat t)⁻¹) (fun t _ => (inv_pos.2 (hetat t)).le) ht
    linarith
  have hetabin : etab ≤ etain := min_le_left _ _
  refine ⟨ρ₁, L, m₀, min etab etao, hρ₁pos, hL0, hm₀pos, lt_min hetabpos hetao, hsmall, ?_⟩

  intro σ hσ v
  have hΦ : Φint σ s = Φint σ₀ s := Φint_congr hσ
  have hphis : ∀ i, phi N σ (s i) = phi N σ₀ (s i) := fun i => congrFun hσ i
  by_cases hbox : ∃ τ : ℍ, v.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) ∧
      (|(τ : ℂ).re| ≤ Bx ∧ y₀ ≤ (τ : ℂ).im ∧ (τ : ℂ).im ≤ Y₁)
  ·
    obtain ⟨w, hv, hwbox⟩ := hbox
    obtain ⟨t, ht, hwt⟩ := Set.mem_iUnion₂.mp (hTbcov hwbox)
    obtain ⟨-, hwt⟩ := hwt
    set τ₀ : ℍ := UpperHalfPlane.ofComplex t with hτ₀
    set zb : ℂ := Cay.cay τ₀ w ^ D.ramification τ₀ with hzb
    have hzbρ : zb ∈ closedBall (0 : ℂ) (ρt t) := by
      rw [mem_closedBall, dist_zero_right]; exact (hwt.le.trans (by linarith [hρt t]))
    have hzb1 : zb ∈ ball (0 : ℂ) 1 := closedBall_subset_ball (hρt1 t) hzbρ
    obtain ⟨hsub1, Ψw, hId, hLipw, hfloorw⟩ := hFnear t zb hzbρ

    have hjv : jB N ∈ v.toValuationSubring := by
      rw [hv, ValuationSubring.mem_comap, phi_jB]; exact ATLINT.jC_mem_pt D w
    obtain ⟨τv, hcomapv, tv, htv, hxv⟩ := place_proj' D σ s hs v hjv
    have hptv : D.pt τv = D.pt w := CUSPATLAS.pt_eq_pt_of_comap_eq D σ v hcomapv hv
    have hΦw : Φint σ s (w : ℂ) = Φint σ s (τv : ℂ) := by
      funext i
      rw [Φint_eq_ext, Φint_eq_ext, (ATLINT.ext_analyticAt D _ w ((ATLINT.interiorInputs D σ s hs).reg w i)).2.2,
        (ATLINT.ext_analyticAt D _ τv ((ATLINT.interiorInputs D σ s hs).reg τv i)).2.2, hptv]
    have hFzb : F t zb = tv⁻¹ • (fun i => σ (evalVec s v i)) := by
      rw [hzb, hFV t (w : ℂ) w.im_pos, ← hΦ, hΦw, hxv, smul_smul, inv_mul_cancel₀ htv, one_smul]

    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun i => ‖F t zb i‖) Finset.univ_nonempty
    have hpn : ‖F t zb p‖ = ‖F t zb‖ := by
      apply le_antisymm (norm_le_pi_norm _ _)
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hp i (Finset.mem_univ i)
    refine ⟨F t, zb, Ψw, p, tv⁻¹, inv_ne_zero htv, hFzb, hpn,
      fun z hz q => hId z (closedBall_subset_closedBall (hρ₁b.trans (hρble t ht)) hz) q,
      fun z hz z' hz' => (hLipw z (closedBall_subset_closedBall (hρ₁b.trans (hρble t ht)) hz) z'
        (closedBall_subset_closedBall (hρ₁b.trans (hρble t ht)) hz')).trans
        (mul_le_mul_of_nonneg_right (by linarith [hLtle t ht]) (norm_nonneg _)),
      ((min_le_left _ _).trans (hmble t ht)).trans (hfloorw p hpn), ?_, ?_⟩
    ·
      intro e ha0 hgood
      have hb0 : F t zb ≠ 0 := hFZ t zb hzb1
      have hbp : F t zb p ≠ 0 := by
        intro h; rw [h, norm_zero] at hpn; exact hb0 (norm_eq_zero.1 hpn.symm)
      have hvp : evalVec s v p ≠ 0 := by
        intro h; apply hbp
        have := congrFun hFzb p
        simp only [Pi.smul_apply, smul_eq_mul, h, map_zero, mul_zero] at this
        exact this
      have hσvp : σ (evalVec s v p) ≠ 0 := (map_ne_zero σ).2 hvp
      have hxw : F t zb = (F t zb p) • (fun i => σ (evalVec s v i * (evalVec s v p)⁻¹)) := by
        funext i
        have hi := congrFun hFzb i
        have hpp := congrFun hFzb p
        simp only [Pi.smul_apply, smul_eq_mul] at hi hpp ⊢
        rw [hi, hpp, map_mul, map_inv₀]
        field_simp
      have hsum : ∀ b : Fin r → ℂ, (∑ i, b i • phi N σ (s i)) = ∑ i, b i • phi N σ₀ (s i) := fun b => by
        simp only [hphis]
      exact simple_ell D σ s hs τ₀ w v hv (hFA t)
        (fun b hb => by rw [hsum] at hb ⊢; exact hFORD0 t b hb)
        (fun b hb z hz hc => by rw [hsum] at hb ⊢; exact hFORD t b hb z hz hc)
        hzb hzb1 p hbp rfl hxw hρ₁pos (hLt t)
        (fun z hz q => hId z (closedBall_subset_closedBall (hρ₁b.trans (hρble t ht)) hz) q)
        (fun z hz z' hz' => hLipw z (closedBall_subset_closedBall (hρ₁b.trans (hρble t ht)) hz) z'
          (closedBall_subset_closedBall (hρ₁b.trans (hρble t ht)) hz'))
        e ha0 hgood
    ·
      intro j z hz hzD hlt
      have hb0 : F t zb ≠ 0 := hFZ t zb hzb1
      have hbp : F t zb p ≠ 0 := by
        intro h; rw [h, norm_zero] at hpn; exact hb0 (norm_eq_zero.1 hpn.symm)
      have hlt' : pchd (Φ j z) (F t zb) < etab := by
        rw [pchd_smul_right (inv_ne_zero hbp)] at hlt
        exact hlt.trans_le (min_le_left _ _)
      have hFw : F t zb = Φint σ₀ s (w : ℂ) := by rw [hzb, hFV t (w : ℂ) w.im_pos]
      rcases hcovS j z hz hzD with ⟨k, z₁, hz₁, hV, hpt⟩ | hinner
      ·
        have hzbW : zb ∈ closedBall (0:ℂ) (ρt t / 2) := by
          rw [mem_closedBall, dist_zero_right]; exact hwt.le
        obtain ⟨γ, hγ⟩ := hsep_t' t k z₁ hz₁ zb hzbW (by rw [hV]; exact hlt'.trans_le (hetable t ht))
        set z' : ℂ := Cay.cay τ₀ (((γ : SL(2, ℤ)) • Λs k z₁ : ℍ) : ℂ) ^ D.ramification τ₀ with hz'
        have hz'mem : z' ∈ closedBall zb ρ₁ := mem_closedBall.2 hγ.le
        have hFz' : F t z' = Φint σ₀ s ((Λs k z₁ : ℍ) : ℂ) := by
          rw [hz', hFV t _ (((γ : SL(2, ℤ)) • Λs k z₁).im_pos)]
          exact Φint_smul D σ₀ s hs γ (Λs k z₁)
        obtain ⟨c₁, hc₁, hVc⟩ := hVsΦ k z₁ hz₁
        by_cases hzz : z' = zb
        ·
          left
          have h1 : Φint σ₀ s ((Λs k z₁ : ℍ) : ℂ) = Φint σ₀ s (w : ℂ) := by rw [← hFz', hzz, hFw]
          have h2 : D.pt (Λs k z₁) = D.pt w := PLBSEP.inj_all D σ₀ s hs _ _ ⟨1, one_ne_zero, by rw [one_smul, h1]⟩
          rw [hv, ← h2, hpt]
        · right
          refine ⟨z', hz'mem, hzz, c₁, hc₁, ?_⟩
          rw [← hV, hVc, hFz']
      ·
        exfalso
        have := hinner (w : ℂ) hwbox.1 hwbox.2.1 hwbox.2.2 w.im_pos
        rw [← hFw] at this
        linarith [hlt'.trans_le hetabin]
  ·
    obtain ⟨Φb, zb, Ψb, p, tb, htb, hΦb, hp, hId, hLip, hfloor, hsimple, hsep⟩ := hoffσ σ hσ v hbox
    refine ⟨Φb, zb, Ψb, p, tb, htb, hΦb, hp,
      fun z hz q => hId z (closedBall_subset_closedBall hρ₁o hz) q,
      fun z hz z' hz' => (hLip z (closedBall_subset_closedBall hρ₁o hz) z' (closedBall_subset_closedBall hρ₁o hz')).trans
        (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)),
      (min_le_right _ _).trans hfloor, hsimple, fun j z hz hzD hlt => ?_⟩
    have hb0 : Φb zb ≠ 0 := by
      rw [hΦb]; exact smul_ne_zero htb (sigma_evalVec_ne_zero s hs σ v)
    have hbp : Φb zb p ≠ 0 := by
      intro h; rw [h, norm_zero] at hp; exact hb0 (norm_eq_zero.1 hp.symm)
    rw [pchd_smul_right (inv_ne_zero hbp)] at hlt
    exact hsep j z hz hzD (hlt.trans_le (min_le_right _ _))

theorem random_good_covector' (D : ComplexPlaceDictionary N) (s : Fin r → FB N)
    (hs : IsEmbBasis N s) (σ₀ : AlgebraicClosure ℚ →+* ℂ)
    (hbdd : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) (k : ℕ) (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      BddAbove (Set.range fun τ : PLB.Gen D σ u => PLB.psiU D σ s k u τ))
    (hbox : ∀ (Bx yl yu : ℝ), 0 < yl → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) → ∀ lam : ℝ, 0 < lam →
        MeasureTheory.volume {z : ℂ | |z.re| ≤ Bx ∧ yl ≤ z.im ∧ z.im ≤ yu ∧
            ‖ATLINT.ext (N := N) (phi N σ u) z‖
              ≤ Real.exp (PLB.supPsi D σ s k u - lam) * (⨆ i, ‖Φint σ s z i‖) ^ k}
          ≤ ENNReal.ofReal (C * (k + 1) / lam))
    (hcusp : ∀ (γ : SL(2, ℤ)) (h : ℝ), 0 < h → h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods →
      ∀ R : ℝ, 0 < R → R < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) → ∀ lam : ℝ, 0 < lam →
        MeasureTheory.volume {q : ℂ | q ∈ Metric.ball (0 : ℂ) R ∧ q ≠ 0 ∧
            ‖ATLINT.ext (N := N) (phi N σ u)
                ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℍ) : ℂ)‖
              ≤ Real.exp (PLB.supPsi D σ s k u - lam)
                * (⨆ i, ‖Φint σ s ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℍ) : ℂ) i‖) ^ k}
          ≤ ENNReal.ofReal (C * (k + 1) / lam)) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (FB N), (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (T : Finset (Place (AlgebraicClosure ℚ) (FB N))) (v : Place (AlgebraicClosure ℚ) (FB N)), B v = 0 →
      ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (FB N)),
        linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
        (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
        (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
        (∀ y, y ≠ v → (Za - Finsupp.single v (1 : ℤ)) y ≠ 0 →
          ∃ τ : ℍ, y.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) ∧
            secVal s y k u ≠ 0 ∧ PLB.supPsi D σ s k u - C₂ * (k + 1) ≤ PLB.psiU D σ s k u τ) := by
  classical
  have hr := r_pos N s hs
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩

  obtain ⟨Φe, me, Re, Ae, ρe, ρ₁e, Le, mme, Yr, ce, hoffc⟩ := off_charts₂ D s hs σ₀
  obtain ⟨S₀b, hS₀b⟩ := exists_coset_reps (N := N)
  set Yb : ℝ := (∑ g ∈ S₀b, |Yr g|) + 2 with hYbdef
  have hYb : ∀ g ∈ S₀b, Yr g + 1 ≤ Yb := by
    intro g hg
    have h1 : |Yr g| ≤ ∑ g ∈ S₀b, |Yr g| := Finset.single_le_sum (f := fun g => |Yr g|) (fun _ _ => abs_nonneg _) hg
    rw [hYbdef]; linarith [le_abs_self (Yr g)]
  have hYb1 : (1 : ℝ) < Yb := by
    have h0 : 0 ≤ ∑ g ∈ S₀b, |Yr g| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    rw [hYbdef]; linarith

  obtain ⟨Sb, Bx, y₀, Y₁, hy₀, hcovb⟩ := ModularGroup.exists_finset_box_or_cusp (CongruenceSubgroup.Gamma0 N) Yb
  obtain ⟨ι, hι, c, ρ, ρ', R, Φ, lift, Dom, Cvol, κs, hκs, Zs, Λs, Vs, etain,
      hρ, hρρ', hρ'R, hA, hLip, hZ, hCvol, hZs, hΛs, hVs, hVs0, hVsΦ, hetain, hcovS, hloc⟩ :=
    loc_pkg D s hs σ₀ Bx y₀ Y₁ hy₀ hbdd hbox hcusp
  letI := hι
  letI := hκs
  have hoff := base_off_box₂ D s hs σ₀ c ρ R Φ lift Dom hA hZ (fun j => (hρρ' j).trans (hρ'R j)) (fun σ hσ => (hloc σ hσ).1)
    Bx y₀ Y₁ Yb hy₀ hYb1 hcovb hS₀b Φe me Re Ae ρe ρ₁e Le mme Yr ce hoffc hYb
  obtain ⟨ρ₁, L, m₀, eta, hρ₁, hL, hm₀, heta, hsmall, hbase⟩ :=
    base_pkg D s hs σ₀ c ρ R Φ lift Dom hA hZ (fun j => (hρρ' j).trans (hρ'R j)) (fun σ hσ => (hloc σ hσ).1)
      Bx y₀ Y₁ hy₀ Zs Λs Vs hZs hΛs hVs hVs0 hVsΦ hetain hcovS hoff
  obtain ⟨β, hβ, hcore⟩ := random_core c ρ ρ' R Φ hρ hρρ' hρ'R hA hLip hZ heta

  refine ⟨(Cvol + 1) / β, by positivity, ?_⟩
  intro σ hσ k hk u hu huL B hB T v hBv
  obtain ⟨hrep, hcover, hfar⟩ := hloc σ hσ
  set lam : ℝ := (Cvol + 1) * (k + 1) / β with hlam
  have hlampos : 0 < lam := by positivity

  obtain ⟨Φb, zb, Ψb, p, tb, htb, hΦbzb, hp, hId, hLipb, hfloor, hsimple, hsep⟩ := hbase σ hσ v
  have hxv0 : (fun i => σ (evalVec s v i)) ≠ 0 := sigma_evalVec_ne_zero s hs σ v
  have hb0 : Φb zb ≠ 0 := by rw [hΦbzb]; exact smul_ne_zero htb hxv0
  have hbp : Φb zb p ≠ 0 := by
    intro h; rw [h, norm_zero] at hp; exact hb0 (norm_eq_zero.1 hp.symm)
  have hvp : evalVec s v p ≠ 0 := by
    intro h
    apply hbp
    have := congrFun hΦbzb p
    simp only [Pi.smul_apply, smul_eq_mul, h, map_zero, mul_zero] at this
    exact this
  set xh : Fin r → ℂ := (Φb zb p)⁻¹ • Φb zb with hxh
  have hxh_eq : xh = fun i => σ (evalVec s v i * (evalVec s v p)⁻¹) := by
    funext i
    simp only [xh, Pi.smul_apply, smul_eq_mul, hΦbzb, map_mul, map_inv₀]
    field_simp
  have hxh0 : xh ≠ 0 := by
    rw [hxh]; exact smul_ne_zero (inv_ne_zero hbp) hb0

  have hK := hfar k hk u hu huL lam hlampos xh hxh0 eta heta
  choose K hKc hKsub hKeta hKvol hKpsi using hK

  have hcf := finite_cusps (N := N)
  set P : Finset (Place (AlgebraicClosure ℚ) (FB N)) :=
    (T ∪ B.support ∪ hcf.toFinset).filter (fun w => w ≠ v) with hP
  set cw : Place (AlgebraicClosure ℚ) (FB N) → (Fin r → ℂ) :=
    fun w i => σ (evalVec s w i) - σ (evalVec s w p) * σ (evalVec s v i * (evalVec s v p)⁻¹) with hcw
  set Vn : Finset (Fin r → ℂ) := P.image cw with hVn
  have hVn0 : ∀ x ∈ Vn, x ≠ 0 := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
    have hwv : w ≠ v := (Finset.mem_filter.1 hw).2
    exact pencil_chord_ne_zero s hs σ v w hwv p hvp

  have hKβ : ∀ j, volume (K j) ≤ ENNReal.ofReal β := by
    intro j
    refine (hKvol j).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hlam, div_div_eq_mul_div]
    rw [div_le_iff₀ (by positivity)]
    have hk1 : (1:ℝ) ≤ k + 1 := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    nlinarith [hβ, hCvol]

  obtain ⟨e, hb_ball, hb_null, hb_near, hb_far⟩ := hcore σ Φb zb ρ₁ L m₀ Ψb p hρ₁ hL hm₀ hId hLipb hp hb0 hfloor
    hsmall K Vn hKc hKsub hKeta hKβ hVn0
  set b : Fin r → ℂ := fun i => σ (e i) with hb_def

  set a : Fin r → AlgebraicClosure ℚ :=
    fun i => e i - (∑ j, evalVec s v j * (evalVec s v p)⁻¹ * e j) * (if i = p then 1 else 0) with ha_def
  have hσa : ∀ i, σ (a i) = pencilCov xh p b i := by
    intro i
    simp only [a, pencilCov, b, map_sub, map_mul, map_sum, hxh_eq]
    congr 1
    split_ifs <;> simp

  have hax : ∀ w, σ (∑ i, evalVec s w i * a i) = ∑ i, cw w i * b i := by
    intro w
    rw [map_sum]
    simp only [map_mul, hσa]
    rw [pencilCov_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cw, hxh_eq]
    ring

  have hav : ∑ i, evalVec s v i * a i = 0 := by
    apply σ.injective
    rw [hax, map_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hσvp : σ (evalVec s v p) ≠ 0 := (map_ne_zero σ).2 hvp
    simp only [cw, map_mul, map_inv₀]
    rw [mul_comm (σ (evalVec s v i)) ((σ (evalVec s v p))⁻¹), ← mul_assoc, mul_inv_cancel₀ hσvp, one_mul, sub_self,
      zero_mul]

  have ha0 : linSec s a ≠ 0 := by
    intro h0
    have ha : a = 0 := by
      by_contra hne
      exact (linSec_ne_zero_of_ne_zero s hs a hne) h0
    have hbi : ∀ i, b i = (∑ j, xh j * b j) * (if i = p then 1 else 0) := by
      intro i
      have := hσa i
      rw [ha, Pi.zero_apply, map_zero] at this
      simp only [pencilCov] at this
      linear_combination -this
    set z₁ : ℂ := zb + ρ₁ with hz₁
    have hz₁mem : z₁ ∈ closedBall zb ρ₁ := by
      rw [mem_closedBall, dist_eq_norm, hz₁, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hρ₁]
    have hz₁ne : z₁ - zb ≠ 0 := by
      rw [hz₁, add_sub_cancel_left]; exact_mod_cast hρ₁.ne'
    have hpp : Ψb z₁ (p, p) = 0 := by
      have := hId z₁ hz₁mem (p, p)
      simp only [sub_self] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hz₁ne
    apply hb_near z₁ hz₁mem
    have : ∑ i, b i * Ψb z₁ (p, i) = (∑ j, xh j * b j) * Ψb z₁ (p, p) := by
      rw [Finset.sum_eq_single p]
      · rw [hbi p]; simp
      · intro i _ hip; rw [hbi i]; simp [hip]
      · simp
    rw [this, hpp, mul_zero]

  obtain ⟨Za, hZa⟩ := exists_pinned s hs a ha0

  have hZaP : ∀ w ∈ P, Za w = 0 := by
    intro w hw
    refine (pinned_eq_zero_iff s hs ha0 hZa w).2 fun h0 => ?_
    apply hb_null (cw w) (Finset.mem_image_of_mem _ hw)
    rw [← hax, h0, map_zero]
  have hmemP : ∀ w, w ≠ v → (w ∈ T ∨ B w ≠ 0 ∨ jB N ∉ w.toValuationSubring) → w ∈ P := by
    intro w hwv hw
    refine Finset.mem_filter.2 ⟨?_, hwv⟩
    simp only [Finset.mem_union, Finsupp.mem_support_iff, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    tauto

  have hZav : Za v = 1 := by rw [hZa v]; exact hsimple e ha0 hb_near
  refine ⟨a, Za, ha0, hZa, hav, hZav, fun w hwT hwv => hZaP w (hmemP w hwv (Or.inl hwT)), fun w hwv => ?_, ?_⟩
  · by_cases hBw : B w = 0
    · exact Or.inr hBw
    · exact Or.inl (hZaP w (hmemP w hwv (Or.inr (Or.inl hBw))))

  intro y hyv hy
  have hZay : Za y ≠ 0 := by
    rwa [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hyv), sub_zero] at hy
  have hBy : B y = 0 := by
    by_contra hBy
    exact hZay (hZaP y (hmemP y hyv (Or.inr (Or.inl hBy))))
  have hsec : secVal s y k u ≠ 0 := (L2.secVal_ne_zero_iff N s hs k u hu huL B hB y).2 hBy
  have hjy : jB N ∈ y.toValuationSubring := by
    by_contra h
    exact hZay (hZaP y (hmemP y hyv (Or.inr (Or.inr h))))

  obtain ⟨τy, hcomap, ty, hty, hxy⟩ := place_proj' D σ s hs y hjy
  have haxy : ∑ i, evalVec s y i * a i = 0 := by
    by_contra h
    exact hZay ((pinned_eq_zero_iff s hs ha0 hZa y).2 h)
  obtain ⟨j, z, hz, hzD, ⟨t, ht, hΦz⟩, hpt⟩ := hcover τy

  have hbC : ∑ i, b i * chord (Φ j) xh p z i = 0 := by
    have h1 : ∑ i, cw y i * b i = 0 := by rw [← hax, haxy, map_zero]

    have h2 : ∀ i, cw y i = (ty * t⁻¹) * chord (Φ j) xh p z i := by
      intro i
      have exy : σ (evalVec s y i) = ty * Φint σ s (τy : ℂ) i := by
        have := congrFun hxy i; simpa only [Pi.smul_apply, smul_eq_mul] using this
      have exyp : σ (evalVec s y p) = ty * Φint σ s (τy : ℂ) p := by
        have := congrFun hxy p; simpa only [Pi.smul_apply, smul_eq_mul] using this
      have eΦ : ∀ i, Φint σ s (τy : ℂ) i = t⁻¹ * Φ j z i := fun i => by
        have := congrFun hΦz i
        simp only [Pi.smul_apply, smul_eq_mul] at this
        field_simp
        rw [this]; ring
      simp only [cw, chord, exy, exyp, eΦ, hxh_eq]
      ring
    have h3 : ∑ i, cw y i * b i = (ty * t⁻¹) * ∑ i, b i * chord (Φ j) xh p z i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [h2 i]; ring
    rw [h3] at h1
    exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero hty (inv_ne_zero ht))
  have hzK : z ∉ K j := fun hzK => hb_far j z hzK hbC

  rcases le_or_gt eta (pchd (Φ j z) xh) with hfarz | hnearz
  ·
    refine ⟨lift j z, ?_, hsec, ?_⟩
    · rw [hcomap, hpt]
    · have := hKpsi j z hz hzD hzK hfarz
      have hle : (Cvol + 1) / β * (k + 1) = lam := by rw [hlam]; ring
      rw [hle]
      exact this.le
  ·
    exfalso
    rcases hsep j z hz hzD hnearz with hover | ⟨z', hz', hz'ne, t', ht', hΦz'⟩
    ·
      apply hyv
      rw [hpt] at hover
      exact CUSPATLAS.place_under_unique σ (D.pt τy) hcomap hover
    ·
      apply hb_near z' hz'
      have h1 : ∑ i, b i * chord Φb xh p z' i = 0 := by
        have e1 : ∀ i, chord (Φ j) xh p z i = t' * chord Φb xh p z' i := fun i => by
          have := congrFun hΦz' i
          have hp' := congrFun hΦz' p
          simp only [Pi.smul_apply, smul_eq_mul] at this hp'
          simp only [chord, this, hp']
          ring
        have e2 : ∑ i, b i * chord (Φ j) xh p z i = t' * ∑ i, b i * chord Φb xh p z' i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [e1 i]; ring
        rw [e2] at hbC
        exact (mul_eq_zero.1 hbC).resolve_left ht'
      have hxw : Φb zb = (Φb zb p) • xh := by
        rw [hxh, smul_smul, mul_inv_cancel₀ hbp, one_smul]
      have h2 := chord_eq_divided' (S := closedBall zb ρ₁) hId p hxw hbp b hz'
      rw [h2] at h1
      exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero (sub_ne_zero.2 hz'ne) (inv_ne_zero hbp))

end PLBG
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

namespace PLB
open CUSPATLAS ATLINT GLUE

variable {N : ℕ} [NeZero N] {r : ℕ}

section IFACE
variable (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → FB N)

theorem psiU_bddAbove (hs : IsEmbBasis N s) (k : ℕ) (u : FB N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N)) :
    BddAbove (Set.range fun τ : Gen D σ u => psiU D σ s k u τ) :=
  psiX_bddAbove (D := D) (xData_of σ s hs) (wData0_of σ s hs k u hu huL)

theorem phiU_eq_psiU (hs : IsEmbBasis N s) (k : ℕ) (u : FB N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (y : Place (AlgebraicClosure ℚ) (FB N)) (τ : ℍ)
    (hy : y.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ)) (hne : secVal s y k u ≠ 0) :
    phiU σ s k u y = psiU D σ s k u τ := by
  have hE0 := embDivisor_eq_zero_of_comap D σ y τ hy
  have hureg : u ∈ y.toValuationSubring := by
    refine y.mem_of_ord_nonneg hu ?_
    have := L2.neg_le_ord_of_mem _ huL hu y
    simp only [Finsupp.smul_apply, smul_eq_mul, hE0, mul_zero, neg_zero] at this
    exact this
  exact phiU_eq D σ s hs k u y τ hy hureg hne

theorem phiU_le_ciSup_of_cuspidal (hs : IsEmbBasis N s) (k : ℕ) (u : FB N) (hu : u ≠ 0)
    (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (y : Place (AlgebraicClosure ℚ) (FB N)) (hyc : jB N ∉ y.toValuationSubring) (hne : secVal s y k u ≠ 0) :
    phiU σ s k u y ≤ supPsi D σ s k u :=
  phiU_le_supPsi_of_cuspidal (D := D) σ s hs k u hu huL (psiU_bddAbove D σ s hs k u hu huL) y hyc hne

theorem bad_volume_box (hs : IsEmbBasis N s) (σ₀ : AlgebraicClosure ℚ →+* ℂ) (Bx yl yu : ℝ) (hyl : 0 < yl) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ lam : ℝ, 0 < lam →
        MeasureTheory.volume {z : ℂ | |z.re| ≤ Bx ∧ yl ≤ z.im ∧ z.im ≤ yu ∧
            ‖ATLINT.ext (N := N) (phi N σ u) z‖
              ≤ Real.exp (supPsi D σ s k u - lam) * (⨆ i, ‖Φint σ s z i‖) ^ k}
          ≤ ENNReal.ofReal (C * (k + 1) / lam) := by
  classical
  obtain ⟨C, hC, h⟩ := bad_volume_box_X (D := D) (xData_of σ₀ s hs) Bx yl yu hyl
  refine ⟨C, hC, fun σ htup k hk u hu huL lam hlam => ?_⟩
  have hw : WData D (fun i => phi N σ₀ (s i)) k (phi N σ u) := by
    have := wData_of (D := D) σ s hs k u hu huL (psiU_bddAbove D σ s hs k u hu huL)
    rwa [htup] at this
  have hmain := h k (phi N σ u) hw lam hlam
  have e1 : supPsi D σ s k u = supPsiX D (fun i => phi N σ₀ (s i)) k (phi N σ u) := by
    show supPsiX D (fun i => phi N σ (s i)) k (phi N σ u) = _
    rw [htup]
  have e2 : ∀ (z : ℂ) (i : Fin r), Φint σ s z i = ATLINT.ext (N := N) (phi N σ₀ (s i)) z := fun z i => by
    show ATLINT.ext (N := N) (phi N σ (s i)) z = _
    rw [show phi N σ (s i) = phi N σ₀ (s i) from congrFun htup i]
  simp_rw [e1, e2]
  exact hmain

theorem bad_volume_cusp (hs : IsEmbBasis N s) (σ₀ : AlgebraicClosure ℚ →+* ℂ) (γ : SL(2, ℤ)) (h : ℝ) (hh : 0 < h)
    (hper : h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods) (R : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ lam : ℝ, 0 < lam →
        MeasureTheory.volume {q : ℂ | q ∈ Metric.ball (0 : ℂ) R ∧ q ≠ 0 ∧
            ‖ATLINT.ext (N := N) (phi N σ u)
                ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℍ) : ℂ)‖
              ≤ Real.exp (supPsi D σ s k u - lam)
                * (⨆ i, ‖Φint σ s ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℍ) : ℂ) i‖) ^ k}
          ≤ ENNReal.ofReal (C * (k + 1) / lam) := by
  classical
  obtain ⟨C, hC, h'⟩ := bad_volume_cusp_X (D := D) (xData_of σ₀ s hs) γ h hh hper R hR hR1
  refine ⟨C, hC, fun σ htup k hk u hu huL lam hlam => ?_⟩
  have hw : WData D (fun i => phi N σ₀ (s i)) k (phi N σ u) := by
    have := wData_of (D := D) σ s hs k u hu huL (psiU_bddAbove D σ s hs k u hu huL)
    rwa [htup] at this
  have hmain := h' k (phi N σ u) hw lam hlam
  have e1 : supPsi D σ s k u = supPsiX D (fun i => phi N σ₀ (s i)) k (phi N σ u) := by
    show supPsiX D (fun i => phi N σ (s i)) k (phi N σ u) = _
    rw [htup]
  have e2 : ∀ (z : ℂ) (i : Fin r), Φint σ s z i = ATLINT.ext (N := N) (phi N σ₀ (s i)) z := fun z i => by
    show ATLINT.ext (N := N) (phi N σ (s i)) z = _
    rw [show phi N σ (s i) = phi N σ₀ (s i) from congrFun htup i]
  simp_rw [e1, e2]
  exact hmain

theorem random_good_covector (hs : IsEmbBasis N s) (σ₀ : AlgebraicClosure ℚ →+* ℂ)
    (hbdd : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) (k : ℕ) (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      BddAbove (Set.range fun τ : Gen D σ u => psiU D σ s k u τ))
    (hbox : ∀ (Bx yl yu : ℝ), 0 < yl → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) → ∀ lam : ℝ, 0 < lam →
        MeasureTheory.volume {z : ℂ | |z.re| ≤ Bx ∧ yl ≤ z.im ∧ z.im ≤ yu ∧
            ‖ATLINT.ext (N := N) (phi N σ u) z‖
              ≤ Real.exp (supPsi D σ s k u - lam) * (⨆ i, ‖Φint σ s z i‖) ^ k}
          ≤ ENNReal.ofReal (C * (k + 1) / lam))
    (hcusp : ∀ (γ : SL(2, ℤ)) (h : ℝ), 0 < h → h ∈ (CUSPATLAS.conjGamma0 N γ).strictPeriods →
      ∀ R : ℝ, 0 < R → R < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) → ∀ lam : ℝ, 0 < lam →
        MeasureTheory.volume {q : ℂ | q ∈ Metric.ball (0 : ℂ) R ∧ q ≠ 0 ∧
            ‖ATLINT.ext (N := N) (phi N σ u)
                ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℍ) : ℂ)‖
              ≤ Real.exp (supPsi D σ s k u - lam)
                * (⨆ i, ‖Φint σ s ((γ • UpperHalfPlane.ofComplex (Function.Periodic.invQParam h q) : ℍ) : ℂ) i‖) ^ k}
          ≤ ENNReal.ofReal (C * (k + 1) / lam)) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (FB N), (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (T : Finset (Place (AlgebraicClosure ℚ) (FB N))) (v : Place (AlgebraicClosure ℚ) (FB N)), B v = 0 →
      ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (FB N)),
        linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
        (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
        (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
        (∀ y, y ≠ v → (Za - Finsupp.single v (1 : ℤ)) y ≠ 0 →
          ∃ τ : ℍ, y.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) ∧
            secVal s y k u ≠ 0 ∧ supPsi D σ s k u - C₂ * (k + 1) ≤ psiU D σ s k u τ) :=
  PLBG.random_good_covector' D s hs σ₀ (fun σ k u hu huL => psiU_bddAbove D σ s hs k u hu huL)
    (fun Bx yl yu hyl => bad_volume_box D s hs σ₀ Bx yl yu hyl)
    (fun γ h hh hper R hR hR1 => bad_volume_cusp D s hs σ₀ γ h hh hper R hR hR1)

theorem main_analytic_of_iface (hs : IsEmbBasis N s) (σ₀ : AlgebraicClosure ℚ →+* ℂ)
    (hbdd : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) (k : ℕ) (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      BddAbove (Set.range fun τ : Gen D σ u => psiU D σ s k u τ))
    (hL0 : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) (k : ℕ) (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ (y : Place (AlgebraicClosure ℚ) (FB N)) (τ : ℍ),
        y.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) → secVal s y k u ≠ 0 →
        phiU σ s k u y = psiU D σ s k u τ)
    (hcuspval : ∀ (σ : AlgebraicClosure ℚ →+* ℂ) (k : ℕ) (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ (y : Place (AlgebraicClosure ℚ) (FB N)), jB N ∉ y.toValuationSubring → secVal s y k u ≠ 0 →
        phiU σ s k u y ≤ supPsi D σ s k u)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hgood : ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (FB N), (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (T : Finset (Place (AlgebraicClosure ℚ) (FB N))) (v : Place (AlgebraicClosure ℚ) (FB N)), B v = 0 →
      ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (FB N)),
        linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
        (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
        (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
        (∀ y, y ≠ v → (Za - Finsupp.single v (1 : ℤ)) y ≠ 0 →
          ∃ τ : ℍ, y.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) ∧
            secVal s y k u ≠ 0 ∧ supPsi D σ s k u - C₂ * (k + 1) ≤ psiU D σ s k u τ)) :
    ∀ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (FB N), (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (T : Finset (Place (AlgebraicClosure ℚ) (FB N))) (v y₀ : Place (AlgebraicClosure ℚ) (FB N)),
        B v = 0 → B y₀ = 0 →
      ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (FB N)),
        linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
        (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
        (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
        ((embDegree N : ℝ) - 1) * phiU σ s k u y₀ - (2 * ((embDegree N : ℝ) - 1) * C₂ + 2 * |(embDegree N : ℝ) - 1|) * k
          ≤ (Za - Finsupp.single v (1 : ℤ)).sum (fun y n => (n : ℝ) * phiU σ s k u y) := by
  intro σ htup k hk u hu huL B hB T v y₀ hBv hBy₀
  classical
  obtain ⟨a, Za, h1, h2, h3, h4, h5, h6, hzeros⟩ := hgood σ htup k hk u hu huL B hB T v hBv
  refine ⟨a, Za, h1, h2, h3, h4, h5, h6, ?_⟩
  set S : ℝ := supPsi D σ s k u with hS
  have hd1 : (0 : ℝ) ≤ (embDegree N : ℝ) - 1 := by
    unfold embDegree; push_cast; nlinarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have SV := fun w => L2.secVal_ne_zero_iff N s hs k u hu huL B hB w

  have hy₀S : phiU σ s k u y₀ ≤ S := by
    have hsv : secVal s y₀ k u ≠ 0 := (SV y₀).2 hBy₀
    by_cases hj : jB N ∈ y₀.toValuationSubring
    · obtain ⟨τ₀, -, hy⟩ := CUSPATLAS.placePoint D σ y₀ hj
      rw [hL0 σ k u hu huL y₀ τ₀ hy hsv]

      have hE0 := embDivisor_eq_zero_of_comap D σ y₀ τ₀ hy
      have hureg : u ∈ y₀.toValuationSubring := by
        refine y₀.mem_of_ord_nonneg hu ?_
        have := L2.neg_le_ord_of_mem _ huL hu y₀
        simp only [Finsupp.smul_apply, smul_eq_mul, hE0, mul_zero, neg_zero] at this
        exact this
      obtain ⟨P, hP, hsec, -⟩ := dict_values D σ s hs k u y₀ τ₀ hy hureg
      have hgen : τ₀ ∈ Gen D σ u := by
        intro h0
        apply (map_ne_zero σ).mpr hsv
        rw [hsec, h0, zero_mul]
      rw [hS]
      unfold supPsi
      exact le_ciSup (hbdd σ k u hu huL) (⟨τ₀, hgen⟩ : Gen D σ u)
    · exact hcuspval σ k u hu huL y₀ hj hsv

  have hothers : ∀ y, (Za - Finsupp.single v (1 : ℤ)) y ≠ 0 → S - C₂ * (k + 1) ≤ phiU σ s k u y := by
    intro y hy
    have hyv : y ≠ v := by
      rintro rfl
      simp [h4] at hy
    obtain ⟨τ, hyτ, hsv, hbound⟩ := hzeros y hyv hy
    rw [hL0 σ k u hu huL y τ hyτ hsv]
    exact hbound

  have Sa := fun w => L2.hypSec_facts N s hs a h1 Za h2 w
  have hnn : ∀ w, 0 ≤ (Za - Finsupp.single v (1 : ℤ)) w := by
    intro w
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · have := (Sa w).1; omega
  have htot := PLBALG.sum_cast_sub_single_eq s hs a h1 Za h2 v
  have hsum : (S - C₂ * (k + 1)) * ((embDegree N : ℝ) - 1)
      ≤ (Za - Finsupp.single v (1 : ℤ)).sum (fun y n => (n : ℝ) * phiU σ s k u y) := by
    rw [← htot]
    exact le_sum_mul_of_le _ hnn _ _ hothers
  have hmono := mul_le_mul_of_nonneg_left hy₀S hd1
  have hC₂k : ((embDegree N : ℝ) - 1) * C₂ * (k + 1) ≤ 2 * ((embDegree N : ℝ) - 1) * C₂ * k := by
    have h0 : 0 ≤ ((embDegree N : ℝ) - 1) * C₂ := mul_nonneg hd1 hC₂
    nlinarith
  have habs : 0 ≤ 2 * |(embDegree N : ℝ) - 1| * (k : ℝ) := by positivity
  nlinarith [hsum, hmono, hC₂k, habs]

end IFACE
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

theorem main_analytic (D : ComplexPlaceDictionary N) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (σ₀ : AlgebraicClosure ℚ →+* ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ,
      (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) →
      ∀ (k : ℕ), 0 < k → ∀ (u : FB N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (FB N), (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (T : Finset (Place (AlgebraicClosure ℚ) (FB N))) (v y₀ : Place (AlgebraicClosure ℚ) (FB N)),
        B v = 0 → B y₀ = 0 →
      ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (FB N)),
        linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
        (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
        (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
        ((embDegree N : ℝ) - 1) * phiU σ s k u y₀ - c * k
          ≤ (Za - Finsupp.single v (1 : ℤ)).sum (fun y n => (n : ℝ) * phiU σ s k u y) := by
  obtain ⟨C₂, hC₂, hgood⟩ := random_good_covector D s hs σ₀
    (fun σ k u hu huL => psiU_bddAbove D σ s hs k u hu huL)
    (fun Bx yl yu hyl => bad_volume_box D s hs σ₀ Bx yl yu hyl)
    (fun γ h hh hper R hR hR1 => bad_volume_cusp D s hs σ₀ γ h hh hper R hR hR1)
  have hd1 : (0 : ℝ) ≤ (embDegree N : ℝ) - 1 := by
    unfold embDegree; push_cast; nlinarith
  refine ⟨2 * ((embDegree N : ℝ) - 1) * C₂ + 2 * |(embDegree N : ℝ) - 1|,
    add_nonneg (mul_nonneg (mul_nonneg two_pos.le hd1) hC₂) (by positivity), ?_⟩
  exact main_analytic_of_iface D s hs σ₀
    (fun σ k u hu huL => psiU_bddAbove D σ s hs k u hu huL)
    (fun σ k u hu huL y τ hy hne => phiU_eq_psiU D σ s hs k u hu huL y τ hy hne)
    (fun σ k u hu huL y hyc hne => phiU_le_ciSup_of_cuspidal D σ s hs k u hu huL y hyc hne) C₂ hC₂ hgood

theorem main_for (D : ComplexPlaceDictionary N) (s : Fin r → FB N) (hs : IsEmbBasis N s)
    (σ₀ : AlgebraicClosure ℚ →+* ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ σ : AlgebraicClosure ℚ →+* ℂ,
      (fun i => phi N σ (s i)) = (fun i => phi N σ₀ (s i)) → Body s σ c := by
  obtain ⟨c, hc0, han⟩ := main_analytic D s hs σ₀
  refine ⟨c, hc0, fun σ htup => ?_⟩
  intro k u hu huL B hB T v y₀ hBv hBy₀
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact PLBALG.body_k0 s hs σ c u hu huL B T v y₀
  · exact han σ htup k hk u hu huL B hB T v y₀ hBv hBy₀

theorem pencil_lb (D : ComplexPlaceDictionary N) (s : Fin r → FB N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ σ : AlgebraicClosure ℚ →+* ℂ, Body s σ c₀ := by
  classical
  have hfin := CUSPATLAS.finite_range_phi_comp (N := N) s
  choose c hc0 hc using fun σ₀ => main_for D s hs σ₀
  have hmem : ∀ x ∈ hfin.toFinset, ∃ σ : AlgebraicClosure ℚ →+* ℂ, (fun i => phi N σ (s i)) = x :=
    fun x hx => by simpa using hfin.mem_toFinset.mp hx
  choose pre hpre using hmem
  let S0 : Finset (AlgebraicClosure ℚ →+* ℂ) := hfin.toFinset.attach.image fun x => pre x.1 x.2
  refine ⟨∑ σ₀ ∈ S0, c σ₀, fun σ => ?_⟩
  have hx : (fun i => phi N σ (s i)) ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨σ, rfl⟩
  have hσ₀ : pre _ hx ∈ S0 := Finset.mem_image.mpr ⟨⟨_, hx⟩, Finset.mem_attach _ _, rfl⟩
  have hb : Body s σ (c (pre _ hx)) := hc (pre _ hx) σ (by rw [hpre _ hx])
  exact hb.mono (Finset.single_le_sum (fun σ' _ => hc0 σ') hσ₀)

theorem solution_shape (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
        (v y₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), B v = 0 → B y₀ = 0 →
      ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
        (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
        (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
        ((embDegree N : ℝ) - 1) * (Real.log ‖σ (secVal s y₀ k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y₀ i)‖)) - c₀ * k
          ≤ (Za - Finsupp.single v (1 : ℤ)).sum
              (fun y n => (n : ℝ) * (Real.log ‖σ (secVal s y k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖))) := by
  obtain ⟨D⟩ := ModularCurve.exists_complexPlaceDictionary N
  obtain ⟨c₀, h⟩ := pencil_lb D s hs
  exact ⟨c₀, fun σ k u hu huL B hB T v y₀ hBv hBy₀ => h σ k u hu huL B hB T v y₀ hBv hBy₀⟩

end PLB
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge.CUSPATLAS"

open AlgebraicCurve ModularCurve in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
        (v y₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), B v = 0 → B y₀ = 0 →
      ∃ (a : Fin r → AlgebraicClosure ℚ) (Za : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        linSec s a ≠ 0 ∧ (∀ w, Za w = w.ord (linSec s a) + embDivisor N w) ∧
        (∑ i, evalVec s v i * a i = 0) ∧ Za v = 1 ∧
        (∀ w ∈ T, w ≠ v → Za w = 0) ∧ (∀ w, w ≠ v → Za w = 0 ∨ B w = 0) ∧
        ((embDegree N : ℝ) - 1) * (Real.log ‖σ (secVal s y₀ k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y₀ i)‖)) - c₀ * k
          ≤ (Za - Finsupp.single v (1 : ℤ)).sum
              (fun y n => (n : ℝ) * (Real.log ‖σ (secVal s y k u)‖ - (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s y i)‖))) :=
  PLB.solution_shape N s hs

end
end S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge
end P2MW
export P2MW.S_ModularCurve_JZero_exists_hyperplaneSection_sum_log_secVal_ge (solution)
