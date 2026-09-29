-- Prove2me | solution 1 for ModularCurve.MultCovering.crossComparison_annIn_annIn_of_jWidth_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/dd3d6082-dc9f-5567-82f8-80e702a8165f

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringLink
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_ModularCurve_MultCovering_ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one
import Theorems.Thm_ModularCurve_MultCovering_one_le_hasseExp
import Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
import Theorems.Thm_ModularCurve_MultCovering_infChart_residue_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_MultCovering_infChart_goodFamily_residue_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_goodFamily_zero_eq_one
import Theorems.Thm_ModularCurve_MultCovering_linkMatrixInv_mul
import Theorems.Thm_ModularCurve_MultCovering_linkMatrix_mul_inv
import Theorems.Thm_ModularCurve_MultCovering_eq_sum_linkMatrix_smul_goodFamily
import Theorems.Thm_ModularCurve_MultCovering_linkBudget_spec
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.AlgebraicCurve IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.ModularCurve.MultCovering"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord Place.ord_zero Place.ord_inv HasPrincipalDivisors Place.evalAt_one prox evalVec Place.mem_of_ord_nonneg Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends prox_eq_neg_log_iSup_sub_of_chart exists_evalVec_eq_smul_mulVec_of_eq_sum_smul prox_smul_smul abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le Place.isRational_of_isAlgClosed Place.ord_finset_prod'"
p2m_open "AlgebraicCurve"

private theorem abv_sub_le_max {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (a b : L) :
    μ (a - b) ≤ max (μ a) (μ b) := by
  rcases le_total (μ b) (μ a) with hab | hab
  ·
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [map_zero] at hab
      have hb : b = 0 := μ.eq_zero.1 (le_antisymm hab (μ.nonneg b))
      simp [hb]
    have hq : b * a⁻¹ ∈ A := (hμA _).2 (by
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ (μ.pos ha0)).2 (by simpa using hab))
    have h1 : 1 - b * a⁻¹ ∈ A := sub_mem (one_mem _) hq
    have h2 : μ (1 - b * a⁻¹) ≤ 1 := (hμA _).1 h1
    have : a - b = a * (1 - b * a⁻¹) := by field_simp
    rw [this, map_mul]
    calc μ a * μ (1 - b * a⁻¹) ≤ μ a * 1 := mul_le_mul_of_nonneg_left h2 (μ.nonneg a)
      _ = μ a := mul_one _
      _ ≤ max (μ a) (μ b) := le_max_left _ _
  · rcases eq_or_ne b 0 with rfl | hb0
    · rw [map_zero] at hab
      have ha : a = 0 := μ.eq_zero.1 (le_antisymm hab (μ.nonneg a))
      simp [ha]
    have hq : a * b⁻¹ ∈ A := (hμA _).2 (by
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ (μ.pos hb0)).2 (by simpa using hab))
    have h1 : a * b⁻¹ - 1 ∈ A := sub_mem hq (one_mem _)
    have h2 : μ (a * b⁻¹ - 1) ≤ 1 := (hμA _).1 h1
    have : a - b = b * (a * b⁻¹ - 1) := by field_simp
    rw [this, map_mul]
    calc μ b * μ (a * b⁻¹ - 1) ≤ μ b * 1 := mul_le_mul_of_nonneg_left h2 (μ.nonneg b)
      _ = μ b := mul_one _
      _ ≤ max (μ a) (μ b) := le_max_right _ _

private theorem abv_eq_one_of_isUnit_vs {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L} (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : A)) : μ a = 1 := by
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : a * (b : L) = 1 := by
    have := congrArg (fun t : A => (t : L)) hb
    simpa using this
  have h1 : μ a * μ (b : L) = 1 := by rw [← map_mul, hb', map_one]
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  have hb1 : μ (b : L) ≤ 1 := (hμA (b : L)).1 b.2
  have ha0 : 0 ≤ μ a := μ.nonneg a
  exact le_antisymm ha1 (by nlinarith)

private theorem abv_lt_one_of_mem_maximalIdeal_vs {L : Type*} [Field L]
    {A : ValuationSubring L} (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L}
    (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A) : μ a < 1 := by
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  refine lt_of_le_of_ne ha1 fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at h1
  have hinv : a⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

private theorem residue_eq_zero_of_mem_maximalIdeal' {L : Type*} [Field L] {A : ValuationSubring L}
    {a : L} (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A) :
    IsLocalRing.residue A ⟨a, ha⟩ = 0 :=
  (IsLocalRing.residue_eq_zero_iff _).2 hm

private theorem abv_evalAt_eq_zpow_of_isAttached
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (IsLocalRing.ResidueField A) Fbar)
    (hatt : An.IsAttached C x) (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hzf : ∀ Q ∈ An.dom, Q.ord f = 0) :
    ∀ Q ∈ An.dom, 0 < μ (Q.evalAt An.param) ∧ μ (Q.evalAt An.param) < 1 ∧
      μ (Q.evalAt f) = μ (Q.evalAt An.param) ^ (x.ord (C.residue ⟨f, hf⟩)) := by
  intro Q hQ
  obtain ⟨-, hzC, -, hlaw⟩ := hatt
  obtain ⟨hw, hunit⟩ := hlaw f hf hres hzf Q hQ
  obtain ⟨-, -, ⟨hzA, hzmax⟩, hz0, -⟩ := An.mem_dom Q hQ
  have hμz1 : μ (Q.evalAt An.param) < 1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA hzA hzmax
  have hμz0 : 0 < μ (Q.evalAt An.param) := μ.pos hz0
  have hunit1 := abv_eq_one_of_isUnit_vs μ hμA hw hunit
  rw [map_mul, map_zpow₀, zpow_neg] at hunit1
  exact ⟨hμz0, hμz1, (mul_inv_eq_one₀ (zpow_ne_zero _ hμz0.ne')).1 hunit1⟩

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField ord ord_zero ord_mul ord_inv ord_coe_unit ord_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring adicValuation_le_one_of_mem adicValuation_le_one_iff IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_one mem_of_ord_nonneg isRational_of_isAlgClosed ord_finset_prod'" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_mul' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_mul'"
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_sub' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_algebraMap' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_prod' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {ι : Type*} (S : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ S, f i ∈ v.toValuationSubring) :
    (∏ i ∈ S, f i) ∈ v.toValuationSubring ∧ v.evalAt (∏ i ∈ S, f i) = ∏ i ∈ S, v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨by simp, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨hmem, heq⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfi : f i ∈ v.toValuationSubring := hf i (Finset.mem_insert_self _ _)
    refine ⟨?_, ?_⟩
    · rw [Finset.prod_insert hi]; exact mul_mem hfi hmem
    · rw [Finset.prod_insert hi, Finset.prod_insert hi, v.evalAt_mul' hv hfi hmem, heq]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul' hv (pow_mem hf n) hf, ih]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_neg' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (f : F) : v.ord (-f) = v.ord f := by
  unfold Place.ord
  rw [Valuation.map_neg]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_prod' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {ι : Type*} (S : Finset ι) (f : ι → F) (hf : ∀ i ∈ S, f i ≠ 0) :
    v.ord (∏ i ∈ S, f i) = ∑ i ∈ S, v.ord (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      v.ord_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.2 fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_algebraMap' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hmem := v.algebraMap_mem' c
  have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
    rw [← map_inv₀]; exact v.algebraMap_mem' _
  have h1 : 0 ≤ v.ord (algebraMap K F c) := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hmem) with h | h
    · simp [h]
    · exact h
  have h2 : 0 ≤ v.ord (algebraMap K F c)⁻¹ := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hmem') with h | h
    · simp [h]
    · exact h
  rw [v.ord_inv] at h2
  omega

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hf) with h | h
  · simp [h]
  · exact h

end Place
p2m_export "AlgebraicCurve" "Place.ord_nonneg_of_mem'"
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.isUnit_of_ord_eq_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hϖ
  rw [h, zpow_zero, mul_one] at hu
  have : (⟨f, hf⟩ : v.toValuationSubring) = u := Subtype.ext hu
  rw [this]
  exact Units.isUnit u

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_eq_zero_of_evalAt_ne_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne (v.ord_nonneg_of_mem' hf) (Ne.symm hne)
  apply h
  have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have : v.ord f = 0 := by
      have := v.ord_coe_unit u
      rwa [hu] at this
    omega
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

private theorem inv_mem_of_isUnit' {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
    (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (u : O) = 0 := by rw [hu]; rfl
    exact u.ne_zero this
  have hval : ((u⁻¹ : Oˣ) : O).1 = x⁻¹ := by
    have h1 := congrArg (fun t : O => (t : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  exact hval ▸ ((u⁻¹ : Oˣ) : O).2

namespace ComponentChart p2m_export "AlgebraicCurve.ComponentChart" "integers residue nodes ker_residue dom" end ComponentChart
namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.isUnit_of_residue_ne_zero'
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]
    exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.isUnit_of_residue_ne_zero'"
namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.residue_inv'
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.residue_inv'"
end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint jWidth ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jBar mAnnuli modulusExp Fbar ChartCtx infChart chart src tgt ssValue ssValue_injective nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one one_le_hasseExp infChart_residue_goodFamily eq_mAnnuli_add_one_of_isEmbBasis infChart_goodFamily_residue_ne_zero goodFamily_zero_eq_one linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.AlgebraicCurve IsLocalRing"

section GenericHelpers

theorem evalAt_mul_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

theorem evalAt_algebraMap_D {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

theorem minor_mulVec_D {K : Type*} [Field K] {r : ℕ} (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) (i j : Fin r) :
    M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i
      = ∑ p : Fin r × Fin r, M i p.1 * M j p.2 * (x p.1 * y p.2 - x p.2 * y p.1) := by
  have hswap : ∑ p : Fin r × Fin r, M j p.1 * x p.1 * (M i p.2 * y p.2)
      = ∑ p : Fin r × Fin r, M j p.2 * x p.2 * (M i p.1 * y p.1) := by
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hswap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

end GenericHelpers

section FamilyFacts
variable {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)

theorem goodFamily_ne_zero' (i : Fin r) : goodFamily Φ i ≠ 0 := Φ.t_basis.1.ne_zero i

theorem goodFamilyZero_eq_inv_mul' (l : Fin r) :
    goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * goodFamily Φ l := rfl

end FamilyFacts

section CtxFacts
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
  (Γ : ChartCtx p A) (Δ : AnnCtx Γ)

theorem modulus_dvd' (e : Fin (mAnnuli p)) : ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    (p : AlgebraicClosure ℚ) ^ modulusExp = ((Δ.annIn e).modulus : AlgebraicClosure ℚ) * a := by
  have hw : jWidth (ssValue Γ e) ≤ 3 := by
    unfold jWidth; split_ifs <;> norm_num
  refine ⟨(p : AlgebraicClosure ℚ) ^ (3 - jWidth (ssValue Γ e)), pow_mem (natCast_mem A p) _, ?_⟩
  have hm : ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    show (((Δ.An e).modulus : ↥A) : AlgebraicClosure ℚ) = _
    rw [Δ.modulus_eq e]; push_cast; rfl
  rw [hm, ← pow_add, show modulusExp = 3 from rfl, Nat.add_sub_cancel' hw]

end CtxFacts

theorem annOut_wide' (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∃ Q₁ ∈ (Δ.annOut e).dom, ∃ Q₂ ∈ (Δ.annOut e).dom,
        μ (Q₁.evalAt (Δ.annOut e).param) ≠ μ (Q₂.evalAt (Δ.annOut e).param) := by
  intro μ hμA
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := Δ.exists_mem_dom_abv_evalAt_param_ne e μ hμA
  refine ⟨Q₁, hdom ▸ hQ₁, Q₂, hdom ▸ hQ₂, ?_⟩
  have key : ∀ Q ∈ (Δ.annIn e).dom,
      μ (Q.evalAt (Δ.annOut e).param) * μ (Q.evalAt (Δ.annIn e).param)
        = μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) := by
    intro Q hQ
    obtain ⟨hrat, hzin, -, hz0, -⟩ := (Δ.annIn e).mem_dom Q hQ
    obtain ⟨-, hzout, -⟩ := (Δ.annOut e).mem_dom Q (hdom ▸ hQ)
    rw [← map_mul, ← evalAt_mul_D Q hrat hzout hzin, htwo, evalAt_algebraMap_D]
  intro heq
  apply hne
  have h1 := key Q₁ hQ₁
  have h2 := key Q₂ hQ₂
  rw [heq] at h1
  have h12 := h1.trans h2.symm
  have hne0 : μ (Q₂.evalAt (Δ.annOut e).param) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (μ.pos hmod0).ne' h2.symm
  exact mul_left_cancel₀ hne0 h12

end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint jWidth ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jBar mAnnuli modulusExp Fbar ChartCtx infChart chart src tgt ssValue ssValue_injective nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one one_le_hasseExp infChart_residue_goodFamily eq_mAnnuli_add_one_of_isEmbBasis infChart_goodFamily_residue_ne_zero goodFamily_zero_eq_one linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.AlgebraicCurve IsLocalRing"

section ResidueLinePort

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem ord_charLGeomPlaceOfPoint_jBar_sub' (k : Type) [Field k] [DecidableEq k] (a c : k) :
    (charLGeomPlaceOfPoint k a).ord (jBar k - algebraMap k ↥(modularFunctionFieldC k 1) c) = if c = a then 1 else 0 :=
  ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a c

theorem jBar_sub_algebraMap_ne_zero' (k : Type) [Field k] [DecidableEq k] (c : k) :
    jBar k - algebraMap k ↥(modularFunctionFieldC k 1) c ≠ 0 := by
  intro h
  have := ord_charLGeomPlaceOfPoint_jBar_sub' k c c
  rw [h, Place.ord_zero, if_pos rfl] at this
  exact zero_ne_one this

theorem jBar_ne_zero' (k : Type) [Field k] [DecidableEq k] : jBar k ≠ 0 := by
  simpa using jBar_sub_algebraMap_ne_zero' k 0

private theorem _root_.AlgebraicCurve.Place.ord_finset_prod' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

p2m_alias "P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.AlgebraicCurve.Place.ord_finset_prod'" "AlgebraicCurve.Place.ord_finset_prod'"
theorem ssPolyBar_ne_zero' : ssPolyBar Γ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun e _ => jBar_sub_algebraMap_ne_zero' _ _

theorem ord_nodeTgt_ssPolyBar' (e : Fin (mAnnuli p)) : (nodeTgt Γ e).ord (ssPolyBar Γ) = 1 := by
  show (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord _ = 1
  rw [ssPolyBar, Place.ord_finset_prod' _ _ _ (fun e' _ => jBar_sub_algebraMap_ne_zero' _ _)]
  simp_rw [ord_charLGeomPlaceOfPoint_jBar_sub', (ssValue_injective Γ).eq_iff]
  simp [Finset.sum_ite_eq']

theorem ord_nodeTgt_jBar' (e : Fin (mAnnuli p)) :
    (nodeTgt Γ e).ord (jBar (IsLocalRing.ResidueField ↥A)) = if (0 : IsLocalRing.ResidueField ↥A) = ssValue Γ e then 1 else 0 := by
  have h := ord_charLGeomPlaceOfPoint_jBar_sub' (IsLocalRing.ResidueField ↥A) (ssValue Γ e) 0
  rw [map_zero, sub_zero] at h
  exact h

theorem nodeTgt_isRational' (e : Fin (mAnnuli p)) : (nodeTgt Γ e).IsRational := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  let eqv := ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A)
  letI : Algebra (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A (tgt p e)) := eqv.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A (tgt p e)) :=
    IsScalarTower.of_algebraMap_eq fun c => (eqv.commutes c).symm
  haveI : FiniteDimensional (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A (tgt p e)) := by
    let L : RatFunc (IsLocalRing.ResidueField ↥A) ≃ₗ[RatFunc (IsLocalRing.ResidueField ↥A)] Fbar A (tgt p e) :=
      { eqv.toRingEquiv.toAddEquiv with
        map_smul' := fun r y => by
          show eqv (r * y) = eqv r * eqv y
          exact map_mul eqv r y }
    exact L.finiteDimensional
  exact Place.isRational_of_isAlgClosed _

end ResidueLinePort

end ModularCurve.MultCovering

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace ModularCurve
p2m_export "ModularCurve" "IsEmbBasis modularFunctionFieldBar modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint jWidth ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jBar mAnnuli modulusExp Fbar ChartCtx infChart chart src tgt ssValue ssValue_injective nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily linkMatrix linkMatrixInv linkBudget compConst compConst_eq ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one one_le_hasseExp infChart_residue_goodFamily eq_mAnnuli_add_one_of_isEmbBasis infChart_goodFamily_residue_ne_zero goodFamily_zero_eq_one linkMatrixInv_mul linkMatrix_mul_inv eq_sum_linkMatrix_smul_goodFamily linkBudget_spec zeroChart_residue_goodFamilyZero_ne_zero abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom"
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.AlgebraicCurve IsLocalRing"

section TubeSepTangent

private theorem abv_sub_eq_of_abv_lt {L : Type*} [Field L] (μ : AbsoluteValue L ℝ) (hμ : IsNonarchimedean μ)
    {a b : L} (h : μ b < μ a) : μ (a - b) = μ a := by
  apply le_antisymm
  · have := hμ a (-b)
    rw [← sub_eq_add_neg, μ.map_neg] at this
    exact this.trans (max_le le_rfl h.le)
  · have := hμ (a - b) b
    rw [sub_add_cancel] at this
    rcases le_max_iff.1 this with h1 | h1
    · exact h1
    · exact absurd h1 (not_le.2 h)

private theorem Place.evalAt_add' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem aeval_jBar_mem_and_evalAt {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (e : Fin (mAnnuli p))
    (q : Polynomial (IsLocalRing.ResidueField ↥A)) :
    Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) q ∈ (nodeTgt Γ e).toValuationSubring ∧
    (nodeTgt Γ e).evalAt (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) q) = q.eval (ssValue Γ e) := by
  have hxrat := nodeTgt_isRational' Γ e
  have hjreg : jBar (IsLocalRing.ResidueField ↥A) ∈ (nodeTgt Γ e).toValuationSubring :=
    Place.mem_of_ord_nonneg _ (jBar_ne_zero' _) (by rw [ord_nodeTgt_jBar']; split_ifs <;> norm_num)
  have hjval : (nodeTgt Γ e).evalAt (jBar (IsLocalRing.ResidueField ↥A)) = ssValue Γ e := by
    have hpos : (nodeTgt Γ e).ord (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e)) = 1 := by
      have h := ord_charLGeomPlaceOfPoint_jBar_sub' (IsLocalRing.ResidueField ↥A) (ssValue Γ e) (ssValue Γ e)
      rw [if_pos rfl] at h
      exact h
    have hreg : jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e) ∈ (nodeTgt Γ e).toValuationSubring :=
      sub_mem hjreg ((nodeTgt Γ e).algebraMap_mem' _)
    have h0 : (nodeTgt Γ e).evalAt (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e)) = 0 := by
      by_contra hne
      have := Place.ord_eq_zero_of_evalAt_ne_zero' _ hreg hne
      exact zero_ne_one (this.symm.trans hpos)
    rw [Place.evalAt_sub' _ hxrat hjreg ((nodeTgt Γ e).algebraMap_mem' _), Place.evalAt_algebraMap', sub_eq_zero] at h0
    exact h0
  induction q using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C, Polynomial.eval_C]
    exact ⟨(nodeTgt Γ e).algebraMap_mem' _, Place.evalAt_algebraMap' _ _⟩
  | add f g hf hg =>
    rw [map_add, Polynomial.eval_add]
    exact ⟨add_mem hf.1 hg.1, by rw [Place.evalAt_add' _ hxrat hf.1 hg.1, hf.2, hg.2]⟩
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Polynomial.eval_mul, Polynomial.eval_X]
    exact ⟨mul_mem h.1 hjreg, by rw [Place.evalAt_mul' _ hxrat h.1 hjreg, h.2, hjval]⟩

theorem tubeMember_value_D (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (e : Fin (mAnnuli p))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ) (hμA : ∀ a : (AlgebraicClosure ℚ), a ∈ A ↔ μ a ≤ 1)
    (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hR : R ∈ (Δ.annIn e).dom) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hout : ∀ Q ∈ (Δ.annIn e).dom, Q.ord (goodFamily Φ l) ≠ 0 →
      μ (Q.evalAt (Δ.annOut e).param) < μ (R.evalAt (Δ.annOut e).param))
    (hint : goodFamily Φ l ∈ (chart Γ (tgt p e)).integers) (hzoC : (Δ.annOut e).param ∈ (chart Γ (tgt p e)).integers) :
    ∃ hmem : R.evalAt (goodFamily Φ l) * (R.evalAt (Δ.annOut e).param)
        ^ (-((nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩))) ∈ A,
      IsUnit (⟨_, hmem⟩ : A) ∧
      IsLocalRing.residue A ⟨_, hmem⟩ = (nodeTgt Γ e).evalAt ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩
        * ((chart Γ (tgt p e)).residue ⟨(Δ.annOut e).param, hzoC⟩) ^ (-((nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩)))) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  have hattOut := Δ.attached_tgt e
  have hattIn := Δ.attached_src e
  obtain ⟨hintI, hresI⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have hres : (chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩ ≠ 0 := hresI l
  set c' : (AlgebraicClosure ℚ) := (p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l with hc'
  have hc'0 : c' ≠ 0 := pow_ne_zero _ hp0
  have hc'A : c' ∈ A := pow_mem (natCast_mem A p) _
  have heqZ : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * goodFamily Φ l = goodFamilyZero Φ.toFamData l := by
    rw [goodFamilyZero_eq_inv_mul']
  have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * goodFamily Φ l ∈ (chart Γ (src p e)).integers := by
    rw [heqZ]; exact hintZ l
  have hres' : (chart Γ (src p e)).residue ⟨_, hC'⟩ ≠ 0 := by
    have e1 : (⟨_, hC'⟩ : (chart Γ (src p e)).integers) = ⟨goodFamilyZero Φ.toFamData l, hintZ l⟩ := Subtype.ext heqZ
    rw [e1]; exact hresZ l
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (goodFamily Φ l) := by
    intro Q hQ
    rw [hdom] at hQ
    exact Place.ord_nonneg_of_mem' Q (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e Q hQ l hl).1
  have hwide := annOut_wide' p A hA Γ Δ e μ hμA
  have hx : (nodeTgt Γ e).IsRational := nodeTgt_isRational' Γ e
  have hmod0' : ((Δ.annOut e).modulus : (AlgebraicClosure ℚ)) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn e).param * (Δ.annOut e).param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((Δ.annOut e).modulus : (AlgebraicClosure ℚ)) := by
    rw [mul_comm (Δ.annIn e).param, hmod]; exact htwo
  have hR' : R ∈ (Δ.annOut e).dom := by rw [hdom]; exact hR
  have hout' : ∀ Q ∈ (Δ.annOut e).dom, Q.ord (goodFamily Φ l) ≠ 0 →
      μ (Q.evalAt (Δ.annOut e).param) < μ (R.evalAt (Δ.annOut e).param) := by
    intro Q hQ; rw [hdom] at hQ; exact hout Q hQ
  exact AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo' (chart Γ (tgt p e)) (nodeTgt Γ e) hattOut hx
    (chart Γ (src p e)) (nodeSrc Γ e) hattIn hwide (goodFamily Φ l) hint hres c' hc'0 hc'A hC' hres' hpole hzoC R hR' hout'

theorem tube_rows_W1 (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (e : Fin (mAnnuli p)) (hwe : jWidth (ssValue Γ e) = 1)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ) (hμA : ∀ a : (AlgebraicClosure ℚ), a ∈ A ↔ μ a ≤ 1)
    (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hR : R ∈ (Δ.annIn e).dom)
    (hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers)
    (P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A))
    (hP : ∀ l : Fin r, 1 ≤ (l : ℕ) → (P l).natDegree + 1 ≤ mAnnuli p ∧
      (infChart Γ).residue ⟨goodFamily Φ l, hint l⟩ = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) :
    R.IsRational ∧ 0 < μ (R.evalAt (Δ.annOut e).param) ∧
    μ ((p : (AlgebraicClosure ℚ))) ^ modulusExp < μ (R.evalAt (Δ.annOut e).param) ∧
    R.evalAt (Δ.annOut e).param ≠ 0 ∧
    (∀ l : Fin r, 1 ≤ (l : ℕ) → goodFamily Φ l ∈ R.toValuationSubring ∧ μ (R.evalAt (goodFamily Φ l)) < 1) ∧
    ∃ κ : (IsLocalRing.ResidueField ↥A), κ ≠ 0 ∧ ∀ l : Fin r, 1 ≤ (l : ℕ) →
      ∃ h : R.evalAt (goodFamily Φ l) * (R.evalAt (Δ.annOut e).param)⁻¹ ∈ A,
        IsLocalRing.residue A ⟨_, h⟩ = κ * (P l).eval (ssValue Γ e) ∧
        ((P l).eval (ssValue Γ e) ≠ 0 → IsUnit (⟨_, h⟩ : A)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  have hR' : R ∈ (Δ.annOut e).dom := by rw [hdom]; exact hR
  obtain ⟨hRrat, hzR, ⟨hzRA, hzRmax⟩, hzR0, mR, hmR, hπR⟩ := (Δ.annOut e).mem_dom R hR'
  set z := (Δ.annOut e).param with hz_def
  have hρ0 : 0 < μ (R.evalAt z) := μ.pos hzR0
  have hπlt : μ ((p : (AlgebraicClosure ℚ))) ^ modulusExp < μ (R.evalAt z) := by
    obtain ⟨b, hbA, hpb⟩ := modulus_dvd' Γ Δ e
    have hμm : μ (mR : (AlgebraicClosure ℚ)) < 1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA mR.2 (by simpa using hmR)
    have h1 : μ ((p : (AlgebraicClosure ℚ))) ^ modulusExp ≤ μ (((Δ.annOut e).modulus : (AlgebraicClosure ℚ))) := by
      rw [← map_pow, hpb, ← hmod, map_mul]
      calc μ (↑(Δ.annOut e).modulus) * μ b ≤ μ (↑(Δ.annOut e).modulus) * 1 :=
            mul_le_mul_of_nonneg_left ((hμA b).1 hbA) (μ.nonneg _)
        _ = _ := mul_one _
    have h2 : μ (((Δ.annOut e).modulus : (AlgebraicClosure ℚ))) < μ (R.evalAt z) := by
      rw [hπR, map_mul]
      calc μ (R.evalAt (Δ.annOut e).param) * μ (mR : (AlgebraicClosure ℚ)) < μ (R.evalAt (Δ.annOut e).param) * 1 :=
            mul_lt_mul_of_pos_left hμm (μ.pos hzR0)
        _ = μ (R.evalAt z) := mul_one _
    exact lt_of_le_of_lt h1 h2
  have hsmall : ∀ l : Fin r, 1 ≤ (l : ℕ) → goodFamily Φ l ∈ R.toValuationSubring ∧ μ (R.evalAt (goodFamily Φ l)) < 1 :=
    fun l hl => abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e R hR l hl
  refine ⟨hRrat, hρ0, hπlt, hzR0, hsmall, ?_⟩
  have hattOut := Δ.attached_tgt e
  obtain ⟨-, hzoC, hzoord, -⟩ := hattOut
  set C := (chart Γ (tgt p e)) with hC_def
  set xe := (nodeTgt Γ e) with hxe_def
  have hxrat : xe.IsRational := nodeTgt_isRational' Γ e
  have hintC : ∀ i, goodFamily Φ i ∈ C.integers := hint
  have hordss : xe.ord (ssPolyBar Γ) = 1 := ord_nodeTgt_ssPolyBar' Γ e
  have hss0 : ssPolyBar Γ ≠ 0 := ssPolyBar_ne_zero' Γ
  have hzbar0 : C.residue ⟨z, hzoC⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hzoord; exact zero_ne_one hzoord

  have hreg1 : ssPolyBar Γ * (C.residue ⟨z, hzoC⟩) ^ (-(1 : ℤ)) ∈ xe.toValuationSubring := by
    refine Place.mem_of_ord_nonneg xe (mul_ne_zero hss0 (zpow_ne_zero _ hzbar0)) ?_
    rw [xe.ord_mul hss0 (zpow_ne_zero _ hzbar0), xe.ord_zpow, hordss, hzoord]; norm_num
  set κ : (IsLocalRing.ResidueField ↥A) := xe.evalAt (ssPolyBar Γ * (C.residue ⟨z, hzoC⟩) ^ (-(1 : ℤ))) with hκ_def
  have hκ0 : κ ≠ 0 := by
    intro h0
    have h00 : xe.ord (ssPolyBar Γ * (C.residue ⟨z, hzoC⟩) ^ (-(1 : ℤ))) = 0 := by
      rw [xe.ord_mul hss0 (zpow_ne_zero _ hzbar0), xe.ord_zpow, hordss, hzoord]; norm_num
    have hu := Place.isUnit_of_ord_eq_zero' xe hreg1 (mul_ne_zero hss0 (zpow_ne_zero _ hzbar0)) h00
    have hr0 : IsLocalRing.residue xe.toValuationSubring ⟨_, hreg1⟩ ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu
    apply hr0
    rw [← xe.algebraMap_evalAt hxrat hreg1, ← hκ_def, h0, map_zero]
  refine ⟨κ, hκ0, fun l hl => ?_⟩
  obtain ⟨hdeg, hresl⟩ := hP l hl
  obtain ⟨hPreg, hPval⟩ := aeval_jBar_mem_and_evalAt Γ e (P l)
  have hresl' : C.residue ⟨goodFamily Φ l, hintC l⟩ = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) := hresl
  have hPne : Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) ≠ 0 := by
    intro h0
    apply (infChart_goodFamily_residue_ne_zero p A hA Γ Φ).2 l
    show C.residue ⟨goodFamily Φ l, _⟩ = 0
    rw [hresl', h0, mul_zero]
  have hordP : 0 ≤ xe.ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) := Place.ord_nonneg_of_mem' xe hPreg
  set a : ℤ := xe.ord (C.residue ⟨goodFamily Φ l, hintC l⟩) with ha_def
  have ha : a = 1 + xe.ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) := by
    rw [ha_def, hresl', xe.ord_mul hss0 hPne, hordss]
  have ha1 : 1 ≤ a := by omega
  have htres0 : C.residue ⟨goodFamily Φ l, hintC l⟩ ≠ 0 := by rw [hresl']; exact mul_ne_zero hss0 hPne

  have htR : goodFamily Φ l ∈ R.toValuationSubring := (hsmall l hl).1
  have hordzR : R.ord z = 0 := Place.ord_eq_zero_of_evalAt_ne_zero' R hzR hzR0
  have hz0 : z ≠ 0 := by
    intro h0; apply hzbar0
    have : (⟨z, hzoC⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hzinvR : z⁻¹ ∈ R.toValuationSubring := inv_mem_of_isUnit' hzR (Place.isUnit_of_ord_eq_zero' R hzR hz0 hordzR)
  have hzinvval : R.evalAt z⁻¹ = (R.evalAt z)⁻¹ := by
    have h1 : R.evalAt (z * z⁻¹) = R.evalAt z * R.evalAt z⁻¹ := Place.evalAt_mul' R hRrat hzR hzinvR
    rw [mul_inv_cancel₀ hz0, show (1 : (modularFunctionFieldBar (1 * p))) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) 1 from (map_one _).symm,
      Place.evalAt_algebraMap'] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm).symm ▸ rfl
  have hXval : R.evalAt (goodFamily Φ l * z⁻¹) = R.evalAt (goodFamily Φ l) * (R.evalAt z)⁻¹ := by
    rw [Place.evalAt_mul' R hRrat htR hzinvR, hzinvval]
  by_cases hPl : (P l).eval (ssValue Γ e) ≠ 0
  ·
    have h0' : xe.ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) = 0 := by
      apply Place.ord_eq_zero_of_evalAt_ne_zero' xe hPreg
      rw [hPval]; exact hPl
    have hone : a = 1 := by rw [ha, h0']; norm_num
    have hord1 : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩) = 1 := hone
    have hzf := ord_goodFamily_eq_zero_of_ord_residue_eq_one_of_jWidth_eq_one p A hA Γ Δ Φ e hwe l hl (hint l) hord1
    have hout : ∀ Q ∈ (Δ.annIn e).dom, Q.ord (goodFamily Φ l) ≠ 0 →
        μ (Q.evalAt (Δ.annOut e).param) < μ (R.evalAt (Δ.annOut e).param) := fun Q hQ hne => absurd (hzf Q hQ) hne
    obtain ⟨hmem, hunit, hresid⟩ := tubeMember_value_D p A hA Γ Δ Φ e μ hμ hμA R hR l hl hout (hintC l) hzoC
    have e1 : R.evalAt (goodFamily Φ l) * (R.evalAt z) ^ (-a) = R.evalAt (goodFamily Φ l) * (R.evalAt z)⁻¹ := by
      rw [hone, zpow_neg_one]
    have hX : R.evalAt (goodFamily Φ l) * (R.evalAt z)⁻¹ ∈ A := e1 ▸ hmem
    have eX : (⟨_, hX⟩ : A) = ⟨_, hmem⟩ := (Subtype.ext e1).symm
    refine ⟨hX, ?_, fun _ => by rw [eX]; exact hunit⟩
    rw [eX, hresid, ← ha_def, hone, hresl']
    have : ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) * C.residue ⟨z, hzoC⟩ ^ (-(1 : ℤ))
        = (ssPolyBar Γ * C.residue ⟨z, hzoC⟩ ^ (-(1 : ℤ))) * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) := by ring
    rw [this, Place.evalAt_mul' xe hxrat hreg1 hPreg, hPval]
  ·
    push_neg at hPl
    have ha2 : 2 ≤ a := by
      rcases eq_or_lt_of_le ha1 with h1 | h1
      · exfalso
        have h0' : xe.ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) = 0 := by omega
        have hu := Place.isUnit_of_ord_eq_zero' xe hPreg hPne h0'
        have hr0 : IsLocalRing.residue xe.toValuationSubring ⟨_, hPreg⟩ ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu
        apply hr0
        rw [← xe.algebraMap_evalAt hxrat hPreg, hPval, hPl, map_zero]
      · omega
    haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
    have hattOut' := Δ.attached_tgt e
    have hattIn := Δ.attached_src e
    have hattIn' := Δ.attached_src e
    obtain ⟨-, hziC, hziord, -⟩ := hattIn'
    set C' := (chart Γ (src p e)) with hC'_def
    set zi := (Δ.annIn e).param with hzi_def
    have hzires0 : C'.residue ⟨zi, hziC⟩ ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hziord; exact zero_ne_one hziord

    have hzunit : IsUnit (⟨z, hzoC⟩ : C.integers) := C.isUnit_of_residue_ne_zero' hzoC hzbar0
    have hzinvC : z⁻¹ ∈ C.integers := inv_mem_of_isUnit' hzoC hzunit
    have hhC : goodFamily Φ l * z⁻¹ ∈ C.integers := mul_mem (hintC l) hzinvC
    have hhres : C.residue ⟨goodFamily Φ l * z⁻¹, hhC⟩ = C.residue ⟨goodFamily Φ l, hintC l⟩ * (C.residue ⟨z, hzoC⟩)⁻¹ := by
      have e1 : (⟨goodFamily Φ l * z⁻¹, hhC⟩ : C.integers) = ⟨goodFamily Φ l, hintC l⟩ * ⟨z⁻¹, hzinvC⟩ := Subtype.ext rfl
      rw [e1, map_mul, C.residue_inv' hzoC hzbar0 hzinvC]
    have hhres0 : C.residue ⟨_, hhC⟩ ≠ 0 := by rw [hhres]; exact mul_ne_zero htres0 (inv_ne_zero hzbar0)
    have hhord : xe.ord (C.residue ⟨_, hhC⟩) = a - 1 := by
      rw [hhres, xe.ord_mul htres0 (inv_ne_zero hzbar0), Place.ord_inv, hzoord, ← ha_def]; ring

    obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
    set n : ℕ := hasseExp Φ.toFamData l with hn_def
    have hn1 : 1 ≤ n := one_le_hasseExp p A hA Γ Φ l hl
    set c' : (AlgebraicClosure ℚ) := (p : (AlgebraicClosure ℚ)) ^ (n - 1) with hc'
    have hc'0 : c' ≠ 0 := pow_ne_zero _ hp0
    have hc'A : c' ∈ A := pow_mem (natCast_mem A p) _
    have hπ : (((Δ.annIn e).modulus : ↥A) : (AlgebraicClosure ℚ)) = (p : (AlgebraicClosure ℚ)) := by
      show (((Δ.An e).modulus : ↥A) : (AlgebraicClosure ℚ)) = _
      rw [Δ.modulus_eq e, hwe, pow_one]; norm_cast
    have hzz : z * zi = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : (AlgebraicClosure ℚ)) := by rw [← hπ]; exact htwo
    have hzi_eq : zi = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : (AlgebraicClosure ℚ)) * z⁻¹ := by
      rw [← hzz]; field_simp
    have hαp : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : (AlgebraicClosure ℚ)) ≠ 0 := (map_ne_zero _).2 hp0
    have hident : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * (goodFamily Φ l * z⁻¹) = goodFamilyZero Φ.toFamData l * zi := by
      have et : goodFamilyZero Φ.toFamData l
          = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : (AlgebraicClosure ℚ)) ^ n))⁻¹ * goodFamily Φ l := rfl
      rw [et, hzi_eq, hc', map_pow, map_pow]
      have hpn : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : (AlgebraicClosure ℚ))) ^ n = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : (AlgebraicClosure ℚ))) ^ (n - 1) * algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (p : (AlgebraicClosure ℚ)) := by
        rw [← pow_succ, Nat.sub_add_cancel hn1]
      rw [hpn]
      field_simp
    have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * (goodFamily Φ l * z⁻¹) ∈ C'.integers := by
      rw [hident]; exact mul_mem (hintZ l) hziC
    have hres' : C'.residue ⟨_, hC'⟩ ≠ 0 := by
      have e1 : (⟨_, hC'⟩ : C'.integers) = ⟨goodFamilyZero Φ.toFamData l, hintZ l⟩ * ⟨zi, hziC⟩ := Subtype.ext hident
      rw [e1, map_mul]; exact mul_ne_zero (hresZ l) hzires0

    have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (goodFamily Φ l * z⁻¹) := by
      intro Q hQ
      obtain ⟨-, hzQ, -, hzQ0, -⟩ := (Δ.annOut e).mem_dom Q hQ
      have hQ' : Q ∈ (Δ.annIn e).dom := by rw [← hdom]; exact hQ
      have ht : 0 ≤ Q.ord (goodFamily Φ l) := Place.ord_nonneg_of_mem' Q (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e Q hQ' l hl).1
      rw [Q.ord_mul (Φ.t_basis.1.ne_zero l) (inv_ne_zero hz0), Place.ord_inv, Place.ord_eq_zero_of_evalAt_ne_zero' Q hzQ hzQ0]
      simpa using ht
    have hwide := annOut_wide' p A hA Γ Δ e μ hμA
    have hmod0' : ((Δ.annOut e).modulus : (AlgebraicClosure ℚ)) ≠ 0 := by rw [hmod]; exact hmod0
    have htwo' : (Δ.annIn e).param * (Δ.annOut e).param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((Δ.annOut e).modulus : (AlgebraicClosure ℚ)) := by
      rw [mul_comm (Δ.annIn e).param, hmod]; exact htwo
    obtain ⟨hsum, hb, -⟩ := AlgebraicCurve.Annulus.ord_residue_add_nonneg_and_abv_le_one_of_isAttached_both_ends μ hμA
      (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo' C xe hattOut' C' (nodeSrc Γ e) hattIn hwide
      (goodFamily Φ l * z⁻¹) hhC hhres0 c' hc'0 hc'A hC' hres' hpole
    obtain ⟨D, hD0, hDdom, hDord, hDsum, hDlog⟩ := AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
      (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo' C xe hattOut' C' (nodeSrc Γ e) hattIn hwide
      (goodFamily Φ l * z⁻¹) hhC hhres0 c' hc'0 hc'A hC' hres' hpole
    rw [hhord] at hsum hb hDsum
    obtain ⟨hle1, hstrict⟩ := hb R hR'

    have hμp1 : μ (p : (AlgebraicClosure ℚ)) < 1 := by
      have hm : (⟨(p : (AlgebraicClosure ℚ)), natCast_mem A p⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
        have := (Δ.annIn e).modulus_mem
        have e1 : ((Δ.annIn e).modulus : ↥A) = ⟨(p : (AlgebraicClosure ℚ)), natCast_mem A p⟩ := Subtype.ext hπ
        rw [e1] at this; exact this
      exact abv_lt_one_of_mem_maximalIdeal_vs μ hμA (natCast_mem A p) hm
    have hlt : μ (R.evalAt (goodFamily Φ l * z⁻¹)) < 1 := by
      apply hstrict
      by_cases hn2 : 2 ≤ n
      · left
        rw [hc', map_pow]
        exact pow_lt_one₀ (μ.nonneg _) hμp1 (by omega)
      · right
        have hn : n = 1 := by omega
        by_contra hle
        push_neg at hle
        have hzero : a - 1 + (nodeSrc Γ e).ord (C'.residue ⟨_, hC'⟩) = 0 := le_antisymm hle hsum

        have hc'1 : c' = 1 := by rw [hc', hn]; rfl
        have hDz : ∀ Q, D Q = 0 := by
          intro Q
          by_contra hne
          have hpos : 0 < D Q := lt_of_le_of_ne (hD0 Q) (Ne.symm hne)
          have hsumZ : (D.sum fun _ m => m : ℤ) = ∑ Q ∈ D.support, D Q := rfl
          have : 0 < (D.sum fun _ m => m : ℤ) := by
            rw [hsumZ]
            exact Finset.sum_pos' (fun Q _ => hD0 Q) ⟨Q, Finsupp.mem_support_iff.2 hne, hpos⟩
          omega
        have hl0 : (D.sum fun Q m => (m : ℝ) * Real.log (μ (Q.evalAt (Δ.annOut e).param))) = 0 := by
          rw [Finsupp.sum]; exact Finset.sum_eq_zero fun Q _ => by rw [hDz Q]; simp
        have hlogc : Real.log (μ c') = 0 := by rw [hc'1, map_one, Real.log_one]
        rw [hl0, hlogc, zero_add] at hDlog
        have hlogπ : Real.log (μ ((Δ.annOut e).modulus : (AlgebraicClosure ℚ))) ≠ 0 := by
          rw [hmod]; show Real.log (μ (((Δ.annIn e).modulus : ↥A) : (AlgebraicClosure ℚ))) ≠ 0
          rw [hπ]; exact (Real.log_neg (μ.pos hp0) hμp1).ne
        have ha'' : (nodeSrc Γ e).ord (C'.residue ⟨_, hC'⟩) = 0 := by
          rcases mul_eq_zero.1 hDlog.symm with h | h
          · exact_mod_cast h
          · exact absurd h hlogπ
        omega
    rw [hXval] at hle1 hlt
    have hX : R.evalAt (goodFamily Φ l) * (R.evalAt z)⁻¹ ∈ A := (hμA _).2 hle1
    have hXmax : (⟨_, hX⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; intro hu
      exact absurd (abv_eq_one_of_isUnit_vs μ hμA hX hu) (ne_of_lt hlt)
    have hXres : IsLocalRing.residue A ⟨_, hX⟩ = κ * (P l).eval (ssValue Γ e) := by
      rw [(IsLocalRing.residue_eq_zero_iff _).2 hXmax, hPl, mul_zero]
    exact ⟨hX, hXres, fun hne => absurd hPl hne⟩

private theorem exists_index_of_functional_ne {k : Type*} [Field k] {r m : ℕ} (P : Fin r → Polynomial k)
    (hspan : Submodule.span k (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) = Polynomial.degreeLT k m)
    (L : Polynomial k →ₗ[k] k) (q : Polynomial k) (hq : q ∈ Polynomial.degreeLT k m) (hLq : L q ≠ 0) :
    ∃ l : Fin r, 1 ≤ (l : ℕ) ∧ L (P l) ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hLq
  have hle : Submodule.span k (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨l, hl⟩, rfl⟩
    exact hall l hl
  rw [hspan] at hle
  exact hle hq

end TubeSepTangent

end ModularCurve.MultCovering

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.AlgebraicCurve IsLocalRing ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one.ModularCurve.MultCovering"

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s)
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e')
    (hwe : jWidth (ssValue Γ e) = 1) (hwe' : jWidth (ssValue Γ e') = 1) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ R ∈ (Δ.annIn e).dom, ∀ R' ∈ (Δ.annIn e').dom,
        (∃ i' j', evalVec s R i' * evalVec s R' j' ≠ evalVec s R j' * evalVec s R' i') →
        |prox μ (evalVec s R) (evalVec s R')| ≤ compConst Φ s hs * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  classical
  intro μ hμ hμA R hR R' hR' hnonprop
  have hp : p.Prime := Fact.out
  have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : (AlgebraicClosure ℚ)) ∈ A := natCast_mem A p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)

  have hr : r = mAnnuli p + 1 := eq_mAnnuli_add_one_of_isEmbBasis p hp5 s hs
  have hm2 : 2 ≤ mAnnuli p := by
    by_contra hlt; push_neg at hlt
    apply hne; apply Fin.ext; have := e.isLt; have := e'.isLt; omega
  have hr0 : 0 < r := by omega
  set o : Fin r := ⟨0, hr0⟩ with ho

  obtain ⟨hint, h0res, P, hP, -, hPspan⟩ := infChart_residue_goodFamily p A hA Γ Φ

  obtain ⟨hRrat, hρ0, hπρ, hzR0, hsmallR, κ, hκ0, hrowsR⟩ :=
    tube_rows_W1 p A hA Γ Δ Φ e hwe μ hμ hμA R hR hint P hP
  obtain ⟨hR'rat, hρ'0, hπρ', hzR'0, hsmallR', κ', hκ'0, hrowsR'⟩ :=
    tube_rows_W1 p A hA Γ Δ Φ e' hwe' μ hμ hμA R' hR' hint P hP
  set t := goodFamily Φ with ht
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have ht0 : ∀ i, t i ≠ 0 := goodFamily_ne_zero' Φ
  have hto : t o = 1 := goodFamily_zero_eq_one p Φ o rfl
  set zR : (AlgebraicClosure ℚ) := R.evalAt (Δ.annOut e).param with hzR_def
  set zR' : (AlgebraicClosure ℚ) := R'.evalAt (Δ.annOut e').param with hzR'_def
  have htR : ∀ i, t i ∈ R.toValuationSubring := by
    intro i
    by_cases hi : 1 ≤ (i : ℕ)
    · exact (hsmallR i hi).1
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [this, hto]; exact one_mem _
  have htR' : ∀ i, t i ∈ R'.toValuationSubring := by
    intro i
    by_cases hi : 1 ≤ (i : ℕ)
    · exact (hsmallR' i hi).1
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [this, hto]; exact one_mem _
  set x : Fin r → (AlgebraicClosure ℚ) := fun i => R.evalAt (t i * (t o)⁻¹) with hx
  set y : Fin r → (AlgebraicClosure ℚ) := fun i => R'.evalAt (t i * (t o)⁻¹) with hy
  have hxeval : ∀ i, x i = R.evalAt (t i) := fun i => by simp [hx, hto]
  have hyeval : ∀ i, y i = R'.evalAt (t i) := fun i => by simp [hy, hto]
  have hxo : x o = 1 := by rw [hxeval, hto, Place.evalAt_one]
  have hyo : y o = 1 := by rw [hyeval, hto, Place.evalAt_one]
  have hxle : ∀ i, μ (x i) ≤ 1 := by
    intro i; rw [hxeval]
    by_cases hi : 1 ≤ (i : ℕ)
    · exact (hsmallR i hi).2.le
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [this, hto, Place.evalAt_one, map_one]
  have hyle : ∀ i, μ (y i) ≤ 1 := by
    intro i; rw [hyeval]
    by_cases hi : 1 ≤ (i : ℕ)
    · exact (hsmallR' i hi).2.le
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [this, hto, Place.evalAt_one, map_one]
  have hunitabv : ∀ {a : (AlgebraicClosure ℚ)} (ha : a ∈ A), IsUnit (⟨a, ha⟩ : A) → μ a = 1 := fun ha hu => abv_eq_one_of_isUnit_vs μ hμA ha hu

  have hxfac : ∀ l, x l = (R.evalAt (t l) * zR⁻¹) * zR := fun l => by rw [hxeval, inv_mul_cancel_right₀ hzR0]
  have hyfac : ∀ l, y l = (R'.evalAt (t l) * zR'⁻¹) * zR' := fun l => by rw [hyeval, inv_mul_cancel_right₀ hzR'0]

  have hC1 : (Polynomial.C 1 : Polynomial (IsLocalRing.ResidueField ↥A)) ∈ Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := by
    rw [Polynomial.mem_degreeLT, Polynomial.degree_C one_ne_zero]; exact_mod_cast (show 0 < mAnnuli p by omega)
  have hcore : ∃ l : Fin r, μ ((p : (AlgebraicClosure ℚ))) ^ modulusExp < μ (x l - y l) := by
    rcases lt_trichotomy (μ zR) (μ zR') with hlt | heq | hgt
    ·
      obtain ⟨l, hl1, hLl⟩ := exists_index_of_functional_ne P hPspan (Polynomial.leval (ssValue Γ e')) _ hC1
        (by rw [Polynomial.leval_apply, Polynomial.eval_C]; exact one_ne_zero)
      rw [Polynomial.leval_apply] at hLl
      obtain ⟨hX, -, -⟩ := hrowsR l hl1
      obtain ⟨hY, -, hYu⟩ := hrowsR' l hl1
      refine ⟨l, ?_⟩
      have hμy : μ (y l) = μ zR' := by rw [hyfac, map_mul, hunitabv hY (hYu hLl), one_mul]
      have hμx : μ (x l) ≤ μ zR := by
        rw [hxfac, map_mul]
        calc μ (R.evalAt (t l) * zR⁻¹) * μ zR ≤ 1 * μ zR := mul_le_mul_of_nonneg_right ((hμA _).1 hX) (μ.nonneg _)
          _ = μ zR := one_mul _
      have : μ (x l - y l) = μ zR' := by
        rw [← μ.map_neg, neg_sub, abv_sub_eq_of_abv_lt μ hμ (by rw [hμy]; exact lt_of_le_of_lt hμx hlt), hμy]
      rw [this]; exact hπρ'
    ·
      have hμlam : μ (zR' * zR⁻¹) = 1 := by rw [map_mul, map_inv₀, ← heq, mul_inv_cancel₀ hρ0.ne']
      have hlamA : zR' * zR⁻¹ ∈ A := (hμA _).2 hμlam.le
      have hlamU : IsUnit (⟨_, hlamA⟩ : A) := by
        by_contra hnu
        have hmax : (⟨_, hlamA⟩ : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
        have := abv_lt_one_of_mem_maximalIdeal_vs μ hμA hlamA hmax
        linarith
      set lam : (IsLocalRing.ResidueField ↥A) := IsLocalRing.residue A ⟨_, hlamA⟩ with hlam_def
      have hlam0 : lam ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hlamU
      have hzR'eq : zR' = zR' * zR⁻¹ * zR := by rw [inv_mul_cancel_right₀ hzR0]

      set L : Polynomial (IsLocalRing.ResidueField ↥A) →ₗ[(IsLocalRing.ResidueField ↥A)] (IsLocalRing.ResidueField ↥A) :=
        κ • Polynomial.leval (ssValue Γ e) - (lam * κ') • Polynomial.leval (ssValue Γ e') with hL
      have hLapply : ∀ q : Polynomial (IsLocalRing.ResidueField ↥A), L q = κ * q.eval (ssValue Γ e) - lam * κ' * q.eval (ssValue Γ e') := by
        intro q; simp only [hL, LinearMap.sub_apply, LinearMap.smul_apply, Polynomial.leval_apply, smul_eq_mul]
      have hq : (Polynomial.X - Polynomial.C (ssValue Γ e') : Polynomial (IsLocalRing.ResidueField ↥A)) ∈ Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := by
        rw [Polynomial.mem_degreeLT, Polynomial.degree_X_sub_C]; exact_mod_cast hm2
      have hLq : L (Polynomial.X - Polynomial.C (ssValue Γ e')) ≠ 0 := by
        rw [hLapply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C, sub_self, mul_zero, sub_zero]
        exact mul_ne_zero hκ0 (sub_ne_zero.2 fun h => hne (ssValue_injective Γ h))
      obtain ⟨l, hl1, hLl⟩ := exists_index_of_functional_ne P hPspan L _ hq hLq
      rw [hLapply] at hLl
      obtain ⟨hX, hXres, -⟩ := hrowsR l hl1
      obtain ⟨hY, hYres, -⟩ := hrowsR' l hl1
      set d : A := ⟨_, hX⟩ - ⟨_, hlamA⟩ * ⟨_, hY⟩ with hd
      have hdval : x l - y l = zR * (d : (AlgebraicClosure ℚ)) := by
        rw [hxeval, hyeval, hd]; push_cast; field_simp
      have hdres : IsLocalRing.residue A d = κ * (P l).eval (ssValue Γ e) - lam * κ' * (P l).eval (ssValue Γ e') := by
        rw [hd, map_sub, map_mul, hXres, hYres, ← hlam_def]; ring
      refine ⟨l, ?_⟩
      have hu : IsUnit d := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 (by rw [hdres]; exact hLl)
      have : μ (d : (AlgebraicClosure ℚ)) = 1 := abv_eq_one_of_isUnit_vs μ hμA d.2 (by simpa using hu)
      rw [hdval, map_mul, this, mul_one]; exact hπρ
    ·
      obtain ⟨l, hl1, hLl⟩ := exists_index_of_functional_ne P hPspan (Polynomial.leval (ssValue Γ e)) _ hC1
        (by rw [Polynomial.leval_apply, Polynomial.eval_C]; exact one_ne_zero)
      rw [Polynomial.leval_apply] at hLl
      obtain ⟨hX, -, hXu⟩ := hrowsR l hl1
      obtain ⟨hY, -, -⟩ := hrowsR' l hl1
      refine ⟨l, ?_⟩
      have hμx : μ (x l) = μ zR := by rw [hxfac, map_mul, hunitabv hX (hXu hLl), one_mul]
      have hμy : μ (y l) ≤ μ zR' := by
        rw [hyfac, map_mul]
        calc μ (R'.evalAt (t l) * zR'⁻¹) * μ zR' ≤ 1 * μ zR' := mul_le_mul_of_nonneg_right ((hμA _).1 hY) (μ.nonneg _)
          _ = μ zR' := one_mul _
      have : μ (x l - y l) = μ zR := by
        rw [abv_sub_eq_of_abv_lt μ hμ (by rw [hμx]; exact lt_of_le_of_lt hμy hgt), hμx]
      rw [this]; exact hπρ

  obtain ⟨lc, hlc⟩ := hcore
  set M := linkMatrix Φ s hs with hM
  set Minv := linkMatrixInv Φ s hs with hMinv
  set B := linkBudget Φ s hs with hB
  obtain ⟨dP, hdP0, hdP⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr0 s t hs0 ht0 M Minv
    (linkMatrixInv_mul Φ s hs) (linkMatrix_mul_inv Φ s hs) (eq_sum_linkMatrix_smul_goodFamily Φ s hs)
    R hRrat o (fun j => by rw [hto, inv_one, mul_one]; exact htR j)
  obtain ⟨dQ, hdQ0, hdQ⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr0 s t hs0 ht0 M Minv
    (linkMatrixInv_mul Φ s hs) (linkMatrix_mul_inv Φ s hs) (eq_sum_linkMatrix_smul_goodFamily Φ s hs)
    R' hR'rat o (fun j => by rw [hto, inv_one, mul_one]; exact htR' j)
  obtain ⟨i', j', hij⟩ := hnonprop
  have hminor : ∀ i j, evalVec s R i * evalVec s R' j - evalVec s R j * evalVec s R' i
      = dP * dQ * (M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i) := by
    intro i j; rw [hdP, hdQ]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hMm : M.mulVec x i' * M.mulVec y j' - M.mulVec x j' * M.mulVec y i' ≠ 0 := by
    intro h0; apply hij; exact sub_eq_zero.1 (by rw [hminor, h0, mul_zero])
  have hsupM : (⨆ q : Fin r × Fin r, μ (M.mulVec x q.1 * M.mulVec y q.2 - M.mulVec x q.2 * M.mulVec y q.1)) ≠ 0 :=
    ((μ.pos hMm).trans_le (le_ciSup (Finite.bddAbove_range
      (fun q : Fin r × Fin r => μ (M.mulVec x q.1 * M.mulVec y q.2 - M.mulVec x q.2 * M.mulVec y q.1))) (i', j'))).ne'
  have hrowminor : ∃ i j, x i * y j - x j * y i ≠ 0 := by
    by_contra hall; push_neg at hall; apply hMm
    rw [minor_mulVec_D]; exact Finset.sum_eq_zero fun q _ => by rw [hall q.1 q.2, mul_zero]
  obtain ⟨i1, j1, hm1⟩ := hrowminor
  have hx0 : x ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hxo] at this; exact one_ne_zero this
  have hy0 : y ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hyo] at this; exact one_ne_zero this
  set β : ℝ := (μ (p : (AlgebraicClosure ℚ)))⁻¹ ^ B with hβ
  have hμp0 : 0 < μ (p : (AlgebraicClosure ℚ)) := μ.pos hp0
  have hμp1 : μ (p : (AlgebraicClosure ℚ)) ≤ 1 := (hμA _).1 hpA
  have hβ1 : 1 ≤ β := one_le_pow₀ ((one_le_inv₀ hμp0).2 hμp1)
  have hlogβ : Real.log β = (B : ℝ) * (-Real.log (μ (p : (AlgebraicClosure ℚ)))) := by
    rw [hβ, Real.log_pow, Real.log_inv]
  have hentry : ∀ m : (AlgebraicClosure ℚ), (p : (AlgebraicClosure ℚ)) ^ B * m ∈ A → μ m ≤ β := by
    intro m hm
    have h1 : μ ((p : (AlgebraicClosure ℚ)) ^ B * m) ≤ 1 := (hμA _).1 hm
    rw [map_mul, map_pow] at h1
    have hpB : 0 < μ (p : (AlgebraicClosure ℚ)) ^ B := pow_pos hμp0 _
    rw [hβ, inv_pow]
    calc μ m = (μ (p : (AlgebraicClosure ℚ)) ^ B * μ m) * (μ (p : (AlgebraicClosure ℚ)) ^ B)⁻¹ := by field_simp
      _ ≤ 1 * (μ (p : (AlgebraicClosure ℚ)) ^ B)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hpB.le)
      _ = (μ (p : (AlgebraicClosure ℚ)) ^ B)⁻¹ := one_mul _
  have hMβ : ∀ i j, μ (M i j) ≤ β := fun i j => hentry _ (linkBudget_spec Φ s hs A hA i j).1
  have hMβ' : ∀ i j, μ (Minv i j) ≤ β := fun i j => hentry _ (linkBudget_spec Φ s hs A hA i j).2
  have hprox1 : prox μ (evalVec s R) (evalVec s R') = prox μ (M.mulVec x) (M.mulVec y) := by
    rw [hdP, hdQ]; exact AlgebraicCurve.prox_smul_smul μ _ _ hdP0 hdQ0 hsupM
  have hL := AlgebraicCurve.abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le μ hμ M Minv (linkMatrixInv_mul Φ s hs)
    β hβ1 hMβ hMβ' x y hx0 hy0 ⟨i1, j1, hm1⟩
  rw [hlogβ, ← hprox1] at hL
  have hpxy := AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart μ hμ x y o hxo hyo hxle hyle
  set S : ℝ := ⨆ i, μ (x i - y i) with hS
  have hSbdd := Finite.bddAbove_range (fun i : Fin r => μ (x i - y i))
  have hSge : μ (x lc - y lc) ≤ S := le_ciSup hSbdd lc
  have hSpos : 0 < S := lt_of_lt_of_le (lt_trans (pow_pos hμp0 _) hlc) hSge
  have hSle : S ≤ 1 := by
    haveI : Nonempty (Fin r) := ⟨o⟩
    refine ciSup_le fun i => ?_
    exact (abv_sub_le_max μ hμA _ _).trans (max_le (hxle i) (hyle i))
  have hpxy0 : 0 ≤ prox μ x y := by
    rw [hpxy]; exact neg_nonneg.2 (Real.log_nonpos hSpos.le hSle)
  have hpxy3 : prox μ x y ≤ (modulusExp : ℝ) * (-Real.log (μ (p : (AlgebraicClosure ℚ)))) := by
    rw [hpxy]
    have h1 : μ ((p : (AlgebraicClosure ℚ))) ^ modulusExp < S := lt_of_lt_of_le hlc hSge
    have h2 := Real.log_lt_log (pow_pos hμp0 _) h1
    rw [Real.log_pow] at h2
    show -Real.log S ≤ _
    linarith
  have hlam : 0 ≤ -Real.log (μ (p : (AlgebraicClosure ℚ))) := by linarith [Real.log_nonpos hμp0.le hμp1]
  calc |prox μ (evalVec s R) (evalVec s R')|
      = |(prox μ (evalVec s R) (evalVec s R') - prox μ x y) + prox μ x y| := by ring_nf
    _ ≤ |prox μ (evalVec s R) (evalVec s R') - prox μ x y| + |prox μ x y| := abs_add_le _ _
    _ ≤ 4 * ((B : ℝ) * -Real.log (μ (p : (AlgebraicClosure ℚ)))) + (modulusExp : ℝ) * (-Real.log (μ (p : (AlgebraicClosure ℚ)))) := by
        refine add_le_add hL ?_
        rw [abs_of_nonneg hpxy0]; exact hpxy3
    _ ≤ compConst Φ s hs * (-Real.log (μ (p : (AlgebraicClosure ℚ)))) := by
        rw [compConst_eq, hB]
        have hme : (0 : ℝ) ≤ modulusExp := by positivity
        nlinarith

end S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one
end P2MW
export P2MW.S_ModularCurve_MultCovering_crossComparison_annIn_annIn_of_jWidth_eq_one (solution)
