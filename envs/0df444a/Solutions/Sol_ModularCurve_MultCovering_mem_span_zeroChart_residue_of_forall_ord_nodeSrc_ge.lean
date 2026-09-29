-- Prove2me | solution 1 for ModularCurve.MultCovering.mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b8ec519e-d519-53ca-a02f-448c9fede390

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Theorems.Thm_AlgebraicCurve_Annulus_abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends
import Theorems.Thm_ModularCurve_MultCovering_cuspZeroBar_not_mem_infChart_dom
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_ComponentChart_ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends
import Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
import Theorems.Thm_ModularCurve_MultCovering_infChart_nodeData_exists_node_of_member
import Theorems.Thm_ModularCurve_MultCovering_infChart_goodFamily_residue_ne_zero
import Theorems.Thm_ModularCurve_coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat
import Theorems.Thm_ModularCurve_exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_ModularCurve_ComponentChart_residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar
import Theorems.Thm_ModularCurve_exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_mem_integers_residue_ne_zero_of_qCoeff
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ModularCurve_ComponentChart_exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Theorems.Thm_ValuationSubring_valuation_ratCast_eq_one_iff_padicValRat_eq_zero
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldC_one
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord
import Theorems.Thm_ModularCurve_MultCovering_eq_mAnnuli_add_one_of_isEmbBasis
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
import Theorems.Thm_ModularCurve_MultCovering_mem_zeroChart_nodes_iff
import Theorems.Thm_ModularCurve_ofNat1728_mem_ssJSet_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.cuspCount_one WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 3200000

namespace P2MF2J

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge.ModularCurve Polynomial IsLocalRing"

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem ne_zero_of_ord_ne_zero (v : Place K F) {g : F} (h : v.ord g ≠ 0) : g ≠ 0 := by
  rintro rfl
  exact h (Place.ord_zero v)

theorem not_isUnit_of_ord_pos (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring)
    (h : 0 < v.ord g) : ¬ IsUnit (⟨g, hg⟩ : v.toValuationSubring) := by
  rintro ⟨u, hu⟩
  have h0 := v.ord_coe_unit u
  rw [hu] at h0
  change v.ord g = 0 at h0
  omega

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring)
    (h : 0 < v.ord g) : (⟨g, hg⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring :=
  (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (not_isUnit_of_ord_pos v hg h))

theorem mem_of_ord_pos (v : Place K F) {g : F} (h : 0 < v.ord g) : g ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_ord_nonneg_alt (ne_zero_of_ord_ne_zero v h.ne') h.le

theorem ord_algebraMap' (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 :=
  (Place.hasValue_algebraMap v c).ord_eq_zero hc

theorem HasValue.add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_of_ord_sub_algebraMap_pos (v : Place K F) {g : F} {a : K}
    (h : 0 < v.ord (g - algebraMap K F a)) : v.HasValue g a := by
  have hm := mem_of_ord_pos v h
  have hI := mem_maximalIdeal_of_ord_pos v hm h
  have hgmem : g ∈ v.toValuationSubring := by
    have := add_mem hm (v.algebraMap_mem' a)
    rwa [sub_add_cancel] at this
  refine ⟨hgmem, ?_⟩
  have hsplit : (⟨g, hgmem⟩ : v.toValuationSubring)
      = ⟨g - algebraMap K F a, hm⟩ + ⟨algebraMap K F a, v.algebraMap_mem' a⟩ := by
    apply Subtype.ext
    show g = (g - algebraMap K F a) + algebraMap K F a
    rw [sub_add_cancel]
  rw [hsplit, map_add, (residue_eq_zero_iff _).mpr hI, zero_add]
  exact (Place.hasValue_algebraMap v a).residue_eq

theorem evalAt_eq_of_hasValue {v : Place K F} (hv : v.IsRational) {g : F} {a : K} (h : v.HasValue g a) :
    v.evalAt g = a := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv h.mem]
  exact h.residue_eq

end PlaceFacts

section JLine

variable (k : Type*) [Field k] [DecidableEq k]

noncomputable abbrev jB : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩

theorem ratFuncEquiv_algebraMap (Q : k[X]) :
    (ratFuncEquivCharLOneC k).toRingEquiv (algebraMap k[X] (RatFunc k) Q) = aeval (jB k) Q := by
  apply Subtype.ext
  change ((IntermediateField.equivOfEq (modularFunctionFieldC_one k).symm
      (RatFunc.algEquivOfTranscendental (jqModC k) _
        (algebraMap (Polynomial k) (RatFunc k) Q)) :
          ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = _
  have hcoe : ∀ (h : IntermediateField.adjoin k {jqModC k} = modularFunctionFieldC k 1)
      (x : ↥(IntermediateField.adjoin k {jqModC k})),
      ((IntermediateField.equivOfEq h x : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
        = (x : LaurentSeries k) := fun _ _ => rfl
  rw [hcoe, RatFunc.algEquivOfTranscendental_algebraMap]
  have e1 : (((aeval (IntermediateField.AdjoinSimple.gen k (jqModC k)) Q :
      ↥(IntermediateField.adjoin k {jqModC k})) : LaurentSeries k)) = aeval (jqModC k) Q := by
    rw [show (((aeval (IntermediateField.AdjoinSimple.gen k (jqModC k)) Q :
        ↥(IntermediateField.adjoin k {jqModC k})) : LaurentSeries k))
        = (IntermediateField.val _) (aeval (IntermediateField.AdjoinSimple.gen k (jqModC k)) Q) from rfl,
      ← Polynomial.aeval_algHom_apply]
    rfl
  have e2 : (((aeval (jB k) Q : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)) = aeval (jqModC k) Q := by
    rw [show (((aeval (jB k) Q : ↥(modularFunctionFieldC k 1)) : LaurentSeries k))
        = (IntermediateField.val _) (aeval (jB k) Q) from rfl, ← Polynomial.aeval_algHom_apply]
    rfl
  exact e1.trans e2.symm

theorem ord_charLGeomPlaceOfPoint_aeval (a : k) (Q : k[X]) (hQ : Q ≠ 0) :
    (charLGeomPlaceOfPoint k a).ord (aeval (jB k) Q) = Q.rootMultiplicity a := by
  have hplace : charLGeomPlaceOfPoint k a
      = Place.congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
          (fun x => (ratFuncEquivCharLOneC k).commutes x) (RationalFunctionField.placeOfPoint k a) := rfl
  rw [hplace, ← ratFuncEquiv_algebraMap, Place.ord_congrRingEquiv,
    RationalFunctionField.ord_placeOfPoint_algebraMap a hQ]

theorem aeval_jB_ne_zero (Q : k[X]) (hQ : Q ≠ 0) : aeval (jB k) Q ≠ 0 := by
  intro h
  apply hQ
  have h' : aeval (jqModC k) Q = 0 := by
    have := congrArg (IntermediateField.val (modularFunctionFieldC k 1)) h
    rw [← Polynomial.aeval_algHom_apply, map_zero] at this
    exact this
  exact (transcendental_iff.mp (transcendental_jqModC k)) Q h'

theorem hasValue_jB (a : k) : (charLGeomPlaceOfPoint k a).HasValue (jB k) a := by
  apply hasValue_of_ord_sub_algebraMap_pos
  have h := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a a
  rw [if_pos rfl] at h
  change (charLGeomPlaceOfPoint k a).ord (jB k - algebraMap k ↥(modularFunctionFieldC k 1) a) = 1 at h
  omega

theorem hasValue_aeval (a : k) (Q : k[X]) :
    (charLGeomPlaceOfPoint k a).HasValue (aeval (jB k) Q) (Q.eval a) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.aeval_add, eval_add]
    exact P2MF2J.HasValue.add hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial]
    refine Place.HasValue.mul (Place.hasValue_algebraMap _ c) ?_
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact Place.hasValue_one _
    | succ n ih => rw [pow_succ, pow_succ]; exact Place.HasValue.mul ih (hasValue_jB k a)

theorem hasValue_aeval_mul_inv (a : k) (Q R : k[X]) (hR : R.eval a ≠ 0) :
    (charLGeomPlaceOfPoint k a).HasValue (aeval (jB k) Q * (aeval (jB k) R)⁻¹) (Q.eval a * (R.eval a)⁻¹) :=
  Place.HasValue.mul (hasValue_aeval k a Q) ((hasValue_aeval k a R).inv hR)

theorem aeval_mul_inv_sub_algebraMap (a : k) (Q R : k[X]) (hR : R.eval a ≠ 0) :
    aeval (jB k) Q * (aeval (jB k) R)⁻¹ - algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a * (R.eval a)⁻¹)
      = aeval (jB k) (C (R.eval a) * Q - C (Q.eval a) * R)
          * (aeval (jB k) R * algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a))⁻¹ := by
  have hR' : aeval (jB k) R ≠ 0 := by
    intro h0
    have := (hasValue_aeval k a R).ne_zero hR
    exact this h0
  have hc : algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a) ≠ 0 := (_root_.map_ne_zero _).mpr hR
  have e1 : aeval (jB k) (C (R.eval a) * Q - C (Q.eval a) * R)
      = algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a) * aeval (jB k) Q
        - algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a) * aeval (jB k) R := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_C]
  have e2 : algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a * (R.eval a)⁻¹)
      = algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a)
        * (algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a))⁻¹ := by
    rw [_root_.map_mul, map_inv₀]
  rw [e1, e2]
  field_simp

theorem ord_aeval_mul_inv_sub_value (a : k) (Q R : k[X]) (hR : R.eval a ≠ 0)
    (hN : C (R.eval a) * Q - C (Q.eval a) * R ≠ 0) :
    (charLGeomPlaceOfPoint k a).ord
        (aeval (jB k) Q * (aeval (jB k) R)⁻¹
          - algebraMap k ↥(modularFunctionFieldC k 1) (Q.eval a * (R.eval a)⁻¹))
      = (C (R.eval a) * Q - C (Q.eval a) * R).rootMultiplicity a := by
  have hR0 : R ≠ 0 := by rintro rfl; exact hR (eval_zero)
  have hR' : aeval (jB k) R ≠ 0 := aeval_jB_ne_zero k R hR0
  have hc : algebraMap k ↥(modularFunctionFieldC k 1) (R.eval a) ≠ 0 := (_root_.map_ne_zero _).mpr hR
  have hN' : aeval (jB k) (C (R.eval a) * Q - C (Q.eval a) * R) ≠ 0 := aeval_jB_ne_zero k _ hN
  rw [aeval_mul_inv_sub_algebraMap k a Q R hR,
    (charLGeomPlaceOfPoint k a).ord_mul hN' (inv_ne_zero (mul_ne_zero hR' hc)),
    (charLGeomPlaceOfPoint k a).ord_inv, (charLGeomPlaceOfPoint k a).ord_mul hR' hc,
    ord_charLGeomPlaceOfPoint_aeval k a _ hN, ord_charLGeomPlaceOfPoint_aeval k a R hR0, ord_algebraMap' _ hR,
    Polynomial.rootMultiplicity_eq_zero (fun h : IsRoot R a => hR h)]
  simp

end JLine

end P2MF2J

set_option Elab.async false

p2m_open "AlgebraicCurve ModularCurve~jBar P2MW.S_ModularCurve_MultCovering_mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge.ModularCurve IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "embDegree embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff ssJSet PlaceSpecialization.LevelOneProlongationPair jqModC modularFunctionFieldC jqModC_mem modularFunctionFieldC_one PlaceSpecialization ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed_coeff CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar cuspZeroBar_def jWidth jWidth_of_ne jWidth_eq_ite jWidth_pos jWidth_eq_one_or hasPrincipalDivisors_modularFunctionFieldBar_unconditional coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem ssJSet_nonempty ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar ComponentChart.exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar CharPReduction.modularRedLocHom_eq_coeffRed ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap isRational_place_modularFunctionFieldC_one zero_mem_ssJSet_iff exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord ord_charLGeomPlaceEquiv_placeInfty_jqModC MultCovering.mem_zeroChart_nodes_iff ofNat1728_mem_ssJSet_iff"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "FamData zeroSeries coe_frickeInvolutionBar_t hasseContent hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily jBar mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue ssValue_mem_ssJSet ssValue_injective exists_ssValue_eq nodeSrc nodeTgt AnnCtx cuspZeroBar_not_mem_infChart_dom infChart_nodeData_exists_node_of_member infChart_goodFamily_residue_ne_zero eq_mAnnuli_add_one_of_isEmbBasis mem_zeroChart_nodes_iff"
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

def IsContent (Φ : FamData p r) (l : Fin r) (n : ℤ) : Prop :=
  (∀ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 → n ≤ padicValRat p ((zeroSeries Φ l).coeff k)) ∧
    (∃ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 ∧ padicValRat p ((zeroSeries Φ l).coeff k) = n)

theorem isContent_hasseContent (Φ : FamData p r) (l : Fin r) (hex : ∃ n : ℤ, IsContent Φ l n) :
    IsContent Φ l (hasseContent Φ l) := by
  have hex' : ∃ n : ℤ, (∀ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 → n ≤ padicValRat p ((zeroSeries Φ l).coeff k)) ∧
      (∃ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 ∧ padicValRat p ((zeroSeries Φ l).coeff k) = n) := hex
  rw [hasseContent, dif_pos hex']
  exact hex'.choose_spec

theorem IsContent.eq {Φ : FamData p r} {l : Fin r} {m n : ℤ} (hm : IsContent Φ l m) (hn : IsContent Φ l n) :
    m = n := by
  obtain ⟨k, hk, hkm⟩ := hm.2
  obtain ⟨k', hk', hkn⟩ := hn.2
  have h1 := hn.1 k hk
  have h2 := hm.1 k' hk'
  rw [hkm] at h1; rw [hkn] at h2
  exact le_antisymm h2 h1

theorem hasseContent_eq_of_isContent {Φ : FamData p r} {l : Fin r} {n : ℤ} (hn : IsContent Φ l n) :
    hasseContent Φ l = n :=
  (isContent_hasseContent Φ l ⟨n, hn⟩).eq hn

theorem zeroSeries_ne_zero (Φ : FamData p r) (l : Fin r) (ht0 : Φ.t l ≠ 0) : zeroSeries Φ l ≠ 0 := by
  intro h
  apply ht0
  have h1 : ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
      LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
    rw [coe_frickeInvolutionBar_t, h, map_zero]
  have h2 : frickeInvolutionBar (1 * p) (Φ.t l) = 0 := Subtype.ext h1
  exact (EmbeddingLike.map_eq_zero_iff (f := frickeInvolutionBar (1 * p))).mp h2

theorem exists_isContent (Φ : FamData p r) (l : Fin r) (ht0 : Φ.t l ≠ 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (c : AlgebraicClosure ℚ) (hc : c ≠ 0)
    (hcA : ∀ k : ℤ, c * ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A) :
    ∃ n : ℤ, IsContent Φ l n := by
  have hcA' : ∀ k : ℤ, c * (coeffEmb (AlgebraicClosure ℚ) (zeroSeries Φ l)).coeff k ∈ A := by
    intro k; rw [← coe_frickeInvolutionBar_t]; exact hcA k
  obtain ⟨n, h1, k₀, hk₀, hk₀n⟩ := exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem
    (Fact.out : p.Prime) A hA (zeroSeries Φ l) (zeroSeries_ne_zero Φ l ht0) c hc hcA'
  exact ⟨n, h1, k₀, hk₀, hk₀n⟩

theorem zeroSeries_rescaled_gaussUnit (Φ : FamData p r) (l : Fin r) {n : ℤ} (hn : IsContent Φ l n)
    {K : Type*} [Field K] [CharZero K] (A : ValuationSubring K) (hA : A.LiesOverPrime p) :
    (∀ k : ℤ, (coeffEmb K (((p : ℚ) ^ n)⁻¹ • zeroSeries Φ l)).coeff k ∈ A) ∧
      ∃ k : ℤ, (coeffEmb K (((p : ℚ) ^ n)⁻¹ • zeroSeries Φ l)).coeff k ∉ A.nonunits := by
  obtain ⟨k₀, hk₀, hk₀n⟩ := hn.2
  obtain ⟨h1, h2⟩ := coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat A (Fact.out : p.Prime)
    hA (zeroSeries Φ l) n hn.1 k₀ hk₀ hk₀n
  exact ⟨h1, k₀, h2⟩

theorem hasseExp_cast (Φ : FamData p r) (l : Fin r) (h0 : 0 ≤ hasseContent Φ l) :
    (hasseExp Φ l : ℤ) = hasseContent Φ l := by
  rw [hasseExp, Int.toNat_of_nonneg h0]

theorem coe_frickeInvolutionBar_goodFamilyZero (Φ : FamData p r) (l : Fin r) :
    ((frickeInvolutionBar (1 * p) (goodFamilyZero Φ l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l) := by
  rw [goodFamilyZero, map_mul, map_inv₀, AlgEquiv.commutes]

  have hcoe : (((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l))⁻¹ * frickeInvolutionBar (1 * p) (Φ.t l) :
          modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ))
      = (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l))⁻¹ *
        ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
          LaurentSeries (AlgebraicClosure ℚ)) := by
    push_cast
    rfl
  rw [hcoe, coe_frickeInvolutionBar_t]
  ext k
  rw [coeffEmb_coeff, ← map_inv₀, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul,
    HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul]
  show ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l)⁻¹ * algebraMap ℚ (AlgebraicClosure ℚ) ((zeroSeries Φ l).coeff k)
    = algebraMap ℚ (AlgebraicClosure ℚ) ((((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l).coeff k)
  rw [show ((((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l).coeff k)
      = ((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ * (zeroSeries Φ l).coeff k from rfl,
    map_mul, map_inv₀, zpow_natCast, map_pow, map_natCast]

theorem frickeInvolutionBar_goodFamilyZero_qCoeff (Φ : FamData p r) (l : Fin r)
    (hex : ∃ n : ℤ, IsContent Φ l n) (h0 : 0 ≤ hasseContent Φ l)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ hf : ∀ k : ℤ, ((frickeInvolutionBar (1 * p) (goodFamilyZero Φ l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A,
      ∃ k : ℤ, IsUnit (⟨_, hf k⟩ : ↥A) := by
  have hn := isContent_hasseContent Φ l hex
  obtain ⟨h1, k₀, h2⟩ := zeroSeries_rescaled_gaussUnit Φ l hn A hA
  rw [← hasseExp_cast Φ l h0] at h1 h2
  refine ⟨fun k => ?_, k₀, ?_⟩
  · rw [coe_frickeInvolutionBar_goodFamilyZero]; exact h1 k
  · rw [ValuationSubring.valuation_eq_one_iff]
    have hx : ((frickeInvolutionBar (1 * p) (goodFamilyZero Φ l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)).coeff k₀
        = (coeffEmb (AlgebraicClosure ℚ) (((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l)).coeff k₀ := by
      rw [coe_frickeInvolutionBar_goodFamilyZero]
    have h3 : ¬ A.valuation ((coeffEmb (AlgebraicClosure ℚ)
        (((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l)).coeff k₀) < 1 :=
      fun h => h2 ((ValuationSubring.mem_nonunits_iff A).mpr h)
    refine le_antisymm (A.valuation_le_one _) ?_
    rw [not_lt, ← hx] at h3
    exact h3

section Sign

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  (C : ComponentChart A (modularFunctionFieldBar (1 * p)) ↥(modularFunctionFieldC (ResidueField ↥A) 1))
  (hint_iff : ∀ g : modularFunctionFieldBar (1 * p), g ∈ C.integers ↔
    (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
  (hres : ∀ (g : modularFunctionFieldBar (1 * p))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
    ∃ h : g ∈ C.integers,
      ((C.residue ⟨g, h⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) : LaurentSeries (ResidueField ↥A))
        = CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, hg⟩)
  (hnodes : ∀ x, x ∈ C.nodes ↔ ∃ a ∈ ssJSet p (ResidueField ↥A), charLGeomPlaceOfPoint (ResidueField ↥A) a = x)
  (hzero_not : cuspZeroBar (1 * p) ∉ C.dom)

  (hcrit : ∀ (g : modularFunctionFieldBar (1 * p))
    (hf : ∀ k : ℤ, (g : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A)
    (hu : ∃ k : ℤ, IsUnit (⟨(g : LaurentSeries (AlgebraicClosure ℚ)).coeff k, hf k⟩ : ↥A)),
      ∃ h : g ∈ C.integers, C.residue ⟨g, h⟩ ≠ 0)

theorem coe_frickeInvolutionBar_algebraMap_mul (Φ : FamData p r) (l : Fin r) (y : ℚ) :
    ((frickeInvolutionBar (1 * p)
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) y) * Φ.t l) :
          modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (y • zeroSeries Φ l) := by
  rw [map_mul, AlgEquiv.commutes]
  push_cast
  rw [coe_frickeInvolutionBar_t]
  ext k
  rw [coeffEmb_coeff]
  first
  | rw [IntermediateField.algebraMap_apply]
  | skip
  rw [algebraMap_laurentSeries_eq_single,
    HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul,
    show ((y • zeroSeries Φ l).coeff k) = y * (zeroSeries Φ l).coeff k from rfl, map_mul]

include hA hcrit in

theorem exists_frickeInvolutionBar_smul_mem_integers (Φ : FamData p r) (l : Fin r) {n : ℤ} (hn : IsContent Φ l n) :
    ∃ h : frickeInvolutionBar (1 * p)
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ n)⁻¹)) * Φ.t l) ∈ C.integers,
      C.residue ⟨_, h⟩ ≠ 0 := by
  obtain ⟨h1, k₀, h2⟩ := zeroSeries_rescaled_gaussUnit Φ l hn A hA
  have hf : ∀ k : ℤ, ((frickeInvolutionBar (1 * p)
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        (algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ n)⁻¹)) * Φ.t l) : modularFunctionFieldBar (1 * p)) :
          LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A := by
    intro k; rw [coe_frickeInvolutionBar_algebraMap_mul]; exact h1 k
  refine hcrit _ hf ⟨k₀, ?_⟩
  rw [ValuationSubring.valuation_eq_one_iff]
  refine le_antisymm (A.valuation_le_one _) ?_
  have h3 : ¬ A.valuation ((coeffEmb (AlgebraicClosure ℚ) (((p : ℚ) ^ n)⁻¹ • zeroSeries Φ l)).coeff k₀) < 1 :=
    fun h => h2 ((ValuationSubring.mem_nonunits_iff A).mpr h)
  rw [not_lt, ← coe_frickeInvolutionBar_algebraMap_mul] at h3
  exact h3

include hA hint_iff hres hnodes hzero_not hcrit in

theorem hasseContent_nonneg_of_chart (Φ : FamData p r) (l : Fin r) (hex : ∃ n : ℤ, IsContent Φ l n)
    (ht0 : Φ.t l ≠ 0) (ht_int : Φ.t l ∈ C.integers)
    (htpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (Φ.t l) < 0 → W = cuspInftyBar (1 * p)) :
    0 ≤ hasseContent Φ l := by
  by_contra hneg
  push_neg at hneg
  have hnI := isContent_hasseContent Φ l hex
  set n := hasseContent Φ l with hn

  set m : ℕ := (-n).toNat with hm_def
  have hm : (m : ℤ) = -n := Int.toNat_of_nonneg (by omega)
  have hm0 : m ≠ 0 := by intro h; rw [h] at hm; simp at hm; omega
  have hy : algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ n)⁻¹) = (p : AlgebraicClosure ℚ) ^ m := by
    rw [map_inv₀, map_zpow₀, map_natCast, ← zpow_neg, ← hm, zpow_natCast]
  have key := exists_frickeInvolutionBar_smul_mem_integers A hA C hcrit Φ l hnI
  rw [hy] at key
  obtain ⟨hwf_int, hwf_res⟩ := key

  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hxA : (p : AlgebraicClosure ℚ) ^ m ∈ A := pow_mem hpA m
  have hx_int : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ m) ∈ C.integers :=
    (C.algebraMap_mem_iff _).mpr hxA
  have hf_int : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ m) * Φ.t l ∈ C.integers :=
    mul_mem hx_int ht_int
  have hres_p : IsLocalRing.residue ↥A ⟨(p : AlgebraicClosure ℚ) ^ m, hxA⟩ = 0 := by
    have h1 : (⟨(p : AlgebraicClosure ℚ) ^ m, hxA⟩ : ↥A) = (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ^ m := by
      apply Subtype.ext; simp
    rw [h1, map_pow, (IsLocalRing.residue_eq_zero_iff _).mpr, zero_pow hm0]
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA
  have hresf : C.residue ⟨_, hf_int⟩ = 0 := by
    have h1 : (⟨_, hf_int⟩ : C.integers) = ⟨_, hx_int⟩ * ⟨Φ.t l, ht_int⟩ := rfl
    rw [h1, map_mul, C.residue_algebraMap ⟨_, hxA⟩, hres_p, map_zero, zero_mul]
  obtain ⟨a, ha⟩ := ssJSet_nonempty (q := p) (k := ResidueField ↥A)
  have hval : (charLGeomPlaceOfPoint (ResidueField ↥A) a).HasValue (C.residue ⟨_, hf_int⟩) 0 := by
    rw [hresf]; simpa using (charLGeomPlaceOfPoint (ResidueField ↥A) a).hasValue_algebraMap
      (F := ↥(modularFunctionFieldC (ResidueField ↥A) 1)) 0
  have hx0 : (p : AlgebraicClosure ℚ) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hf0 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ m) * Φ.t l ≠ 0 :=
    mul_ne_zero ((map_ne_zero _).mpr hx0) ht0
  have hfpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)),
      W.ord (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ m) * Φ.t l) < 0 →
        W = cuspInftyBar (1 * p) := by
    intro W hW
    apply htpole W
    rwa [W.ord_mul ((map_ne_zero _).mpr hx0) ht0, Place.ord_algebraMap, zero_add] at hW
  exact hwf_res (ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar A hA C hint_iff hres hnodes hzero_not _ hf0 hfpole hf_int hwf_int a ha hval)

include hA hint_iff hres hnodes hzero_not hcrit in

theorem one_le_hasseExp_of_chart (Φ : FamData p r) (l : Fin r) (hex : ∃ n : ℤ, IsContent Φ l n)
    (ht0 : Φ.t l ≠ 0) (ht_int : Φ.t l ∈ C.integers)
    (htpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (Φ.t l) < 0 → W = cuspInftyBar (1 * p))
    (hnode : ∃ a ∈ ssJSet p (ResidueField ↥A), (charLGeomPlaceOfPoint (ResidueField ↥A) a).HasValue (C.residue ⟨Φ.t l, ht_int⟩) 0) :
    1 ≤ hasseExp Φ l := by
  have h0 := hasseContent_nonneg_of_chart A hA C hint_iff hres hnodes hzero_not hcrit Φ l hex ht0 ht_int htpole
  by_contra hlt
  push_neg at hlt
  have hE : hasseExp Φ l = 0 := by omega
  have hc0 : hasseContent Φ l = 0 := by
    have := hasseExp_cast Φ l h0; rw [hE] at this; exact_mod_cast this.symm
  have hnI := isContent_hasseContent Φ l hex
  rw [hc0] at hnI
  have key := exists_frickeInvolutionBar_smul_mem_integers A hA C hcrit Φ l hnI
  have h1 : algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ (0 : ℤ))⁻¹) = 1 := by simp
  rw [h1, map_one, one_mul (Φ.t l)] at key
  obtain ⟨hwf_int, hwf_res⟩ := key
  obtain ⟨a, ha, hval⟩ := hnode
  exact hwf_res (ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar A hA C hint_iff hres hnodes hzero_not _ ht0 htpole ht_int hwf_int a ha hval)

include hA hint_iff hres hnodes hzero_not hcrit in

theorem goodFamilyZero_mem_comap_integers_residue_ne_zero_of_chart (Φ : FamData p r) (l : Fin r)
    (hex : ∃ n : ℤ, IsContent Φ l n) (ht0 : Φ.t l ≠ 0) (ht_int : Φ.t l ∈ C.integers)
    (htpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (Φ.t l) < 0 → W = cuspInftyBar (1 * p)) :
    ∃ h : goodFamilyZero Φ l ∈ (C.comap (frickeInvolutionBar (1 * p))).integers,
      (C.comap (frickeInvolutionBar (1 * p))).residue ⟨_, h⟩ ≠ 0 := by
  have h0 := hasseContent_nonneg_of_chart A hA C hint_iff hres hnodes hzero_not hcrit Φ l hex ht0 ht_int htpole
  obtain ⟨hf, k, hu⟩ := frickeInvolutionBar_goodFamilyZero_qCoeff Φ l hex h0 A hA
  obtain ⟨h, hres'⟩ := hcrit _ hf ⟨k, hu⟩
  exact ⟨h, by rw [ComponentChart.comap_residue_apply]; exact hres'⟩

end Sign

theorem zeroSeries_eq_one_of_t_eq_one (Φ : FamData p r) (l : Fin r) (h : Φ.t l = 1) : zeroSeries Φ l = 1 := by
  have h1 : (Φ.tRat l : LaurentSeries ℚ) = 1 := by
    have h2 : coeffEmb (AlgebraicClosure ℚ) (Φ.tRat l : LaurentSeries ℚ) = 1 := by
      have := congrArg Subtype.val (Φ.t_eq l)
      rw [h] at this
      exact this.symm
    exact (coeffEmb (AlgebraicClosure ℚ)).injective (by rw [h2, map_one])
  have h3 : Φ.tRat l = 1 := Subtype.ext h1
  rw [zeroSeries, h3, map_one]
  rfl

theorem isContent_zero_of_t_eq_one (Φ : FamData p r) (l : Fin r) (h : Φ.t l = 1) : IsContent Φ l 0 := by
  rw [IsContent, zeroSeries_eq_one_of_t_eq_one Φ l h]
  refine ⟨fun k hk => ?_, 0, ?_, ?_⟩
  · by_cases hk0 : k = 0
    · subst hk0; rw [HahnSeries.coeff_one]; simp
    · exfalso; apply hk; rw [HahnSeries.coeff_one]; simp [hk0]
  · rw [HahnSeries.coeff_one]; simp
  · rw [HahnSeries.coeff_one]; simp

theorem hasseExp_eq_zero_of_t_eq_one (Φ : FamData p r) (l : Fin r) (h : Φ.t l = 1) : hasseExp Φ l = 0 := by
  rw [hasseExp, hasseContent_eq_of_isContent (isContent_zero_of_t_eq_one Φ l h)]
  rfl

section Keyed

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) {r : ℕ} (Φ : FamCtx p r)

theorem infChart_mem_integers_iff (g : modularFunctionFieldBar (1 * p)) :
    g ∈ (infChart Γ).integers ↔ (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A) := by
  show g ∈ (chartFst Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply).integers ↔ _
  rw [chartFst_integers]
  exact mem_integersFst_iff_coe_mem_modularLocalized Γ.R g

theorem infChart_residue_eq_modularRedLocHom' (g : modularFunctionFieldBar (1 * p))
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)) :
    ∃ h : g ∈ (infChart Γ).integers,
      (((infChart Γ).residue ⟨g, h⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) : LaurentSeries (ResidueField ↥A))
        = CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, hg⟩ :=
  chartFst_residue_eq_modularRedLocHom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply g hg

theorem infChart_mem_nodes_iff (x : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
    x ∈ (infChart Γ).nodes ↔ ∃ a ∈ ssJSet p (ResidueField ↥A), charLGeomPlaceOfPoint (ResidueField ↥A) a = x :=
  mem_chartFst_nodes_iff Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply x

theorem infChart_criterion (g : modularFunctionFieldBar (1 * p))
    (hf : ∀ k : ℤ, (g : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A)
    (hu : ∃ k : ℤ, IsUnit (⟨(g : LaurentSeries (AlgebraicClosure ℚ)).coeff k, hf k⟩ : ↥A)) :
    ∃ h : g ∈ (infChart Γ).integers, (infChart Γ).residue ⟨g, h⟩ ≠ 0 :=
  chartFst_mem_integers_residue_ne_zero_of_qCoeff Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply g hf hu

theorem cuspZeroBar_not_mem_infChart_dom' : cuspZeroBar (1 * p) ∉ (infChart Γ).dom :=
  cuspZeroBar_not_mem_infChart_dom Γ

private theorem _root_.ModularCurve.MultCovering.t_ne_zero (l : Fin r) : Φ.t l ≠ 0 := Φ.t_basis.1.ne_zero l

p2m_export "ModularCurve.MultCovering" "t_ne_zero"
private theorem _root_.ModularCurve.MultCovering.t_mem_riemannRochSpace (l : Fin r) : Φ.t l ∈ riemannRochSpace (embDivisor (1 * p)) := by
  rw [← Φ.t_basis.2]
  exact Submodule.subset_span ⟨l, rfl⟩

p2m_export "ModularCurve.MultCovering" "t_mem_riemannRochSpace"
private theorem _root_.ModularCurve.MultCovering.t_pole (l : Fin r) :
    ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (Φ.t l) < 0 → W = cuspInftyBar (1 * p) := by
  intro W hW
  by_contra hne
  have h := (mem_riemannRochSpace_iff.mp (t_mem_riemannRochSpace p Φ l)) W
  rcases h with h | h
  · exact t_ne_zero p Φ l h
  · have : (embDivisor (1 * p)) W = 0 := by
      show ((embDegree (1 * p) : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) W = 0
      rw [Finsupp.smul_apply]
      first
      | rw [Finsupp.single_eq_of_ne hne, smul_zero]
      | rw [Finsupp.single_eq_of_ne (Ne.symm hne), smul_zero]
    rw [this, neg_zero] at h
    omega

p2m_export "ModularCurve.MultCovering" "t_pole"
include hA in

theorem exists_isContent_goodFamily (l : Fin r) : ∃ n : ℤ, IsContent Φ.toFamData l n := by
  obtain ⟨c, hc0, hcA⟩ := exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar p
    (embDegree (1 * p)) (Φ.t l) (t_mem_riemannRochSpace p Φ l) (t_ne_zero p Φ l) A hA
  exact exists_isContent Φ.toFamData l (t_ne_zero p Φ l) A hA c hc0 hcA

include hA in

theorem hasValue_zero_infChart_residue (l : Fin r) (hl : 1 ≤ (l : ℕ)) (hint : ∀ l, Φ.t l ∈ (infChart Γ).integers)
    (P : Fin r → Polynomial (ResidueField ↥A))
    (hP : (infChart Γ).residue ⟨Φ.t l, hint l⟩
      = ssPolyBar Γ * Polynomial.aeval (jBar (ResidueField ↥A)) (P l))
    (e : Fin (mAnnuli p)) :
    (charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e)).HasValue ((infChart Γ).residue ⟨Φ.t l, hint l⟩) 0 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  set v := charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e) with hv
  have hvrat : v.IsRational := isRational_place_modularFunctionFieldC_one (ResidueField ↥A) v

  have hfac : ∀ c : ResidueField ↥A, (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ c) ∈ v.toValuationSubring := by
    intro c
    by_cases h0 : (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ c) = 0
    · rw [h0]; exact zero_mem _
    · apply Place.mem_of_ord_nonneg _ h0
      rw [hv, ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap]
      split_ifs <;> omega
  have hj0 : v.HasValue (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e)) 0 := by
    rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos, map_zero, sub_zero]
    refine ⟨hfac _, ?_⟩
    by_cases h0 : (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e)) = 0
    · exact Or.inl h0
    · right; rw [hv, ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap, if_pos rfl]; exact zero_lt_one

  have hjmem : jBar (ResidueField ↥A) ∈ v.toValuationSubring := by
    have := add_mem (hfac (ssValue Γ e)) (v.algebraMap_mem' (ssValue Γ e))
    rwa [sub_add_cancel] at this
  have haeval : ∀ Q : Polynomial (ResidueField ↥A), Polynomial.aeval (jBar (ResidueField ↥A)) Q ∈ v.toValuationSubring := by
    intro Q
    rw [Polynomial.aeval_eq_sum_range]
    refine sum_mem fun n _ => ?_
    rw [Algebra.smul_def]
    exact mul_mem (v.algebraMap_mem' _) (pow_mem hjmem n)

  have hrest : (∏ e' ∈ Finset.univ.erase e, (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e'))) ∈ v.toValuationSubring :=
    prod_mem fun e' _ => hfac _
  obtain ⟨r₁, hr₁, -⟩ := v.exists_hasValue_of_surjective hvrat hrest
  obtain ⟨r₂, hr₂, -⟩ := v.exists_hasValue_of_surjective hvrat (haeval (P l))
  have hss : v.HasValue (ssPolyBar Γ) 0 := by
    have hsplit : ssPolyBar Γ = (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e)) *
        ∏ e' ∈ Finset.univ.erase e, (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e')) := by
      show (∏ e' : Fin (mAnnuli p), (jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e'))) = _
      exact (Finset.mul_prod_erase (Finset.univ)
        (fun e' => jBar (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ (ssValue Γ e')) (Finset.mem_univ e)).symm
    rw [hsplit]
    have := hj0.mul hr₁
    rwa [zero_mul] at this
  rw [hP]
  have := hss.mul hr₂
  rwa [zero_mul] at this

include hA Γ in

theorem hasseContent_nonneg (l : Fin r) : 0 ≤ hasseContent Φ.toFamData l := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨hint, -, -⟩ := Φ.t_inf A hA Γ
  exact hasseContent_nonneg_of_chart A hA (infChart Γ) (infChart_mem_integers_iff p A Γ)
    (infChart_residue_eq_modularRedLocHom' p A Γ) (infChart_mem_nodes_iff p A Γ)
    (cuspZeroBar_not_mem_infChart_dom' p A Γ) (infChart_criterion p A Γ)
    Φ.toFamData l (exists_isContent_goodFamily p A hA Φ l) (t_ne_zero p Φ l) (hint l) (t_pole p Φ l)

include hA Γ in
theorem hasseExp_eq_hasseContent (l : Fin r) : (hasseExp Φ.toFamData l : ℤ) = hasseContent Φ.toFamData l :=
  hasseExp_cast Φ.toFamData l (hasseContent_nonneg p A hA Γ Φ l)

include hA in

private theorem _root_.ModularCurve.MultCovering.zeroChart_residue_goodFamilyZero_ne_zero :
    ∃ hint : ∀ i, goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers,
      ∀ i, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, hint i⟩ ≠ 0 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨hint, -, -⟩ := Φ.t_inf A hA Γ
  have key : ∀ i, ∃ h : goodFamilyZero Φ.toFamData i ∈ (zeroChart Γ).integers,
      (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData i, h⟩ ≠ 0 := fun i =>
    goodFamilyZero_mem_comap_integers_residue_ne_zero_of_chart A hA (infChart Γ) (infChart_mem_integers_iff p A Γ)
      (infChart_residue_eq_modularRedLocHom' p A Γ) (infChart_mem_nodes_iff p A Γ)
      (cuspZeroBar_not_mem_infChart_dom' p A Γ) (infChart_criterion p A Γ)
      Φ.toFamData i (exists_isContent_goodFamily p A hA Φ i) (t_ne_zero p Φ i) (hint i) (t_pole p Φ i)
  exact ⟨fun i => (key i).1, fun i => (key i).2⟩

p2m_export "ModularCurve.MultCovering" "zeroChart_residue_goodFamilyZero_ne_zero"
include hA in

private theorem _root_.ModularCurve.MultCovering.goodFamilyZero_mem_zeroChart_integers : ∀ l : Fin r, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers :=
  (zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ).1

p2m_export "ModularCurve.MultCovering" "goodFamilyZero_mem_zeroChart_integers"
include hA Γ in

theorem one_le_hasseExp : ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp Φ.toFamData l := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  intro l hl
  obtain ⟨hint, -, P, hP, -, -⟩ := Φ.t_inf A hA Γ
  obtain ⟨a, ha⟩ := ssJSet_nonempty (q := p) (k := ResidueField ↥A)
  obtain ⟨e, he⟩ := exists_ssValue_eq Γ a ha
  have hval := hasValue_zero_infChart_residue p A hA Γ Φ l hl hint P (hP l hl).2 e
  refine one_le_hasseExp_of_chart A hA (infChart Γ) (infChart_mem_integers_iff p A Γ)
    (infChart_residue_eq_modularRedLocHom' p A Γ) (infChart_mem_nodes_iff p A Γ)
    (cuspZeroBar_not_mem_infChart_dom' p A Γ) (infChart_criterion p A Γ)
    Φ.toFamData l (exists_isContent_goodFamily p A hA Φ l) (t_ne_zero p Φ l) (hint l) (t_pole p Φ l)
    ⟨ssValue Γ e, ssValue_mem_ssJSet Γ e, hval⟩

theorem hasseExp_zero : ∀ l : Fin r, (l : ℕ) = 0 → hasseExp Φ.toFamData l = 0 := fun l hl =>
  hasseExp_eq_zero_of_t_eq_one Φ.toFamData l (Φ.t_zero l hl)

end Keyed

section Bound

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

include hA in

theorem exists_mem_dom_evalAt_eq_root (e : Fin (mAnnuli p)) (m : ℕ) (hm : 2 ≤ m) :
    ∃ c : AlgebraicClosure ℚ, c ^ m = (p : AlgebraicClosure ℚ) ∧ c ∈ A ∧
      ∃ Q ∈ (Δ.annOut e).dom, Q.evalAt (Δ.annOut e).param = c := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (p : AlgebraicClosure ℚ) (by omega : 0 < m)
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hc; exact hp0 hc.symm
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p

  have hcA : c ∈ A := by
    by_contra h
    have hinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left h
    have hp𝔪 : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA
    have hone : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) * (⟨c⁻¹, hinv⟩ : ↥A) ^ m = 1 := by
      apply Subtype.ext
      show (p : AlgebraicClosure ℚ) * (c⁻¹) ^ m = 1
      rw [← hc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hc0)]
    have : (1 : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [← hone]; exact Ideal.mul_mem_right _ _ hp𝔪
    exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  set cA : ↥A := ⟨c, hcA⟩ with hcA_def
  have hp𝔪 : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hA
  have hcApow : cA ^ m = ⟨(p : AlgebraicClosure ℚ), hpA⟩ := Subtype.ext (by simpa [hcA_def] using hc)
  have hc𝔪 : cA ∈ IsLocalRing.maximalIdeal ↥A :=
    (IsLocalRing.maximalIdeal.isMaximal ↥A).isPrime.mem_of_pow_mem m (by rw [hcApow]; exact hp𝔪)

  have hmod : (Δ.annOut e).modulus = ((p : ℕ) : ↥A) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_eq e
  have hw : 1 ≤ jWidth (ssValue Γ e) := jWidth_pos _
  have hpnat : ((p : ℕ) : ↥A) = ⟨(p : AlgebraicClosure ℚ), hpA⟩ := Subtype.ext (by simp)
  have hdiv : ∃ m' ∈ IsLocalRing.maximalIdeal ↥A, ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = c * m' := by
    refine ⟨cA ^ (m * jWidth (ssValue Γ e) - 1), ?_, ?_⟩
    · have h2 : 2 ≤ m * jWidth (ssValue Γ e) := le_trans (by omega) (Nat.mul_le_mul hm hw)
      exact Ideal.pow_mem_of_mem _ hc𝔪 _ (by omega)
    · rw [hmod, hpnat, ← hcApow, ← pow_mul]
      have : m * jWidth (ssValue Γ e) = (m * jWidth (ssValue Γ e) - 1) + 1 := by
        have : 1 ≤ m * jWidth (ssValue Γ e) := le_trans (by omega) (Nat.mul_le_mul (by omega : 1 ≤ m) hw)
        omega
      conv_lhs => rw [this, pow_succ]
      push_cast
      ring
  obtain ⟨Q, ⟨hQ, hQc⟩, -⟩ := (Δ.annOut e).existsUnique_evalAt_eq cA hc𝔪 (by exact hc0) hdiv
  exact ⟨c, hc, hcA, Q, hQ, hQc⟩

include hA in

theorem annOut_wide (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμp : μ (p : AlgebraicClosure ℚ) < 1)
    (e : Fin (mAnnuli p)) :
    ∃ Q₁ ∈ (Δ.annOut e).dom, ∃ Q₂ ∈ (Δ.annOut e).dom,
      μ (Q₁.evalAt (Δ.annOut e).param) ≠ μ (Q₂.evalAt (Δ.annOut e).param) := by
  obtain ⟨c₁, hc₁, -, Q₁, hQ₁, hQ₁c⟩ := exists_mem_dom_evalAt_eq_root p A hA Γ Δ e 2 le_rfl
  obtain ⟨c₂, hc₂, -, Q₂, hQ₂, hQ₂c⟩ := exists_mem_dom_evalAt_eq_root p A hA Γ Δ e 4 (by norm_num)
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁c, hQ₂c]
  intro h
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have h1 : μ c₁ ^ 4 = μ (p : AlgebraicClosure ℚ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← map_pow, hc₁]
  have h2 : μ c₂ ^ 4 = μ (p : AlgebraicClosure ℚ) := by rw [← map_pow, hc₂]
  rw [h] at h1
  rw [h1] at h2

  nlinarith

include hA Γ Δ in

theorem hasseExp_le_modulusExp : ∀ l : Fin r, hasseExp Φ.toFamData l ≤ modulusExp := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  intro l
  rw [show modulusExp = 3 from rfl]
  by_cases hl : (l : ℕ) = 0
  · rw [hasseExp_zero p Φ l hl]; omega
  have hl1 : 1 ≤ (l : ℕ) := by omega
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint, hnode⟩ := infChart_nodeData_exists_node_of_member p A hA Γ Φ
  obtain ⟨e, he1⟩ := hnode l hl1
  obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  set n := hasseExp Φ.toFamData l with hn
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hdom : (Δ.annIn e).dom = (Δ.annOut e).dom := (Δ.dom_eq e).symm
  have hmodq : (Δ.annIn e).modulus = (Δ.annOut e).modulus := (Δ.modulus_eq' e).symm
  have hmod0 : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_ne_zero e
  have htwo : (Δ.annIn e).param * (Δ.annOut e).param
      = algebraMap (AlgebraicClosure ℚ) _ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm (Δ.annIn e).param (Δ.annOut e).param, Δ.modulus_eq' e]; exact Δ.param_mul_param e
  have hatt : (Δ.annOut e).IsAttached (infChart Γ) (nodeTgt Γ e) := Δ.attached_tgt e
  have hatt' : (Δ.annIn e).IsAttached (zeroChart Γ) (nodeSrc Γ e) := Δ.attached_src e
  have hwide := annOut_wide p A hA Γ Δ μ hμp e

  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (Φ.t l) := by
    intro Q hQ
    by_contra hneg
    push_neg at hneg
    obtain rfl := t_pole p Φ l Q hneg
    rw [← hdom, Δ.mem_dom_iff] at hQ
    exact not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply _
      (cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply) _ (ssValue_mem_ssJSet Γ e) hQ
  have hcA : (p : AlgebraicClosure ℚ) ^ n ∈ A := pow_mem (natCast_mem A p) n
  have hb := AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt (zeroChart Γ) (nodeSrc Γ e) hatt'
    hwide (Φ.t l) (hint l) (hres_ne l) ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA
    (hint0 l) (hres0 l) hpole
  rw [he1, zpow_one] at hb

  have hmodval : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e, Δ.modulus_eq e]; push_cast; rfl
  rw [hmodval, map_pow, map_pow] at hb
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hnw : n ≤ jWidth (ssValue Γ e) := (pow_le_pow_iff_right_of_lt_one₀ hμp0 hμp).mp hb
  rcases jWidth_eq_one_or (ssValue Γ e) with h | h | h <;> omega

end Bound

section WidthOne

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

include hA Δ in

theorem twoEnd_bounds (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμp : μ (p : AlgebraicClosure ℚ) < 1)
    (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    (hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers) (hres : ∀ l, (infChart Γ).residue ⟨goodFamily Φ l, hint l⟩ ≠ 0)
    (hint0 : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hres0 : ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0 l⟩ ≠ 0)
    (e : Fin (mAnnuli p)) (l : Fin r) :
    (μ (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e)) ^ (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint l⟩)
        ≤ μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l ∧
      μ (p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l *
        (μ (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e))
          ^ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0 l⟩) ≤ 1 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  set n := hasseExp Φ.toFamData l with hn
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdom : (Δ.annIn e).dom = (Δ.annOut e).dom := (Δ.dom_eq e).symm
  have hmodq : (Δ.annIn e).modulus = (Δ.annOut e).modulus := (Δ.modulus_eq' e).symm
  have hmod0 : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_ne_zero e
  have htwo : (Δ.annIn e).param * (Δ.annOut e).param
      = algebraMap (AlgebraicClosure ℚ) _ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm (Δ.annIn e).param (Δ.annOut e).param, Δ.modulus_eq' e]; exact Δ.param_mul_param e
  have hatt : (Δ.annOut e).IsAttached (infChart Γ) (nodeTgt Γ e) := Δ.attached_tgt e
  have hatt' : (Δ.annIn e).IsAttached (zeroChart Γ) (nodeSrc Γ e) := Δ.attached_src e
  have hwide := annOut_wide p A hA Γ Δ μ hμp e
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (Φ.t l) := by
    intro Q hQ
    by_contra hneg
    push_neg at hneg
    obtain rfl := t_pole p Φ l Q hneg
    rw [← hdom, Δ.mem_dom_iff] at hQ
    exact not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply _
      (cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply) _ (ssValue_mem_ssJSet Γ e) hQ
  have hcA : (p : AlgebraicClosure ℚ) ^ n ∈ A := pow_mem (natCast_mem A p) n
  have hmodval : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e, Δ.modulus_eq e]; push_cast; rfl
  have hb := AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt (zeroChart Γ) (nodeSrc Γ e) hatt'
    hwide (Φ.t l) (hint l) (hres l) ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA
    (hint0 l) (hres0 l) hpole
  have hb' := AlgebraicCurve.Annulus.abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt (zeroChart Γ) (nodeSrc Γ e) hatt'
    hwide (Φ.t l) (hint l) (hres l) ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA
    (hint0 l) (hres0 l) hpole
  rw [hmodval, map_pow, map_pow] at hb hb'
  exact ⟨hb, hb'⟩

include hA Δ in

theorem exists_node_hasseExp_le_jWidth : ∀ l : Fin r, 1 ≤ (l : ℕ) → ∃ e : Fin (mAnnuli p),
    hasseExp Φ.toFamData l ≤ jWidth (ssValue Γ e) := by
  intro l hl1
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint, hnode⟩ := infChart_nodeData_exists_node_of_member p A hA Γ Φ
  obtain ⟨e, he1⟩ := hnode l hl1
  obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  obtain ⟨hb, -⟩ := twoEnd_bounds p A hA Γ Δ Φ μ hμp hμA hint hres_ne hint0 hres0 e l
  refine ⟨e, ?_⟩
  rw [he1, zpow_one] at hb
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  exact (pow_le_pow_iff_right_of_lt_one₀ hμp0 hμp).mp hb

include hA Δ in

theorem hasseExp_le_one_of_forall_widthOne (hw : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∀ l : Fin r, hasseExp Φ.toFamData l ≤ 1 := by
  intro l
  by_cases hl : (l : ℕ) = 0
  · rw [hasseExp_zero p Φ l hl]; omega
  obtain ⟨e, he⟩ := exists_node_hasseExp_le_jWidth p A hA Γ Δ Φ l (by omega)
  rw [jWidth_of_ne (hw e).1 (hw e).2] at he
  exact he

include hA Δ in

theorem neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero (hw : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      ∀ (e : Fin (mAnnuli p)) (l : Fin r),
        -1 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  refine ⟨hint0, fun e l => ?_⟩
  obtain ⟨-, hb'⟩ := twoEnd_bounds p A hA Γ Δ Φ μ hμp hμA hint2 hres_ne hint0 hres0 e l
  have hn1 := hasseExp_le_one_of_forall_widthOne p A hA Γ Δ Φ hw l
  rw [jWidth_of_ne (hw e).1 (hw e).2, pow_one] at hb'
  set a' := (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0 l⟩) with ha'
  set n := hasseExp Φ.toFamData l with hn
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

  have hz : μ (p : AlgebraicClosure ℚ) ^ ((n : ℤ) + a') ≤ 1 := by
    rw [zpow_add₀ hμp0.ne', zpow_natCast]; exact hb'
  have h0 : 0 ≤ (n : ℤ) + a' := (zpow_le_one_iff_right_of_lt_one₀ hμp0 hμp).mp hz
  omega

include hA in

theorem zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes :
    ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      ∀ (l : Fin r) (v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)),
        v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  refine ⟨hint0, fun l v hv => ?_⟩
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero _).mpr (pow_ne_zero _ hp0))
  have hg0 : goodFamilyZero Φ.toFamData l ≠ 0 := mul_ne_zero hx0 (t_ne_zero p Φ l)
  apply AlgebraicCurve.ComponentChart.ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg
    (zeroChart Γ) (goodFamilyZero Φ.toFamData l) hg0 (hint0 l) (hres0 l) _ v hv

  intro P hP
  have hord : P.ord (goodFamilyZero Φ.toFamData l) = P.ord (Φ.t l) := by
    show P.ord (_ * Φ.t l) = _
    rw [P.ord_mul hx0 (t_ne_zero p Φ l), Place.ord_inv, Place.ord_algebraMap, neg_zero, zero_add]
  rw [hord]
  by_contra hneg
  push_neg at hneg
  obtain rfl := t_pole p Φ l P hneg

  apply cuspZeroBar_not_mem_infChart_dom' p A Γ
  have hP' : frickeInvolutionBar (1 * p) • cuspInftyBar (1 * p) ∈ (infChart Γ).dom :=
    (ComponentChart.mem_comap_dom (frickeInvolutionBar (1 * p)) (infChart Γ) _).mp hP
  rw [cuspZeroBar_def]
  exact hP'

end WidthOne

section Orth

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)

theorem coe_sum_single_smul_coeff (X : Fin r → ↥(modularFunctionFieldFull (1 * p))) (l : Fin r) (a : ℚ) (m : ℤ) :
    (((∑ i, (Pi.single l a : Fin r → ℚ) i • X i : ↥(modularFunctionFieldFull (1 * p)))) : LaurentSeries ℚ).coeff m
      = a * ((X l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m := by
  rw [Finset.sum_eq_single l (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul])
    (fun h => (h (Finset.mem_univ l)).elim), Pi.single_eq_same]
  first
  | rfl
  | (rw [IntermediateField.coe_smul]; rfl)
  | simp [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul]

namespace FamData p2m_export "ModularCurve.MultCovering.FamData" "t t_eq tRat" end FamData
p2m_open_scoped "ModularCurve.MultCovering.FamData" in
theorem FamData.t_ne_zero (hbasis : IsEmbBasis (1 * p) D.t) (l : Fin r) : D.t l ≠ 0 := hbasis.1.ne_zero l

p2m_open_scoped "ModularCurve.MultCovering.FamData" in
theorem FamData.t_mem_riemannRochSpace (hbasis : IsEmbBasis (1 * p) D.t) (l : Fin r) :
    D.t l ∈ riemannRochSpace (embDivisor (1 * p)) := by
  rw [← hbasis.2]; exact Submodule.subset_span ⟨l, rfl⟩

p2m_open_scoped "ModularCurve.MultCovering.FamData" in
theorem FamData.t_pole (hbasis : IsEmbBasis (1 * p) D.t) (l : Fin r) :
    ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)), W.ord (D.t l) < 0 → W = cuspInftyBar (1 * p) := by
  intro W hW
  by_contra hne
  rcases (mem_riemannRochSpace_iff.mp (FamData.t_mem_riemannRochSpace p D hbasis l)) W with h | h
  · exact FamData.t_ne_zero p D hbasis l h
  · have : (embDivisor (1 * p)) W = 0 := by
      show ((embDegree (1 * p) : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) W = 0
      rw [Finsupp.smul_apply]
      first
      | rw [Finsupp.single_eq_of_ne hne, smul_zero]
      | rw [Finsupp.single_eq_of_ne (Ne.symm hne), smul_zero]
    rw [this, neg_zero] at h
    omega

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.exists_isContent_of_isEmbBasis (hbasis : IsEmbBasis (1 * p) D.t)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (l : Fin r) : ∃ n : ℤ, IsContent D l n := by
  obtain ⟨c, hc0, hcA⟩ := exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar p
    (embDegree (1 * p)) (D.t l) (FamData.t_mem_riemannRochSpace p D hbasis l) (FamData.t_ne_zero p D hbasis l) A hA
  exact exists_isContent D l (FamData.t_ne_zero p D hbasis l) A hA c hc0 hcA

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.hasseContent_nonneg_of_orth (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (l : Fin r) : 0 ≤ hasseContent D l := by
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  have hn := isContent_hasseContent D l (FamData.exists_isContent_of_isEmbBasis p D hbasis A hA l)
  obtain ⟨k₀, hk₀, hk₀n⟩ := hn.2
  have key := (horthZero (Pi.single l 1)).mpr (fun i => by
    by_cases hi : i = l
    · subst hi; rw [Pi.single_eq_same, padicValRat.one]; omega
    · rw [Pi.single_eq_of_ne hi, padicValRat.zero]; omega) k₀
  rw [coe_sum_single_smul_coeff, one_mul] at key
  rw [← hk₀n]
  exact key

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.exists_zeroChart_residue_goodFamilyZero_ne_zero_of_orth (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∃ hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers,
      ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ ≠ 0 := by
  have key : ∀ l, ∃ h : goodFamilyZero D l ∈ (zeroChart Γ).integers, (zeroChart Γ).residue ⟨goodFamilyZero D l, h⟩ ≠ 0 := by
    intro l
    obtain ⟨hf, k, hu⟩ := frickeInvolutionBar_goodFamilyZero_qCoeff D l
      (FamData.exists_isContent_of_isEmbBasis p D hbasis A hA l) (FamData.hasseContent_nonneg_of_orth p D hbasis horthZero l) A hA
    obtain ⟨h, hres⟩ := infChart_criterion p A Γ _ hf ⟨k, hu⟩
    refine ⟨h, ?_⟩
    show ((infChart Γ).comap (frickeInvolutionBar (1 * p))).residue ⟨goodFamilyZero D l, h⟩ ≠ 0
    rw [ComponentChart.comap_residue_apply]
    exact hres
  exact ⟨fun l => (key l).1, fun l => (key l).2⟩

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.goodFamilyZero_mem_zeroChart_integers (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers :=
  (FamData.exists_zeroChart_residue_goodFamilyZero_ne_zero_of_orth p D hbasis horthZero A hA Γ).1

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.zeroChart_residue_goodFamilyZero_ne_zero (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩ ≠ 0 := by
  obtain ⟨h, hne⟩ := FamData.exists_zeroChart_residue_goodFamilyZero_ne_zero_of_orth p D hbasis horthZero A hA Γ
  exact hne

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    ∀ (l : Fin r) (v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)),
      v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  have hres0 := FamData.zeroChart_residue_goodFamilyZero_ne_zero p D hbasis horthZero A hA Γ hint
  intro l v hv
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((p : AlgebraicClosure ℚ) ^ hasseExp D l))⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero _).mpr (pow_ne_zero _ hp0))
  have hg0 : goodFamilyZero D l ≠ 0 := mul_ne_zero hx0 (FamData.t_ne_zero p D hbasis l)
  apply AlgebraicCurve.ComponentChart.ord_residue_nonneg_of_not_mem_nodes_of_forall_mem_dom_ord_nonneg
    (zeroChart Γ) (goodFamilyZero D l) hg0 (hint l) (hres0 l) _ v hv
  intro P hP
  have hord : P.ord (goodFamilyZero D l) = P.ord (D.t l) := by
    show P.ord (_ * D.t l) = _
    rw [P.ord_mul hx0 (FamData.t_ne_zero p D hbasis l), Place.ord_inv, Place.ord_algebraMap, neg_zero, zero_add]
  rw [hord]
  by_contra hneg
  push_neg at hneg
  obtain rfl := FamData.t_pole p D hbasis l P hneg
  apply cuspZeroBar_not_mem_infChart_dom' p A Γ
  have hP' : frickeInvolutionBar (1 * p) • cuspInftyBar (1 * p) ∈ (infChart Γ).dom :=
    (ComponentChart.mem_comap_dom (frickeInvolutionBar (1 * p)) (infChart Γ) _).mp hP
  rw [cuspZeroBar_def]
  exact hP'

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.exists_infChart_residue_t_ne_zero_of_orthInf
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (l : Fin r) :
    ∃ h : D.t l ∈ (infChart Γ).integers, (infChart Γ).residue ⟨D.t l, h⟩ ≠ 0 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set g : LaurentSeries ℚ := ((D.tRat l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ) with hg

  have hle : ∀ k : ℤ, g.coeff k ≠ 0 → (0 : ℤ) ≤ padicValRat p (g.coeff k) := by
    intro k _
    have key := (horthInf (Pi.single l 1)).mpr (fun i => by
      by_cases hi : i = l
      · subst hi; rw [Pi.single_eq_same, padicValRat.one]
      · rw [Pi.single_eq_of_ne hi, padicValRat.zero]) k
    rw [coe_sum_single_smul_coeff, one_mul] at key
    exact key

  have hnot : ¬ ∀ i, (0 : ℤ) ≤ padicValRat p ((Pi.single l ((p : ℚ)⁻¹) : Fin r → ℚ) i) := by
    intro h
    have := h l
    rw [Pi.single_eq_same, padicValRat.inv, padicValRat.self (Fact.out : p.Prime).one_lt] at this
    omega
  rw [← horthInf] at hnot
  push_neg at hnot
  obtain ⟨m, hm⟩ := hnot
  rw [coe_sum_single_smul_coeff] at hm
  have hm0 : g.coeff m ≠ 0 := by
    intro h0; rw [← hg, h0, mul_zero, padicValRat.zero] at hm; exact lt_irrefl _ hm
  have hv0 : padicValRat p (g.coeff m) = 0 := by
    rw [← hg, padicValRat.mul (inv_ne_zero hp0) hm0, padicValRat.inv, padicValRat.self (Fact.out : p.Prime).one_lt] at hm
    have := hle m hm0
    omega
  obtain ⟨h1, h2⟩ := coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat A (Fact.out : p.Prime) hA g 0
    (fun k hk => by exact_mod_cast hle k hk) m hm0 (by rw [hv0]; try rfl)
  have hsm : ((p : ℚ) ^ (0 : ℤ))⁻¹ • g = g := by rw [zpow_zero, inv_one, one_smul]
  rw [hsm] at h1 h2
  have hcoe : ((D.t l : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) g := by
    rw [D.t_eq l]
  have hf : ∀ k : ℤ, ((D.t l : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A := by
    intro k; rw [hcoe]; exact h1 k
  refine infChart_criterion p A Γ (D.t l) hf ⟨m, ?_⟩
  rw [ValuationSubring.valuation_eq_one_iff]
  refine le_antisymm (A.valuation_le_one _) ?_
  have h3 : ¬ A.valuation ((coeffEmb (AlgebraicClosure ℚ) g).coeff m) < 1 :=
    fun h => h2 ((ValuationSubring.mem_nonunits_iff A).mpr h)
  rw [not_lt, ← hcoe] at h3
  exact h3

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.neg_one_le_ord_nodeSrc_residue_goodFamilyZero' (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (hle1 : ∀ l : Fin r, hasseExp D l ≤ 1)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    ∀ (e : Fin (mAnnuli p)) (l : Fin r), -1 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) := by
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  intro e l
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hC, hres⟩ := FamData.exists_infChart_residue_t_ne_zero_of_orthInf p D horthInf A hA Γ l
  have hres0 := FamData.zeroChart_residue_goodFamilyZero_ne_zero p D hbasis horthZero A hA Γ hint
  set n := hasseExp D l with hn
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdom : (Δ.annIn e).dom = (Δ.annOut e).dom := (Δ.dom_eq e).symm
  have hmodq : (Δ.annIn e).modulus = (Δ.annOut e).modulus := (Δ.modulus_eq' e).symm
  have hmod0 : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_ne_zero e
  have htwo : (Δ.annIn e).param * (Δ.annOut e).param
      = algebraMap (AlgebraicClosure ℚ) _ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm (Δ.annIn e).param (Δ.annOut e).param, Δ.modulus_eq' e]; exact Δ.param_mul_param e
  have hatt : (Δ.annOut e).IsAttached (infChart Γ) (nodeTgt Γ e) := Δ.attached_tgt e
  have hatt' : (Δ.annIn e).IsAttached (zeroChart Γ) (nodeSrc Γ e) := Δ.attached_src e
  have hwide := annOut_wide p A hA Γ Δ μ hμp e
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (D.t l) := by
    intro Q hQ
    by_contra hneg
    push_neg at hneg
    obtain rfl := FamData.t_pole p D hbasis l Q hneg
    rw [← hdom, Δ.mem_dom_iff] at hQ
    exact not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply _
      (cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply) _ (ssValue_mem_ssJSet Γ e) hQ
  have hcA : (p : AlgebraicClosure ℚ) ^ n ∈ A := pow_mem (natCast_mem A p) n
  have hb' := AlgebraicCurve.Annulus.abv_mul_abv_modulus_zpow_ord_residue_le_one_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt (zeroChart Γ) (nodeSrc Γ e) hatt'
    hwide (D.t l) hC hres ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA (hint l) (hres0 l) hpole
  have hmodval : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e, Δ.modulus_eq e]; push_cast; rfl
  rw [hmodval, map_pow, map_pow] at hb'
  set a' := (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) with ha'
  set w := jWidth (ssValue Γ e) with hw_def
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hz : μ (p : AlgebraicClosure ℚ) ^ ((n : ℤ) + (w : ℤ) * a') ≤ 1 := by
    rw [zpow_add₀ hμp0.ne', zpow_mul, zpow_natCast, zpow_natCast]; exact hb'
  have h0 : 0 ≤ (n : ℤ) + (w : ℤ) * a' := (zpow_le_one_iff_right_of_lt_one₀ hμp0 hμp).mp hz
  have hw1 : (1 : ℤ) ≤ w := by exact_mod_cast jWidth_pos (ssValue Γ e)
  have hn1 : (n : ℤ) ≤ 1 := by exact_mod_cast hle1 l
  by_contra hlt
  push_neg at hlt
  have : (w : ℤ) * a' ≤ a' := by nlinarith
  omega

end Orth

section OrthOne

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)

p2m_open_scoped "ModularCurve.MultCovering.FamData" in
theorem FamData.tRat_eq_one_of_t_eq_one (l : Fin r) (h : D.t l = 1) : D.tRat l = 1 := by
  have h2 : coeffEmb (AlgebraicClosure ℚ) (D.tRat l : LaurentSeries ℚ) = 1 := by
    have := congrArg Subtype.val (D.t_eq l)
    rw [h] at this
    exact this.symm
  exact Subtype.ext ((coeffEmb (AlgebraicClosure ℚ)).injective (by rw [h2, OneMemClass.coe_one, map_one]))

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.one_le_hasseExp_of_orth
    (hzero : ∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1)
    (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp D l := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  intro l hl
  by_contra hlt
  push_neg at hlt
  have h0n : hasseExp D l = 0 := by omega
  have hp : (p : ℕ).Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hAp : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA

  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) l.2
  set l₀ : Fin r := ⟨0, hr⟩ with hl₀
  have hl0 : (l₀ : ℕ) = 0 := rfl
  have hll₀ : l ≠ l₀ := by intro h; rw [h, hl0] at hl; omega
  have ht0 : D.tRat l₀ = 1 := FamData.tRat_eq_one_of_t_eq_one p D l₀ (hzero l₀ hl0)

  obtain ⟨hint, hres0⟩ := FamData.exists_zeroChart_residue_goodFamilyZero_ne_zero_of_orth p D hbasis horthZero A hA Γ
  have hg : goodFamilyZero D l = D.t l := by
    show (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp D l))⁻¹ * D.t l = D.t l
    rw [h0n, pow_zero, map_one, inv_one, one_mul (D.t l)]
  have hunit : ∃ h : frickeInvolutionBar (1 * p) (D.t l) ∈ (infChart Γ).integers, (infChart Γ).residue ⟨_, h⟩ ≠ 0 := by
    have e1 : frickeInvolutionBar (1 * p) (goodFamilyZero D l) = frickeInvolutionBar (1 * p) (D.t l) := by rw [hg]
    have key : ∃ h : frickeInvolutionBar (1 * p) (goodFamilyZero D l) ∈ (infChart Γ).integers,
        (infChart Γ).residue ⟨_, h⟩ ≠ 0 := by
      refine ⟨hint l, ?_⟩
      have := hres0 l
      rwa [show (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩
        = (infChart Γ).residue ⟨frickeInvolutionBar (1 * p) (goodFamilyZero D l), hint l⟩ from
          ComponentChart.comap_residue_apply _ _ _] at this
    rw [e1] at key
    exact key
  obtain ⟨hwf_int, hwf_res⟩ := hunit

  obtain ⟨hf_int, -⟩ := FamData.exists_infChart_residue_t_ne_zero_of_orthInf p D horthInf A hA Γ l

  obtain ⟨c₀, hc₀, hconst⟩ :=
    ComponentChart.exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar A hA (infChart Γ)
      (infChart_mem_integers_iff p A Γ) (infChart_residue_eq_modularRedLocHom' p A Γ) (infChart_mem_nodes_iff p A Γ)
      (cuspZeroBar_not_mem_infChart_dom' p A Γ) (D.t l) (FamData.t_ne_zero p D hbasis l) (FamData.t_pole p D hbasis l)
      hf_int hwf_int hwf_res

  set b : ℤ → ℚ := fun m => (zeroSeries D l).coeff m with hb
  have hcontent := isContent_hasseContent D l (FamData.exists_isContent_of_isEmbBasis p D hbasis A hA l)
  have hc0 : hasseContent D l = 0 := by
    have h1 := hasseExp_cast D l (FamData.hasseContent_nonneg_of_orth p D hbasis horthZero l)
    rw [h0n] at h1; exact_mod_cast h1.symm
  have hbint : ∀ m, b m ≠ 0 → 0 ≤ padicValRat p (b m) := by
    intro m hm; have := hcontent.1 m hm; rw [hc0] at this; exact this
  have hbA : ∀ m, ((b m : ℚ) : AlgebraicClosure ℚ) ∈ A := by
    intro m
    by_cases hm : b m = 0
    · rw [hm, Rat.cast_zero]; exact zero_mem A
    · exact (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp hm).mpr (hbint m hm)
  have hcoeff : ∀ m, ((frickeInvolutionBar (1 * p) (D.t l) : modularFunctionFieldBar (1 * p)) :
      LaurentSeries (AlgebraicClosure ℚ)).coeff m = ((b m : ℚ) : AlgebraicClosure ℚ) := by
    intro m; rw [coe_frickeInvolutionBar_t, coeffEmb_coeff, eq_ratCast]

  have h₂ : ((frickeInvolutionBar (1 * p) (D.t l) : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A) :=
    (infChart_mem_integers_iff p A Γ _).mp hwf_int
  obtain ⟨hwf_int', hres₂⟩ := infChart_residue_eq_modularRedLocHom' p A Γ _ h₂
  have hint_coeffs : ((frickeInvolutionBar (1 * p) (D.t l) : modularFunctionFieldBar (1 * p)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring := fun m => by
    rw [hcoeff]; exact hbA m
  have hred : ∀ m : ℤ, IsLocalRing.residue ↥A ⟨((b m : ℚ) : AlgebraicClosure ℚ), hbA m⟩
      = (HahnSeries.single (0 : ℤ) c₀ : LaurentSeries (ResidueField ↥A)).coeff m := by
    intro m
    have e2 := hres₂
    rw [hconst, CharPReduction.modularRedLocHom_eq_coeffRed _ _ _ _ hint_coeffs] at e2

    have e3 := congrArg (fun z : LaurentSeries (ResidueField ↥A) => z.coeff m) e2
    simp only [CharPReduction.coeffRed_coeff] at e3
    rw [← algebraMap_laurentSeries_eq_single]
    convert e3.symm using 2 <;> try rfl
    simp only [hcoeff]

  have hbpos : ∀ m, m ≠ 0 → b m ≠ 0 → 1 ≤ padicValRat p (b m) := by
    intro m hm hbm
    have h1 : IsLocalRing.residue ↥A ⟨((b m : ℚ) : AlgebraicClosure ℚ), hbA m⟩ = 0 := by
      rw [hred m, HahnSeries.coeff_single_of_ne hm]
    rw [IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff] at h1
    have h2 : padicValRat p (b m) ≠ 0 := fun h =>
      (lt_irrefl _) (h1.trans_le ((ValuationSubring.valuation_ratCast_eq_one_iff_padicValRat_eq_zero A hp hAp hbm).mpr h).ge)
    have := hbint m hbm
    omega

  set cv : Fin r → ℚ := Pi.single l ((p : ℚ)⁻¹) - Pi.single l₀ ((p : ℚ)⁻¹ * b 0) with hcv
  have hsum : ∀ m : ℤ, (((∑ i, cv i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p)))) :
      LaurentSeries ℚ).coeff m = (p : ℚ)⁻¹ * b m - (p : ℚ)⁻¹ * b 0 * ((1 : LaurentSeries ℚ).coeff m) := by
    intro m
    have : (∑ i, cv i • frickeInvolutionFull (1 * p) (D.tRat i) : ↥(modularFunctionFieldFull (1 * p)))
        = (∑ i, (Pi.single l ((p : ℚ)⁻¹) : Fin r → ℚ) i • frickeInvolutionFull (1 * p) (D.tRat i))
          - ∑ i, (Pi.single l₀ ((p : ℚ)⁻¹ * b 0) : Fin r → ℚ) i • frickeInvolutionFull (1 * p) (D.tRat i) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcv, Pi.sub_apply, sub_smul]
    rw [this, AddSubgroupClass.coe_sub]
    first
    | rw [HahnSeries.coeff_sub]
    | rw [HahnSeries.sub_coeff]
    | simp only [HahnSeries.coeff_sub', Pi.sub_apply]
    rw [coe_sum_single_smul_coeff, coe_sum_single_smul_coeff, ht0, map_one]
    rfl
  have hLHS : ∀ m : ℤ, 0 ≤ padicValRat p ((((∑ i, cv i • frickeInvolutionFull (1 * p) (D.tRat i) :
      ↥(modularFunctionFieldFull (1 * p)))) : LaurentSeries ℚ).coeff m) := by
    intro m
    rw [hsum]
    by_cases hm : m = 0
    · subst hm
      rw [HahnSeries.coeff_one]
      simp
    · rw [HahnSeries.coeff_one, if_neg hm, mul_zero, sub_zero]
      by_cases hbm : b m = 0
      · rw [hbm, mul_zero, padicValRat.zero]
      · rw [padicValRat.mul (inv_ne_zero hp0) hbm, padicValRat.inv, padicValRat.self hp.one_lt]
        have := hbpos m hm hbm
        omega
  have hRHS := (horthZero cv).mp hLHS l
  rw [hcv, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hll₀, sub_zero, padicValRat.inv,
    padicValRat.self hp.one_lt, h0n] at hRHS
  simp at hRHS

end OrthOne

section OrthZ1

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.inf_h0_of_one_le_hasseExp (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (hge1 : ∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ hasseExp D l) :
    ∀ l : Fin r, 1 ≤ (l : ℕ) → ∀ m : ℤ, 0 ≤ padicValRat p ((p : ℚ)⁻¹ *
      ((frickeInvolutionFull (1 * p) (D.tRat l) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m) := by
  intro l hl m
  have hp : (p : ℕ).Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, Fact.out⟩
  have hcontent := isContent_hasseContent D l (FamData.exists_isContent_of_isEmbBasis p D hbasis A hA l)
  have hcast := hasseExp_cast D l (FamData.hasseContent_nonneg_of_orth p D hbasis horthZero l)
  by_cases hbm : (zeroSeries D l).coeff m = 0
  · show 0 ≤ padicValRat p ((p : ℚ)⁻¹ * (zeroSeries D l).coeff m)
    rw [hbm, mul_zero, padicValRat.zero]
  · show 0 ≤ padicValRat p ((p : ℚ)⁻¹ * (zeroSeries D l).coeff m)
    rw [padicValRat.mul (inv_ne_zero hp0) hbm, padicValRat.inv, padicValRat.self hp.one_lt]
    have h1 := hcontent.1 m hbm
    have h2 := hge1 l hl
    have h3 : (1 : ℤ) ≤ hasseContent D l := by rw [← hcast]; exact_mod_cast h2
    omega

p2m_open_scoped "ModularCurve.MultCovering.FamData" in

theorem FamData.hasseExp_le_one_of_orth_of_node (hzero : ∀ l : Fin r, (l : ℕ) = 0 → D.t l = 1)
    (hbasis : IsEmbBasis (1 * p) D.t)
    (horthInf : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • D.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, 0 ≤ padicValRat p (c i))
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    (hw1 : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728)
    (hnode1 : ∃ hint : ∀ l, D.t l ∈ (infChart Γ).integers, ∀ l : Fin r, 1 ≤ (l : ℕ) →
      ∃ e : Fin (mAnnuli p), (nodeTgt Γ e).ord ((infChart Γ).residue ⟨D.t l, hint l⟩) = 1) :
    ∀ l : Fin r, hasseExp D l ≤ 1 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  intro l
  by_cases hl : (l : ℕ) = 0
  · rw [hasseExp_eq_zero_of_t_eq_one D l (hzero l hl)]; omega
  have hl1 : 1 ≤ (l : ℕ) := by omega
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint1, hnode⟩ := hnode1
  obtain ⟨e, he1⟩ := hnode l hl1
  obtain ⟨hC, hres⟩ := FamData.exists_infChart_residue_t_ne_zero_of_orthInf p D horthInf A hA Γ l
  obtain ⟨hint0, hres0⟩ := FamData.exists_zeroChart_residue_goodFamilyZero_ne_zero_of_orth p D hbasis horthZero A hA Γ
  set n := hasseExp D l with hn
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hdom : (Δ.annIn e).dom = (Δ.annOut e).dom := (Δ.dom_eq e).symm
  have hmodq : (Δ.annIn e).modulus = (Δ.annOut e).modulus := (Δ.modulus_eq' e).symm
  have hmod0 : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Δ.modulus_eq' e]; exact Δ.modulus_ne_zero e
  have htwo : (Δ.annIn e).param * (Δ.annOut e).param
      = algebraMap (AlgebraicClosure ℚ) _ ((Δ.annOut e).modulus : AlgebraicClosure ℚ) := by
    rw [mul_comm (Δ.annIn e).param (Δ.annOut e).param, Δ.modulus_eq' e]; exact Δ.param_mul_param e
  have hatt : (Δ.annOut e).IsAttached (infChart Γ) (nodeTgt Γ e) := Δ.attached_tgt e
  have hatt' : (Δ.annIn e).IsAttached (zeroChart Γ) (nodeSrc Γ e) := Δ.attached_src e
  have hwide := annOut_wide p A hA Γ Δ μ hμp e
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (D.t l) := by
    intro Q hQ
    by_contra hneg
    push_neg at hneg
    obtain rfl := FamData.t_pole p D hbasis l Q hneg
    rw [← hdom, Δ.mem_dom_iff] at hQ
    exact not_isSSCentred_of_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply _
      (cuspInftyBar_mem_chartFst_dom Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply) _ (ssValue_mem_ssJSet Γ e) hQ
  have hcA : (p : AlgebraicClosure ℚ) ^ n ∈ A := pow_mem (natCast_mem A p) n
  have hb := AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom hmodq hmod0 htwo (infChart Γ) (nodeTgt Γ e) hatt (zeroChart Γ) (nodeSrc Γ e) hatt'
    hwide (D.t l) hC hres ((p : AlgebraicClosure ℚ) ^ n) (pow_ne_zero _ hp0) hcA (hint0 l) (hres0 l) hpole
  rw [he1, zpow_one] at hb
  have hmodval : ((Δ.annOut e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    rw [Δ.modulus_eq' e, Δ.modulus_eq e]; push_cast; rfl
  rw [hmodval, map_pow, map_pow, jWidth_of_ne (hw1 e).1 (hw1 e).2, pow_one] at hb
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0

  have : μ (p : AlgebraicClosure ℚ) ^ 1 ≤ μ (p : AlgebraicClosure ℚ) ^ n := by rwa [pow_one]
  exact (pow_le_pow_iff_right_of_lt_one₀ hμp0 hμp).mp this

end OrthZ1

end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "embDegree embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff ssJSet PlaceSpecialization.LevelOneProlongationPair jqModC modularFunctionFieldC jqModC_mem modularFunctionFieldC_one PlaceSpecialization ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed_coeff CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar cuspZeroBar_def jWidth jWidth_of_ne jWidth_eq_ite jWidth_pos jWidth_eq_one_or hasPrincipalDivisors_modularFunctionFieldBar_unconditional coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem ssJSet_nonempty ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar ComponentChart.exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar CharPReduction.modularRedLocHom_eq_coeffRed ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap isRational_place_modularFunctionFieldC_one zero_mem_ssJSet_iff exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord ord_charLGeomPlaceEquiv_placeInfty_jqModC MultCovering.mem_zeroChart_nodes_iff ofNat1728_mem_ssJSet_iff"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "FamData zeroSeries coe_frickeInvolutionBar_t hasseContent hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily jBar mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue ssValue_mem_ssJSet ssValue_injective exists_ssValue_eq nodeSrc nodeTgt AnnCtx cuspZeroBar_not_mem_infChart_dom infChart_nodeData_exists_node_of_member infChart_goodFamily_residue_ne_zero eq_mAnnuli_add_one_of_isEmbBasis mem_zeroChart_nodes_iff"
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"
section ContentTwo

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair Polynomial

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

theorem ssPolyBar_eq_aeval :
    ssPolyBar Γ = aeval (jBar (ResidueField ↥A)) (∏ e : Fin (mAnnuli p), (X - C (ssValue Γ e))) := by
  rw [ssPolyBar, map_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [map_sub, aeval_X, aeval_C]

theorem rootMultiplicity_prod_X_sub_C (e : Fin (mAnnuli p)) :
    (∏ e' : Fin (mAnnuli p), (X - C (ssValue Γ e'))).rootMultiplicity (ssValue Γ e) = 1 := by
  classical
  have hne : (∏ e' : Fin (mAnnuli p), (X - C (ssValue Γ e'))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e' _ => X_sub_C_ne_zero _
  rw [← Polynomial.count_roots, Polynomial.roots_prod _ _ hne]
  simp only [Polynomial.roots_X_sub_C, Multiset.count_bind, Multiset.count_singleton]
  rw [show (Finset.univ.val.map fun e' : Fin (mAnnuli p) => if ssValue Γ e = ssValue Γ e' then 1 else 0).sum
      = ∑ e' : Fin (mAnnuli p), (if ssValue Γ e = ssValue Γ e' then 1 else 0) from rfl]
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ hne'
    rw [if_neg]
    exact fun h => hne' ((ssValue_injective Γ) h).symm
  · simp

include hA Δ in

theorem hasseExp_le_jWidth_mul (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hint : ∀ l, Φ.t l ∈ (infChart Γ).integers)
    (P : Polynomial (ResidueField ↥A)) (hP0 : P ≠ 0)
    (hres : (infChart Γ).residue ⟨Φ.t l, hint l⟩ = ssPolyBar Γ * aeval (jBar (ResidueField ↥A)) P)
    (e : Fin (mAnnuli p)) :
    hasseExp Φ.toFamData l ≤ jWidth (ssValue Γ e) * (1 + P.rootMultiplicity (ssValue Γ e)) := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  obtain ⟨hb, -⟩ := twoEnd_bounds p A hA Γ Δ Φ μ hμp hμA hint2 hres_ne hint0 hres0 e l
  have hord : (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l, hint2 l⟩) = 1 + P.rootMultiplicity (ssValue Γ e) := by
    have e1 : (infChart Γ).residue ⟨goodFamily Φ l, hint2 l⟩ = ssPolyBar Γ * aeval (jBar (ResidueField ↥A)) P := hres
    rw [e1, ssPolyBar_eq_aeval, ← map_mul]
    have hne : (∏ e' : Fin (mAnnuli p), (X - C (ssValue Γ e'))) * P ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun e' _ => X_sub_C_ne_zero _) hP0
    rw [show nodeTgt Γ e = charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e) from rfl,
      show (jBar (ResidueField ↥A)) = P2MF2J.jB (ResidueField ↥A) from rfl,
      P2MF2J.ord_charLGeomPlaceOfPoint_aeval _ _ _ hne, Polynomial.rootMultiplicity_mul hne,
      rootMultiplicity_prod_X_sub_C]
    push_cast
    ring
  rw [hord] at hb
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have h1 : μ (p : AlgebraicClosure ℚ) ^ (((jWidth (ssValue Γ e) * (1 + P.rootMultiplicity (ssValue Γ e)) : ℕ) : ℤ))
      ≤ μ (p : AlgebraicClosure ℚ) ^ ((hasseExp Φ.toFamData l : ℕ) : ℤ) := by
    rw [zpow_natCast, zpow_natCast, pow_mul]
    have : (μ (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e)) ^ ((1 : ℤ) + (P.rootMultiplicity (ssValue Γ e) : ℤ))
        = (μ (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e)) ^ (1 + P.rootMultiplicity (ssValue Γ e)) := by
      rw [← zpow_natCast]; push_cast; rfl
    rw [← this]; exact hb
  have h2 := (zpow_le_zpow_iff_right_of_lt_one₀ hμp0 hμp).mp h1
  exact_mod_cast h2

include hA Δ in

theorem hasseExp_le_two_of_thirteen_le' (hp13 : 13 ≤ p) : ∀ l : Fin r, hasseExp Φ.toFamData l ≤ 2 := by
  classical
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  intro l
  by_cases hl0 : (l : ℕ) = 0
  · rw [hasseExp_zero p Φ l hl0]; omega
  have hl : 1 ≤ (l : ℕ) := by omega
  by_contra h3
  push_neg at h3
  obtain ⟨hint, -, P, hP, hLI, -⟩ := Φ.t_inf A hA Γ
  obtain ⟨hdeg, hres⟩ := hP l hl
  have hP0 : P l ≠ 0 := hLI.ne_zero ⟨l, hl⟩
  have hmult : ∀ e : Fin (mAnnuli p), 3 ≤ jWidth (ssValue Γ e) + (P l).rootMultiplicity (ssValue Γ e) := by
    intro e
    have hb := hasseExp_le_jWidth_mul p A hA Γ Δ Φ l hl hint (P l) hP0 hres e
    have hw := jWidth_eq_one_or (ssValue Γ e)
    rcases hw with hw | hw | hw <;> rw [hw] at hb ⊢ <;> omega
  have hsum_mult : ∑ e : Fin (mAnnuli p), (P l).rootMultiplicity (ssValue Γ e) ≤ (P l).natDegree := by
    calc ∑ e : Fin (mAnnuli p), (P l).rootMultiplicity (ssValue Γ e)
        = ∑ a ∈ Finset.univ.image (ssValue Γ), (P l).rootMultiplicity a := by
          rw [Finset.sum_image (fun x _ y _ h => ssValue_injective Γ h)]
      _ = ∑ a ∈ Finset.univ.image (ssValue Γ), (P l).roots.count a := by
          refine Finset.sum_congr rfl fun a _ => ?_; rw [Polynomial.count_roots]
      _ = ∑ a ∈ (Finset.univ.image (ssValue Γ)).filter (· ∈ (P l).roots.toFinset), (P l).roots.count a := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun a _ => ?_
          split_ifs with h
          · rfl
          · exact Multiset.count_eq_zero_of_notMem (fun hm => h (Multiset.mem_toFinset.mpr hm))
      _ ≤ ∑ a ∈ (P l).roots.toFinset, (P l).roots.count a :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun a ha => (Finset.mem_filter.mp ha).2) (fun _ _ _ => Nat.zero_le _)
      _ = (P l).roots.card := Multiset.toFinset_sum_count_eq _
      _ ≤ (P l).natDegree := Polynomial.card_roots' _
  set m := mAnnuli p with hm
  have hcount0 : (Finset.univ.filter fun e : Fin (mAnnuli p) => ssValue Γ e = 0).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => ssValue_injective Γ
      ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have hcount1728 : (Finset.univ.filter fun e : Fin (mAnnuli p) => ssValue Γ e = 1728).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => ssValue_injective Γ
      ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have hwle : ∀ e : Fin (mAnnuli p), jWidth (ssValue Γ e)
      ≤ 1 + 2 * (if ssValue Γ e = 0 then 1 else 0) + (if ssValue Γ e = 1728 then 1 else 0) := by
    intro e
    rw [jWidth_eq_ite]
    split_ifs <;> omega
  have hsumw : ∑ e : Fin (mAnnuli p), jWidth (ssValue Γ e) ≤ m + 3 := by
    have h1 : ∑ e : Fin (mAnnuli p), jWidth (ssValue Γ e)
        ≤ ∑ e : Fin (mAnnuli p), (1 + 2 * (if ssValue Γ e = 0 then 1 else 0) + (if ssValue Γ e = 1728 then 1 else 0)) :=
      Finset.sum_le_sum fun e _ => hwle e
    have h2 : ∑ e : Fin (mAnnuli p), (1 + 2 * (if ssValue Γ e = 0 then 1 else 0) + (if ssValue Γ e = 1728 then 1 else 0))
        = m + 2 * (Finset.univ.filter fun e : Fin (mAnnuli p) => ssValue Γ e = 0).card
          + (Finset.univ.filter fun e : Fin (mAnnuli p) => ssValue Γ e = 1728).card := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole]
      simp [hm]
    omega
  have hsum3 : 3 * m ≤ ∑ e : Fin (mAnnuli p), (jWidth (ssValue Γ e) + (P l).rootMultiplicity (ssValue Γ e)) := by
    have : ∑ _e : Fin (mAnnuli p), (3 : ℕ) = 3 * m := by simp [hm, mul_comm]
    rw [← this]
    exact Finset.sum_le_sum fun e _ => hmult e
  rw [Finset.sum_add_distrib] at hsum3
  have hdeg' : (P l).natDegree + 1 ≤ m := hdeg
  have hm2 : m ≤ 2 := by omega
  have hsumw_ge : 2 * m + 1 ≤ ∑ e : Fin (mAnnuli p), jWidth (ssValue Γ e) := by omega
  have hex0 : ∃ e : Fin (mAnnuli p), ssValue Γ e = 0 := by
    by_contra hno
    push_neg at hno
    have hwle' : ∀ e : Fin (mAnnuli p), jWidth (ssValue Γ e) ≤ 1 + (if ssValue Γ e = 1728 then 1 else 0) := by
      intro e; rw [jWidth_eq_ite, if_neg (hno e)]; split_ifs <;> omega
    have h1 : ∑ e : Fin (mAnnuli p), jWidth (ssValue Γ e) ≤ ∑ e : Fin (mAnnuli p), (1 + (if ssValue Γ e = 1728 then 1 else 0)) :=
      Finset.sum_le_sum fun e _ => hwle' e
    have h2 : ∑ e : Fin (mAnnuli p), (1 + (if ssValue Γ e = 1728 then 1 else 0))
        = m + (Finset.univ.filter fun e : Fin (mAnnuli p) => ssValue Γ e = 1728).card := by
      rw [Finset.sum_add_distrib, Finset.sum_boole]; simp [hm]
    omega
  obtain ⟨e0, he0⟩ := hex0
  have h0mem : (0 : ResidueField ↥A) ∈ ssJSet p (ResidueField ↥A) := he0 ▸ ssValue_mem_ssJSet Γ e0
  have hp5 : 5 ≤ p := le_trans (by norm_num) hp13
  have hp3 : p % 3 = 2 := (ModularCurve.zero_mem_ssJSet_iff p hp5 (ResidueField ↥A)).mp h0mem
  have hdiv : 1 ≤ p / 12 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hmform : m = p / 12 + (if p % 3 = 2 then 1 else 0) + (if p % 4 = 3 then 1 else 0) := by rw [hm]; rfl
  rw [if_pos hp3] at hmform
  have hex1728 : ∃ e : Fin (mAnnuli p), ssValue Γ e = 1728 := by
    by_contra hno
    push_neg at hno
    have hwle' : ∀ e : Fin (mAnnuli p), jWidth (ssValue Γ e) ≤ 1 + 2 * (if ssValue Γ e = 0 then 1 else 0) := by
      intro e; rw [jWidth_eq_ite]
      by_cases h1 : ssValue Γ e = 0
      · rw [if_pos h1, if_pos h1]
      · rw [if_neg h1, if_neg h1, if_neg (hno e)]
    have h1 : ∑ e : Fin (mAnnuli p), jWidth (ssValue Γ e) ≤ ∑ e : Fin (mAnnuli p), (1 + 2 * (if ssValue Γ e = 0 then 1 else 0)) :=
      Finset.sum_le_sum fun e _ => hwle' e
    have h2 : ∑ e : Fin (mAnnuli p), (1 + 2 * (if ssValue Γ e = 0 then 1 else 0))
        = m + 2 * (Finset.univ.filter fun e : Fin (mAnnuli p) => ssValue Γ e = 0).card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole]; simp [hm]
    split_ifs at hmform <;> omega
  obtain ⟨e1, he1⟩ := hex1728
  have h1728mem : (1728 : ResidueField ↥A) ∈ ssJSet p (ResidueField ↥A) := he1 ▸ ssValue_mem_ssJSet Γ e1
  have hp4 : p % 4 = 3 := (ModularCurve.ofNat1728_mem_ssJSet_iff p hp5 (ResidueField ↥A)).mp h1728mem
  rw [if_pos hp4] at hmform
  omega

end ContentTwo
end ModularCurve.MultCovering

namespace ModularCurve
p2m_export "ModularCurve" "embDegree embDivisor IsEmbBasis frickeInvolutionFull cuspInftyBar modularFunctionFieldFull modularFunctionFieldBar algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff ssJSet PlaceSpecialization.LevelOneProlongationPair jqModC modularFunctionFieldC jqModC_mem modularFunctionFieldC_one PlaceSpecialization ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed_coeff CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar cuspZeroBar_def jWidth jWidth_of_ne jWidth_eq_ite jWidth_pos jWidth_eq_one_or hasPrincipalDivisors_modularFunctionFieldBar_unconditional coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem ssJSet_nonempty ComponentChart.residue_frickeInvolutionBar_eq_zero_of_hasValue_zero_of_forall_pole_eq_cuspInftyBar exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar ComponentChart.exists_residue_frickeInvolutionBar_eq_algebraMap_of_forall_pole_eq_cuspInftyBar CharPReduction.modularRedLocHom_eq_coeffRed ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap isRational_place_modularFunctionFieldC_one zero_mem_ssJSet_iff exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord ord_charLGeomPlaceEquiv_placeInfty_jqModC MultCovering.mem_zeroChart_nodes_iff ofNat1728_mem_ssJSet_iff"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "FamData zeroSeries coe_frickeInvolutionBar_t hasseContent hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily jBar mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart ssValue ssValue_mem_ssJSet ssValue_injective exists_ssValue_eq nodeSrc nodeTgt AnnCtx cuspZeroBar_not_mem_infChart_dom infChart_nodeData_exists_node_of_member infChart_goodFamily_residue_ne_zero eq_mAnnuli_add_one_of_isEmbBasis mem_zeroChart_nodes_iff"
p2m_open "ModularCurve.MultCovering ModularCurve~jBar"
section SpanWidthOne

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair Polynomial

variable (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)

include hA Δ in

theorem hasseExp_add_jWidth_mul_ord_nonneg (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (e : Fin (mAnnuli p)) (l : Fin r) :
    0 ≤ (hasseExp Φ.toFamData l : ℤ) + (jWidth (ssValue Γ e) : ℤ)
      * (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨μ, -, hμp, hμA⟩ :=
    ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime (Fact.out : p.Prime) A hA
  obtain ⟨hint2, hres_ne⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hint0, hres0⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  obtain ⟨-, hb'⟩ := twoEnd_bounds p A hA Γ Δ Φ μ hμp hμA hint2 hres_ne hint0 hres0 e l
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  set n := hasseExp Φ.toFamData l
  set w := jWidth (ssValue Γ e)
  set a' := (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint0 l⟩) with ha'
  have hz : μ (p : AlgebraicClosure ℚ) ^ ((n : ℤ) + (w : ℤ) * a') ≤ 1 := by
    rw [zpow_add₀ hμp0.ne', zpow_mul, zpow_natCast, zpow_natCast]; exact hb'
  exact (zpow_le_one_iff_right_of_lt_one₀ hμp0 hμp).mp hz

theorem ssValue_pow_injective' :
    Function.Injective fun e : Fin (mAnnuli p) => ssValue Γ e ^ p := by
  intro e e' h
  apply ssValue_injective Γ
  exact frobenius_inj (ResidueField ↥A) p h

include hA Δ in

theorem mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge' (hp5 : 5 ≤ p)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (f : ↥(modularFunctionFieldC (ResidueField ↥A) 1))
    (hreg : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord f)
    (hnode : ∀ e : Fin (mAnnuli p), -((1 / jWidth (ssValue Γ e) : ℕ) : ℤ) ≤ (nodeSrc Γ e).ord f) :
    f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : DecidableEq (RatFunc (ResidueField ↥A)) := Classical.decEq _
  set res₀ : Fin r → ↥(modularFunctionFieldC (ResidueField ↥A) 1) :=
    fun l => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩ with hres₀
  set jB : ↥(modularFunctionFieldC (ResidueField ↥A) 1) := ⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) 1⟩ with hjB

  set S : Finset (Fin (mAnnuli p)) := Finset.univ.filter (fun e => jWidth (ssValue Γ e) = 1) with hS
  set S₀ : Finset (ResidueField ↥A) := S.image (fun e => ssValue Γ e ^ p) with hS₀
  have hS₀card : S₀.card = S.card :=
    Finset.card_image_of_injective _ (ssValue_pow_injective' p A Γ)
  have hmemS₀ : ∀ {b : ResidueField ↥A}, b ∈ S₀ ↔ ∃ e, jWidth (ssValue Γ e) = 1 ∧ ssValue Γ e ^ p = b := by
    intro b
    simp only [hS₀, hS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

  have hnodes : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1), v ∈ (zeroChart Γ).nodes ↔ ∃ e, charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e ^ p) = v := by
    intro v
    rw [ModularCurve.MultCovering.mem_zeroChart_nodes_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨e, he⟩ := exists_ssValue_eq Γ a ha
      exact ⟨e, by rw [he]⟩
    · rintro ⟨e, rfl⟩
      exact ⟨ssValue Γ e, ssValue_mem_ssJSet Γ e, rfl⟩
  have hnodeSrc : ∀ e, nodeSrc Γ e = charLGeomPlaceOfPoint (ResidueField ↥A) (ssValue Γ e ^ p) := fun e => rfl

  have hinf_not : charLGeomPlaceEquiv (ResidueField ↥A) (RationalFunctionField.placeInfty (ResidueField ↥A)) ∉ (zeroChart Γ).nodes := by
    intro hmem
    obtain ⟨e, he⟩ := (hnodes _).mp hmem
    have h1 := ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_jqModC (ResidueField ↥A)
    have h2 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap (ResidueField ↥A) (ssValue Γ e ^ p) 0
    rw [map_zero, sub_zero, he] at h2
    rw [h2] at h1
    split_ifs at h1 <;> omega

  have hpres : ∀ g : ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      (∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1), v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord g) →
      (∀ e : Fin (mAnnuli p), -((1 / jWidth (ssValue Γ e) : ℕ) : ℤ) ≤ (nodeSrc Γ e).ord g) →
      ∃ Q : Polynomial (ResidueField ↥A), Q ∈ Polynomial.degreeLT (ResidueField ↥A) (S₀.card + 1) ∧
        (∏ a ∈ S₀, (jB - algebraMap (ResidueField ↥A) _ a)) * g = Polynomial.aeval jB Q := by
    intro g hg hgn
    have hreg' : ∀ b : (ResidueField ↥A), b ∉ S₀ → 0 ≤ (charLGeomPlaceOfPoint (ResidueField ↥A) b).ord g := by
      intro b hb
      by_cases hbn : charLGeomPlaceOfPoint (ResidueField ↥A) b ∈ (zeroChart Γ).nodes
      · obtain ⟨e, he⟩ := (hnodes _).mp hbn
        have hw : jWidth (ssValue Γ e) ≠ 1 := by
          intro hw; exact hb (hmemS₀.mpr ⟨e, hw, by
            have := congrArg (fun v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) => v) he
            exact charLGeomPlaceOfPoint_injective (ResidueField ↥A) (by simpa using he)⟩)
        have := hgn e
        rw [hnodeSrc, he] at this
        have hdiv : (1 / jWidth (ssValue Γ e) : ℕ) = 0 := by
          rcases jWidth_eq_one_or (ssValue Γ e) with h | h | h
          · exact absurd h hw
          · rw [h]
          · rw [h]
        rw [hdiv] at this
        simpa using this
      · exact hg _ hbn
    have hS₀' : ∀ a ∈ S₀, -1 ≤ (charLGeomPlaceOfPoint (ResidueField ↥A) a).ord g := by
      intro a ha
      obtain ⟨e, hw, rfl⟩ := hmemS₀.mp ha
      have := hgn e
      rw [hw, hnodeSrc] at this
      simpa using this
    have hinf' : -((0 : ℕ) : ℤ) ≤ (charLGeomPlaceEquiv (ResidueField ↥A) (RationalFunctionField.placeInfty (ResidueField ↥A))).ord g := by
      simpa using hg _ hinf_not
    obtain ⟨Q, hQdeg, hQ⟩ := ModularCurve.exists_prod_mul_eq_aeval_of_forall_ord_nonneg_of_forall_neg_one_le_ord
      S₀ 0 g hreg' hS₀' hinf'
    refine ⟨Q, ?_, hQ⟩
    rw [Polynomial.mem_degreeLT]
    by_cases hQ0 : Q = 0
    · rw [hQ0, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · have := hQdeg hQ0
      rw [zero_add] at this
      exact lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le this)

  set T : Finset (Fin r) := Finset.univ.filter (fun l => hasseExp Φ.toFamData l ≤ 1) with hT
  have hT_reg : ∀ l ∈ T, ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1), v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord (res₀ l) := by
    intro l _ v hv
    obtain ⟨hint', hz3⟩ := zeroChart_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes p A hA Γ Φ
    exact hz3 l v hv
  have hT_node : ∀ l ∈ T, ∀ e : Fin (mAnnuli p), -((1 / jWidth (ssValue Γ e) : ℕ) : ℤ) ≤ (nodeSrc Γ e).ord (res₀ l) := by
    intro l hl e
    have hn : hasseExp Φ.toFamData l ≤ 1 := (Finset.mem_filter.mp hl).2
    have hb := hasseExp_add_jWidth_mul_ord_nonneg p A hA Γ Δ Φ hint e l
    have hw1 : 1 ≤ jWidth (ssValue Γ e) := jWidth_pos (ssValue Γ e)
    set w := jWidth (ssValue Γ e) with hw
    set a' := (nodeSrc Γ e).ord (res₀ l)
    change 0 ≤ (hasseExp Φ.toFamData l : ℤ) + (w : ℤ) * a' at hb
    rcases jWidth_eq_one_or (ssValue Γ e) with h | h | h <;> rw [← hw] at h <;> rw [h] at hb ⊢ <;> push_cast <;> omega
  choose Qf hQf_mem hQf using hpres f hreg hnode
  have hQT : ∀ l : T, ∃ Q : Polynomial (ResidueField ↥A), Q ∈ Polynomial.degreeLT (ResidueField ↥A) (S₀.card + 1) ∧
      (∏ a ∈ S₀, (jB - algebraMap (ResidueField ↥A) _ a)) * res₀ l = Polynomial.aeval jB Q :=
    fun l => hpres (res₀ l) (hT_reg l l.2) (hT_node l l.2)
  choose QT hQT_mem hQT_eq using hQT

  have hr : r = mAnnuli p + 1 := eq_mAnnuli_add_one_of_isEmbBasis p hp5 Φ.t Φ.t_basis
  have hTcard : S.card + 1 ≤ T.card := by

    obtain ⟨hintI, -, P, hP, hPLI, -⟩ := Φ.t_inf A hA Γ
    set Tc : Finset (Fin r) := Finset.univ.filter (fun l => 2 ≤ hasseExp Φ.toFamData l) with hTc
    have hTc1 : ∀ l ∈ Tc, 1 ≤ (l : ℕ) := by
      intro l hl
      by_contra h0
      push_neg at h0
      have : hasseExp Φ.toFamData l = 0 := hasseExp_zero p Φ l (by omega)
      have h2 := (Finset.mem_filter.mp hl).2
      omega
    set DS : Polynomial (ResidueField ↥A) := ∏ e ∈ S, (X - C (ssValue Γ e)) with hDS
    have hDS0 : DS ≠ 0 := Finset.prod_ne_zero_iff.mpr fun e _ => X_sub_C_ne_zero _
    have hdvd : ∀ l ∈ Tc, DS ∣ P l := by
      intro l hl
      apply Finset.prod_dvd_of_coprime
      · intro e _ e' _ hne
        exact (Polynomial.pairwise_coprime_X_sub_C (ssValue_injective Γ)) hne
      · intro e he
        have hw : jWidth (ssValue Γ e) = 1 := (Finset.mem_filter.mp he).2
        have hP0 : P l ≠ 0 := hPLI.ne_zero ⟨l, hTc1 l hl⟩
        have hb := hasseExp_le_jWidth_mul p A hA Γ Δ Φ l (hTc1 l hl) hintI (P l) hP0 (hP l (hTc1 l hl)).2 e
        rw [hw, one_mul] at hb
        have h2 := (Finset.mem_filter.mp hl).2
        have hmult : 1 ≤ (P l).rootMultiplicity (ssValue Γ e) := by omega
        have := (Polynomial.le_rootMultiplicity_iff hP0).mp hmult
        simpa using this

    have hR : ∀ l : Tc, ∃ R : Polynomial (ResidueField ↥A), P l = DS * R := fun l => hdvd l l.2
    choose R hRl using hR
    have hRdeg : ∀ l : Tc, R l ∈ Polynomial.degreeLT (ResidueField ↥A) (mAnnuli p - S.card) := by
      intro l
      rw [Polynomial.mem_degreeLT]
      have hP0 : P l ≠ 0 := hPLI.ne_zero ⟨l, hTc1 l l.2⟩
      have hR0 : R l ≠ 0 := by intro h; apply hP0; rw [hRl l, h, mul_zero]
      have hdegP := (hP l (hTc1 l l.2)).1
      have hdegDS : DS.natDegree = S.card := by
        rw [hDS, Polynomial.natDegree_prod _ _ (fun e _ => X_sub_C_ne_zero _)]
        simp
      have : (P (l : Fin r)).natDegree = DS.natDegree + (R l).natDegree := by
        rw [hRl l, Polynomial.natDegree_mul hDS0 hR0]
      rw [Polynomial.degree_eq_natDegree hR0]
      exact_mod_cast (by omega : (R l).natDegree < mAnnuli p - S.card)
    have hRLI : LinearIndependent (ResidueField ↥A) (fun l : Tc => (⟨R l, hRdeg l⟩ : Polynomial.degreeLT (ResidueField ↥A) (mAnnuli p - S.card))) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg l

      have hg' : ∑ i : Tc, g i • R i = 0 := by
        have := congrArg (Subtype.val) hg
        simpa using this
      have hgP : ∑ i : Tc, g i • P (i : Fin r) = 0 := by
        have : ∑ i : Tc, g i • P (i : Fin r) = DS * ∑ i : Tc, g i • R i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hRl i, smul_eq_C_mul, smul_eq_C_mul]; ring
        rw [this, hg', mul_zero]

      have hinj : Function.Injective (fun i : Tc => (⟨(i : Fin r), hTc1 i i.2⟩ : {l : Fin r // 1 ≤ (l : ℕ)})) := by
        intro i j h; apply Subtype.ext; exact congrArg (fun x : {l : Fin r // 1 ≤ (l : ℕ)} => (x : Fin r)) h
      have hPLI' := hPLI.comp _ hinj
      exact (Fintype.linearIndependent_iff.mp hPLI') g (by simpa using hgP) l
    have hTc_le : Tc.card ≤ mAnnuli p - S.card := by
      have := hRLI.fintype_card_le_finrank
      rw [Fintype.card_coe] at this
      have hfin : Module.finrank (ResidueField ↥A) (Polynomial.degreeLT (ResidueField ↥A) (mAnnuli p - S.card)) = mAnnuli p - S.card := by
        rw [LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv (ResidueField ↥A) (mAnnuli p - S.card)), Module.finrank_fin_fun]
      rw [hfin] at this
      exact this

    have hpart : T.card + Tc.card = r := by
      have : Tc = Tᶜ := by
        ext l; simp [hT, hTc, Finset.mem_compl]; omega
      rw [this, Finset.card_add_card_compl, Fintype.card_fin]
    have hSm : S.card ≤ mAnnuli p := by
      calc S.card ≤ (Finset.univ : Finset (Fin (mAnnuli p))).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = mAnnuli p := by simp
    omega

  set vec : Option T → Polynomial.degreeLT (ResidueField ↥A) (S₀.card + 1) := fun o =>
    Option.elim o ⟨Qf, hQf_mem⟩ (fun l => ⟨QT l, hQT_mem l⟩) with hvec
  have hdep : ¬ LinearIndependent (ResidueField ↥A) vec := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_option, Fintype.card_coe,
      LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv (ResidueField ↥A) (S₀.card + 1)), Module.finrank_fin_fun, hS₀card] at this
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i₀, hi₀⟩ := hdep

  set D : ↥(modularFunctionFieldC (ResidueField ↥A) 1) := ∏ a ∈ S₀, (jB - algebraMap (ResidueField ↥A) _ a) with hD
  have hD0 : D ≠ 0 := by
    rw [hD]
    refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
    intro h0
    have h1 := ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap (ResidueField ↥A) a a
    rw [if_pos rfl] at h1
    change (charLGeomPlaceOfPoint (ResidueField ↥A) a).ord (jB - algebraMap (ResidueField ↥A) _ a) = 1 at h1
    rw [h0, Place.ord_zero] at h1
    exact zero_ne_one h1
  have hsum : g none • f + ∑ l : T, g (some l) • res₀ l = 0 := by
    have e1 : ∑ o : Option T, g o • (Polynomial.aeval jB ((vec o : Polynomial.degreeLT (ResidueField ↥A) (S₀.card + 1)) : Polynomial (ResidueField ↥A))) = 0 := by
      have h1 := congrArg (fun x : Polynomial.degreeLT (ResidueField ↥A) (S₀.card + 1) => Polynomial.aeval jB (x : Polynomial (ResidueField ↥A))) hg
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, ZeroMemClass.coe_zero, map_zero] at h1
      exact h1
    rw [Fintype.sum_option] at e1
    simp only [hvec, Option.elim] at e1
    rw [← hQf] at e1
    have e2 : ∀ l : T, g (some l) • Polynomial.aeval jB (QT l) = D * (g (some l) • res₀ l) := by
      intro l; rw [← hQT_eq l, mul_smul_comm]
    simp only [e2] at e1
    rw [← mul_smul_comm, ← Finset.mul_sum, ← mul_add] at e1
    exact (mul_eq_zero.mp e1).resolve_left hD0

  have hg0 : g none ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hsum
    have hLI' := hLI.comp (fun l : T => (l : Fin r)) Subtype.val_injective
    have hall := (Fintype.linearIndependent_iff.mp hLI') (fun l => g (some l)) hsum
    cases i₀ with
    | none => exact hi₀ h0
    | some l => exact hi₀ (hall l)
  have hf : f = (g none)⁻¹ • (-(∑ l : T, g (some l) • res₀ l)) := by
    have : g none • f = -(∑ l : T, g (some l) • res₀ l) := eq_neg_of_add_eq_zero_left hsum
    rw [← this, smul_smul, inv_mul_cancel₀ hg0, one_smul]
  rw [hf]
  refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.sum_mem _ fun l _ => ?_))
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(l : Fin r), rfl⟩)

end SpanWidthOne
end ModularCurve.MultCovering

open AlgebraicCurve IsLocalRing _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_MultCovering_mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge.ModularCurve.MultCovering in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (f : ↥(modularFunctionFieldC (ResidueField ↥A) 1))
    (hreg : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1),
      v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord f)
    (hnode : ∀ e : Fin (mAnnuli p), -((1 / jWidth (ssValue Γ e) : ℕ) : ℤ) ≤ (nodeSrc Γ e).ord f) :
    f ∈ Submodule.span (ResidueField ↥A)
        (Set.range fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) :=
  ModularCurve.MultCovering.mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge' p A hA Γ Δ Φ hp5 hint hLI f hreg hnode

end S_ModularCurve_MultCovering_mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge
end P2MW
export P2MW.S_ModularCurve_MultCovering_mem_span_zeroChart_residue_of_forall_ord_nodeSrc_ge (solution)
