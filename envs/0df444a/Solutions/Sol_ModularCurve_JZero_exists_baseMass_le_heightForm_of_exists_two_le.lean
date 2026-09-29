-- Prove2me | solution 1 for ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/536a9a25-cfef-5d8a-bb5e-313b088e3d9c

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Theorems.Thm_ModularCurve_JZero_heightForm_sub_baseMass_eq
import Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_sub_canonicalDivisorOf_forall_ne_not_and
import Theorems.Thm_AlgebraicCurve_det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix
import Theorems.Thm_ModularCurve_infinite_place_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_exists_ord_sub_evalAt_eq_one
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_self
import Theorems.Thm_ModularCurve_JZero_sum_pairHt_le_of_isUnit_det_jetMatrix
import Theorems.Thm_ModularCurve_JZero_exists_absLogHeight_regVal_sub_two_mul_pointHt_le
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_isCusp_cuspInftyBar
import Theorems.Thm_ModularCurve_isCusp_iff_ord_neg
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_JZero_finrank_riemannRochSpace_canonicalDivisorOf_sub_erase_add_offBaseMass
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_ModularCurve_JZero_jensen_good_at_le
import Theorems.Thm_ModularCurve_JZero_jensen_bad_at_le
import Theorems.Thm_ModularCurve_JZero_jensen_arch_at_le_of_nonCuspidal
import Theorems.Thm_ModularCurve_JZero_exists_pointHt_le_mul_baseHt
import Theorems.Thm_ModularCurve_JZero_exists_sub_mul_baseHt_le_pairHt
import Theorems.Thm_AlgebraicCurve_exists_forall_neg_le_pairHt
import Theorems.Thm_AlgebraicCurve_exists_forall_neg_le_baseHt
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_ModularCurve_exists_injective_riemannRochSpace_canonicalDivisorOf_sub_eq_bot
import Theorems.Thm_AlgebraicCurve_isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_pairHt_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.chowForm_zero AlgebraicCurve.secProd_zero ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one MvPolynomial.logMahlerMeasure_C"
p2m_attr_erase "simp" "MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox"

set_option autoImplicit false
set_option maxHeartbeats 4000000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.AlgebraicCurve ModularCurve KaehlerDifferential"

section ConfGlueSec
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.AlgebraicCurve ModularCurve Finset"

namespace ConfGlue

section Shift
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mul_mem_riemannRochSpace_iff (D : Divisor K F) {h : F} (hh : h ≠ 0)
    (Dh : Divisor K F) (hDh : ∀ w, Dh w = w.ord h) (x : F) :
    x * h ∈ riemannRochSpace D ↔ x ∈ riemannRochSpace (D + Dh) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp
  · rw [mem_riemannRochSpace_iff, mem_riemannRochSpace_iff]
    refine forall_congr' fun v => ?_
    rw [Place.ord_mul _ hx hh, ← hDh]
    simp only [mul_ne_zero hx hh, hx, false_or, Finsupp.coe_add, Pi.add_apply]
    constructor <;> intro hv <;> linarith

noncomputable def mulEquiv (D : Divisor K F) {h : F} (hh : h ≠ 0)
    (Dh : Divisor K F) (hDh : ∀ w, Dh w = w.ord h) :
    ↥(riemannRochSpace (D + Dh)) ≃ₗ[K] ↥(riemannRochSpace D) where
  toFun x := ⟨(x : F) * h, (mul_mem_riemannRochSpace_iff D hh Dh hDh x).mpr x.2⟩
  invFun y := ⟨(y : F) * h⁻¹, (mul_mem_riemannRochSpace_iff D hh Dh hDh _).mp (by
    rw [inv_mul_cancel_right₀ hh]; exact y.2)⟩
  left_inv x := by ext; simp [mul_inv_cancel_right₀ hh]
  right_inv y := by ext; simp [inv_mul_cancel_right₀ hh]
  map_add' x y := by ext; simp [add_mul]
  map_smul' c x := by ext; simp

theorem finrank_riemannRochSpace_add_eq (D : Divisor K F) {h : F} (hh : h ≠ 0)
    (Dh : Divisor K F) (hDh : ∀ w, Dh w = w.ord h) :
    Module.finrank K ↥(riemannRochSpace (D + Dh)) = Module.finrank K ↥(riemannRochSpace D) :=
  LinearEquiv.finrank_eq (mulEquiv D hh Dh hDh)

theorem riemannRochSpace_eq_bot_iff_of_ord (D₁ : Divisor K F) {h : F} (hh : h ≠ 0)
    (Dh : Divisor K F) (hDh : ∀ w, Dh w = w.ord h) :
    riemannRochSpace D₁ = ⊥ ↔ riemannRochSpace (D₁ + Dh) = ⊥ := by
  constructor
  · intro h0
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hxh : x * h ∈ riemannRochSpace D₁ := (mul_mem_riemannRochSpace_iff D₁ hh Dh hDh x).mpr hx
    have hx0 : x * h = 0 := (Submodule.eq_bot_iff _).mp h0 _ hxh
    exact (mul_eq_zero.mp hx0).resolve_right hh
  · intro h0
    rw [Submodule.eq_bot_iff]
    intro y hy
    have hyh : y * h⁻¹ ∈ riemannRochSpace (D₁ + Dh) :=
      (mul_mem_riemannRochSpace_iff D₁ hh Dh hDh _).mp (by rw [inv_mul_cancel_right₀ hh]; exact hy)
    have hy0 : y * h⁻¹ = 0 := (Submodule.eq_bot_iff _).mp h0 _ hyh
    exact (mul_eq_zero.mp hy0).resolve_right (inv_ne_zero hh)

end Shift

section Split
variable {α : Type*} [DecidableEq α]

theorem finsupp_sum_split {M : Type*} [AddCommMonoid M] (D : α →₀ ℤ) (S : Finset α) (f : α → ℤ → M) :
    D.sum f = ∑ v ∈ D.support.filter (fun v => v ∉ S), f v (D v)
      + ∑ v ∈ D.support.filter (fun v => v ∈ S), f v (D v) := by
  rw [Finsupp.sum, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not D.support (fun v => v ∈ S) (fun v => f v (D v))).symm

theorem finsupp_sum_erase_sum_eq (D : α →₀ ℤ) (Φ : α → α → ℝ) :
    (D.sum fun v n => (D.erase v).sum fun w k => (n : ℝ) * (k : ℝ) * Φ v w)
      = ∑ v ∈ D.support, ∑ w ∈ D.support.erase v, (D v : ℝ) * (D w : ℝ) * Φ v w := by
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finsupp.support_erase]
  exact Finset.sum_congr rfl fun w hw => by rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hw)]

theorem sum_erase_split (T S : Finset α) (G : α → α → ℝ) :
    ∑ v ∈ T, ∑ w ∈ T.erase v, G v w
      = ∑ v ∈ T.filter (fun v => v ∉ S), ∑ w ∈ (T.filter (fun v => v ∉ S)).erase v, G v w
        + ∑ v ∈ T.filter (fun v => v ∉ S), ∑ w ∈ T.filter (fun v => v ∈ S), G v w
        + ∑ v ∈ T.filter (fun v => v ∈ S), ∑ w ∈ T.filter (fun v => v ∉ S), G v w
        + ∑ v ∈ T.filter (fun v => v ∈ S), ∑ w ∈ (T.filter (fun v => v ∈ S)).erase v, G v w := by
  set A := T.filter (fun v => v ∉ S) with hA
  set B := T.filter (fun v => v ∈ S) with hB
  have hsplit : ∀ φ : α → ℝ, ∑ w ∈ T, φ w = ∑ w ∈ A, φ w + ∑ w ∈ B, φ w := fun φ => by
    rw [add_comm]; exact (Finset.sum_filter_add_sum_filter_not T (fun v => v ∈ S) φ).symm
  have hinA : ∀ v ∈ A, ∑ w ∈ T.erase v, G v w = ∑ w ∈ A.erase v, G v w + ∑ w ∈ B, G v w := by
    intro v hv
    have hvT : v ∈ T := (Finset.mem_filter.mp hv).1
    rw [Finset.sum_erase_eq_sub hvT, hsplit, Finset.sum_erase_eq_sub hv]; ring
  have hinB : ∀ v ∈ B, ∑ w ∈ T.erase v, G v w = ∑ w ∈ A, G v w + ∑ w ∈ B.erase v, G v w := by
    intro v hv
    have hvT : v ∈ T := (Finset.mem_filter.mp hv).1
    rw [Finset.sum_erase_eq_sub hvT, hsplit, Finset.sum_erase_eq_sub hv]; ring
  rw [hsplit (fun v => ∑ w ∈ T.erase v, G v w), Finset.sum_congr rfl hinA, Finset.sum_congr rfl hinB,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

end Split

open Classical in

theorem exists_bound_cusp_parts (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) (g₀ : ℕ) (ε : ℝ) :
    ∃ Cc : ℝ, ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, 0 ≤ D v) → D (cuspInftyBar N) = 0 → JZero.offBaseMass N D ≤ g₀ →
      |∑ v ∈ D.support.filter (fun v => v ∈ S),
          ((((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
              + (JZero.offBaseMass N D : ℝ) - 2 + ε) * (D v : ℝ)
            + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
              * ((D v : ℝ) * ((D v : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)| ≤ Cc ∧
      |∑ v ∈ D.support.filter (fun v => v ∈ S), ∑ w ∈ (D.support.filter (fun v => v ∈ S)).erase v,
          (D v : ℝ) * (D w : ℝ) * pairHt s v w| ≤ Cc := by
  classical
  set g : ℝ := (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) with hg
  set CtS : ℝ := ∑ v ∈ S, |baseHt s (cuspInftyBar N) v| with hCtS
  set CbS : ℝ := ∑ v ∈ S, ∑ w ∈ S, |pairHt s v w| with hCbS
  set W : ℝ := (g + g₀ + 2 + |ε|) * g₀ + (2 * g + 2) * ((g₀ : ℝ) ^ 2) with hW
  have hg0 : 0 ≤ g := Nat.cast_nonneg _
  have hCtS0 : 0 ≤ CtS := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCbS0 : 0 ≤ CbS := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hW0 : 0 ≤ W := by positivity
  refine ⟨W * CtS + (g₀ : ℝ) ^ 2 * CbS, fun D hD hinf hm => ⟨?_, ?_⟩⟩
  ·
    have hm0 : (0 : ℝ) ≤ (JZero.offBaseMass N D : ℝ) := by
      have : (0 : ℤ) ≤ JZero.offBaseMass N D := by
        simp only [JZero.offBaseMass, Finsupp.sum]
        exact Finset.sum_nonneg fun v _ => by
          rw [Finsupp.erase_apply]; split_ifs
          · exact le_rfl
          · exact hD v
      exact_mod_cast this
    have hmg : (JZero.offBaseMass N D : ℝ) ≤ g₀ := by exact_mod_cast hm
    have hDv : ∀ v ∈ D.support.filter (fun v => v ∈ S), (0 : ℝ) ≤ D v ∧ (D v : ℝ) ≤ g₀ := by
      intro v hv
      have hvs : v ∈ D.support := (Finset.mem_filter.mp hv).1
      have hvi : v ≠ cuspInftyBar N := fun h0 => (Finsupp.mem_support_iff.mp hvs) (h0 ▸ hinf)
      refine ⟨by exact_mod_cast hD v, ?_⟩
      have h1 : D v ≤ JZero.offBaseMass N D := by
        simp only [JZero.offBaseMass, Finsupp.sum]
        have hmem : v ∈ (D.erase (cuspInftyBar N)).support := by
          rw [Finsupp.support_erase]; exact Finset.mem_erase.mpr ⟨hvi, hvs⟩
        have hnn : ∀ w ∈ (D.erase (cuspInftyBar N)).support, (0 : ℤ) ≤ (D.erase (cuspInftyBar N)) w :=
          fun w _ => by
            rw [Finsupp.erase_apply]; split_ifs
            · exact le_rfl
            · exact hD w
        have := Finset.single_le_sum hnn hmem
        simp only [Finsupp.erase_ne hvi] at this
        exact this
      have : (D v : ℝ) ≤ (JZero.offBaseMass N D : ℝ) := by exact_mod_cast h1
      linarith
    have hterm : ∀ v ∈ D.support.filter (fun v => v ∈ S),
        |(((g + (JZero.offBaseMass N D : ℝ) - 2 + ε) * (D v : ℝ)
            + (2 * g - 2) * ((D v : ℝ) * ((D v : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)|
          ≤ W * |baseHt s (cuspInftyBar N) v| := by
      intro v hv
      obtain ⟨h0, h1⟩ := hDv v hv
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have hn2 : (D v : ℝ) ^ 2 ≤ (g₀ : ℝ) ^ 2 := pow_le_pow_left₀ h0 h1 2
      rw [abs_le]
      constructor
      · nlinarith [abs_nonneg ε, neg_abs_le ε, le_abs_self ε, mul_nonneg h0 hm0, mul_nonneg h0 hg0]
      · nlinarith [abs_nonneg ε, neg_abs_le ε, le_abs_self ε, mul_nonneg h0 hm0, mul_nonneg h0 hg0]
    calc |∑ v ∈ D.support.filter (fun v => v ∈ S), _|
        ≤ ∑ v ∈ D.support.filter (fun v => v ∈ S),
            |(((g + (JZero.offBaseMass N D : ℝ) - 2 + ε) * (D v : ℝ)
              + (2 * g - 2) * ((D v : ℝ) * ((D v : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ D.support.filter (fun v => v ∈ S), W * |baseHt s (cuspInftyBar N) v| :=
          Finset.sum_le_sum hterm
      _ ≤ ∑ v ∈ S, W * |baseHt s (cuspInftyBar N) v| :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => (Finset.mem_filter.mp hv).2)
            (fun v _ _ => mul_nonneg hW0 (abs_nonneg _))
      _ = W * CtS := by rw [hCtS, Finset.mul_sum]
      _ ≤ W * CtS + (g₀ : ℝ) ^ 2 * CbS := by nlinarith
  · have hDv : ∀ v ∈ D.support.filter (fun v => v ∈ S), (0 : ℝ) ≤ D v ∧ (D v : ℝ) ≤ g₀ := by
      intro v hv
      have hvs : v ∈ D.support := (Finset.mem_filter.mp hv).1
      have hvi : v ≠ cuspInftyBar N := fun h0 => (Finsupp.mem_support_iff.mp hvs) (h0 ▸ hinf)
      refine ⟨by exact_mod_cast hD v, ?_⟩
      have h1 : D v ≤ JZero.offBaseMass N D := by
        simp only [JZero.offBaseMass, Finsupp.sum]
        have hmem : v ∈ (D.erase (cuspInftyBar N)).support := by
          rw [Finsupp.support_erase]; exact Finset.mem_erase.mpr ⟨hvi, hvs⟩
        have hnn : ∀ w ∈ (D.erase (cuspInftyBar N)).support, (0 : ℤ) ≤ (D.erase (cuspInftyBar N)) w :=
          fun w _ => by
            rw [Finsupp.erase_apply]; split_ifs
            · exact le_rfl
            · exact hD w
        have := Finset.single_le_sum hnn hmem
        simp only [Finsupp.erase_ne hvi] at this
        exact this
      have h2 : (D v : ℝ) ≤ (JZero.offBaseMass N D : ℝ) := by exact_mod_cast h1
      have h3 : (JZero.offBaseMass N D : ℝ) ≤ g₀ := by exact_mod_cast hm
      linarith
    have hpair : ∀ v ∈ D.support.filter (fun v => v ∈ S), ∀ w ∈ D.support.filter (fun v => v ∈ S),
        |(D v : ℝ) * (D w : ℝ) * pairHt s v w| ≤ (g₀ : ℝ) ^ 2 * |pairHt s v w| := by
      intro v hv w hw
      obtain ⟨hv0, hv1⟩ := hDv v hv
      obtain ⟨hw0, hw1⟩ := hDv w hw
      rw [abs_mul, abs_mul, abs_of_nonneg hv0, abs_of_nonneg hw0]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      nlinarith
    calc |∑ v ∈ D.support.filter (fun v => v ∈ S), ∑ w ∈ (D.support.filter (fun v => v ∈ S)).erase v,
            (D v : ℝ) * (D w : ℝ) * pairHt s v w|
        ≤ ∑ v ∈ D.support.filter (fun v => v ∈ S), |∑ w ∈ (D.support.filter (fun v => v ∈ S)).erase v,
            (D v : ℝ) * (D w : ℝ) * pairHt s v w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ D.support.filter (fun v => v ∈ S), ∑ w ∈ (D.support.filter (fun v => v ∈ S)).erase v,
            |(D v : ℝ) * (D w : ℝ) * pairHt s v w| :=
          Finset.sum_le_sum fun v _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ D.support.filter (fun v => v ∈ S), ∑ w ∈ D.support.filter (fun v => v ∈ S),
            (g₀ : ℝ) ^ 2 * |pairHt s v w| :=
          Finset.sum_le_sum fun v hv => (Finset.sum_le_sum fun w hw => hpair v hv w (Finset.mem_of_mem_erase hw)).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun _ _ _ => mul_nonneg (by positivity) (abs_nonneg _)))
      _ ≤ ∑ v ∈ S, ∑ w ∈ S, (g₀ : ℝ) ^ 2 * |pairHt s v w| :=
          (Finset.sum_le_sum fun v _ => Finset.sum_le_sum_of_subset_of_nonneg
              (fun w hw => (Finset.mem_filter.mp hw).2) (fun _ _ _ => mul_nonneg (by positivity) (abs_nonneg _))).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => (Finset.mem_filter.mp hv).2)
              (fun _ _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (abs_nonneg _)))
      _ = (g₀ : ℝ) ^ 2 * CbS := by
          rw [hCbS, Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by rw [Finset.mul_sum]
      _ ≤ W * CtS + (g₀ : ℝ) ^ 2 * CbS := by nlinarith

end ConfGlue
end ConfGlueSec

section ConfGlue2Sec
set_option autoImplicit false
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.AlgebraicCurve ModularCurve"

namespace ConfGlue

theorem exists_uniformiser_assignment (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ τ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → modularFunctionFieldBar N,
      (∀ R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.ord (τ R) = 1) ∧
      ∀ R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R ≠ cuspInftyBar N →
        ∃ i, s i ∈ R.toValuationSubring ∧
        τ R = s i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s i)) := by
  classical
  let jElt : modularFunctionFieldBar N :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩
  have hj : (cuspInftyBar N).ord jElt = -1 := ord_cuspInftyBar_coeffEmb_jq N
  have hcov : ∀ R, R ≠ cuspInftyBar N → ∃ i, s i ∈ R.toValuationSubring ∧
      R.ord (s i - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (R.evalAt (s i))) = 1 :=
    fun R hR => exists_ord_sub_evalAt_eq_one N s hs R hR
  refine ⟨fun R => if hR : R = cuspInftyBar N then jElt⁻¹ else
      s (Classical.choose (hcov R hR))
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (R.evalAt (s (Classical.choose (hcov R hR)))), fun R => ?_, fun R hR => ?_⟩
  · dsimp only
    by_cases hR : R = cuspInftyBar N
    · subst hR
      rw [dif_pos rfl, Place.ord_inv, hj]
      norm_num
    · rw [dif_neg hR]
      exact (Classical.choose_spec (hcov R hR)).2
  · refine ⟨Classical.choose (hcov R hR), (Classical.choose_spec (hcov R hR)).1, ?_⟩
    dsimp only
    rw [dif_neg hR]

theorem choose_two_le_half_sub_one_mul {n g : ℕ} (hn : n ≤ g) :
    (n : ℝ) * ((n : ℝ) - 1) / 2 ≤ ((g : ℝ) - 1) / 2 * n := by
  have h : (n : ℝ) ≤ g := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem abs_le_add_two_mul_of_neg_le {t F : ℝ} (hF : 0 ≤ F) (h : -F ≤ t) : |t| ≤ t + 2 * F := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]; linarith
  · rw [abs_of_neg ht]; linarith

theorem sum_mul_abs_le_of_neg_le {ι : Type*} (S : Finset ι) (w t : ι → ℝ) {F : ℝ} (hF : 0 ≤ F)
    (hw : ∀ v ∈ S, 0 ≤ w v) (h : ∀ v ∈ S, -F ≤ t v) :
    ∑ v ∈ S, w v * |t v| ≤ (∑ v ∈ S, w v * t v) + 2 * F * ∑ v ∈ S, w v := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v hv => ?_
  have := abs_le_add_two_mul_of_neg_le hF (h v hv)
  have hwv := hw v hv
  nlinarith

theorem int_choose_two_le_half_sub_one_mul {d : ℤ} {g : ℕ} (h0 : 0 ≤ d) (hd : d ≤ g) :
    (d : ℝ) * ((d : ℝ) - 1) / 2 ≤ ((g : ℝ) - 1) / 2 * d := by
  have h : (d : ℝ) ≤ g := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := by exact_mod_cast h0
  nlinarith

theorem finsupp_sum_mul_abs_le_of_neg_le {α : Type*} (E : α →₀ ℤ) (hE : ∀ v, 0 ≤ E v) (t : α → ℝ)
    {F : ℝ} (hF : 0 ≤ F) (h : ∀ v, -F ≤ t v) :
    (E.sum fun v n => (n : ℝ) * |t v|)
      ≤ (E.sum fun v n => (n : ℝ) * t v) + 2 * F * (E.sum fun _ n => (n : ℝ)) := by
  simp only [Finsupp.sum]
  exact sum_mul_abs_le_of_neg_le E.support (fun v => (E v : ℝ)) t hF
    (fun v _ => by show (0 : ℝ) ≤ (E v : ℝ); exact_mod_cast hE v) (fun v _ => h v)

theorem exists_disjoint_of_card_lt {α ι : Type*} [Fintype ι] (T : Finset α) (B : ι → Finset α)
    (hdisj : ∀ a a', a ≠ a' → Disjoint (B a) (B a')) (hcard : T.card < Fintype.card ι) :
    ∃ a, Disjoint T (B a) := by
  classical
  by_contra hcon
  push Not at hcon
  have hbad : ∀ a, ∃ x, x ∈ T ∧ x ∈ B a := fun a => Finset.not_disjoint_iff.mp (hcon a)
  choose φ hφ using hbad
  have hinj : Function.Injective φ := by
    intro a a' h
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj a a' hne) (hφ a).2 (h ▸ (hφ a').2)
  have hle : Fintype.card ι ≤ T.card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card_of_injOn φ (fun a _ => (hφ a).1) (hinj.injOn)
  omega

theorem le_sum_abs {κ : Type*} [Fintype κ] (C : κ → ℝ) (k : κ) : C k ≤ ∑ k', |C k'| :=
  (le_abs_self (C k)).trans
    (Finset.single_le_sum (f := fun k' => |C k'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k))

theorem le_sum_abs_of_mem {κ : Type*} (s : Finset κ) (C : κ → ℝ) {k : κ} (hk : k ∈ s) :
    C k ≤ ∑ k' ∈ s, |C k'| :=
  (le_abs_self (C k)).trans (Finset.single_le_sum (f := fun k' => |C k'|) (fun _ _ => abs_nonneg _) hk)

theorem exists_forall_le_of_fintype {κ : Type*} [Fintype κ] (C : κ → ℝ) :
    ∃ Cmax : ℝ, 0 ≤ Cmax ∧ ∀ k, C k ≤ Cmax :=
  ⟨∑ k', |C k'|, Finset.sum_nonneg fun _ _ => abs_nonneg _, le_sum_abs C⟩

theorem exists_forall_le_of_finset {α : Type*} (S : Finset α) (C : α → ℝ) :
    ∃ Cmax : ℝ, 0 ≤ Cmax ∧ ∀ w ∈ S, C w ≤ Cmax :=
  ⟨∑ w ∈ S, |C w|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun _ hw => le_sum_abs_of_mem S C hw⟩

theorem exists_forall_le_of_finite {κ : Type*} [Finite κ] (C : κ → ℝ) :
    ∃ Cmax : ℝ, 0 ≤ Cmax ∧ ∀ k, C k ≤ Cmax := by
  cases nonempty_fintype κ
  exact exists_forall_le_of_fintype C

scoped instance finite_boundedPattern (M g : ℕ) : Finite {e : Fin M → ℕ // ∀ i, e i ≤ g} := by
  classical
  refine Finite.of_injective (fun e : {e : Fin M → ℕ // ∀ i, e i ≤ g} =>
    (fun i => (⟨e.1 i, Nat.lt_succ_of_le (e.2 i)⟩ : Fin (g + 1)))) ?_
  intro e e' h
  apply Subtype.ext; funext i
  have := congrFun h i
  exact congrArg Fin.val this

end ConfGlue
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"
end ConfGlue2Sec
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

namespace ConfGlue

theorem absLogHeight_eq_inv_mul_logHeight {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] (hK : ∀ i, x i ∈ K) :
    absLogHeight x = (Module.finrank ℚ ↥K : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hK i⟩ : ↥K)) := by
  haveI := AlgebraicCurve.finiteDimensional_adjoin_range x
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ K :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact hK i)
  unfold absLogHeight
  rw [← Height.inv_finrank_mul_logHeight_inclusion hle]
  rfl

theorem absLogHeight_comp_equiv {ι ι' : Type} [Fintype ι] [Fintype ι'] (x : ι → AlgebraicClosure ℚ) (σ : ι' ≃ ι) :
    absLogHeight (x ∘ σ) = absLogHeight x := by
  haveI := AlgebraicCurve.finiteDimensional_adjoin_range x
  set K := IntermediateField.adjoin ℚ (Set.range x)
  have hK : ∀ i, x i ∈ K := fun i => IntermediateField.subset_adjoin ℚ (Set.range x) ⟨i, rfl⟩
  rw [absLogHeight_eq_inv_mul_logHeight (x ∘ σ) K (fun i => hK (σ i)), absLogHeight_eq_inv_mul_logHeight x K hK]
  congr 1
  exact Height.logHeight_comp_equiv σ (fun i => (⟨x i, hK i⟩ : ↥K))

end ConfGlue
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

namespace ConfGlue

theorem exists_coeff_of_mem_riemannRochSpace_two_smul (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (u : modularFunctionFieldBar N)
    (hu : u ∈ riemannRochSpace ((2 : ℤ) • embDivisor N)) :
    ∃ c : Fin r × Fin r → AlgebraicClosure ℚ, u = ∑ p, c p • (s p.1 * s p.2) := by
  classical
  have hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace (embDivisor N) := hs.2
  have h2 : riemannRochSpace ((2 : ℤ) • embDivisor N)
      = Submodule.span (AlgebraicClosure ℚ) (Set.range fun p : Fin r × Fin r => s p.1 * s p.2) := by
    rw [← ModularCurve.JZero.riemannRochSpace_embDivisor_mul_self N, ← hspan, Submodule.span_mul_span]
    congr 1
    ext x
    simp only [Set.mem_mul, Set.mem_range, Prod.exists]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩; exact ⟨i, j, rfl⟩
    · rintro ⟨i, j, rfl⟩; exact ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
  rw [h2] at hu
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hu
  exact ⟨c, hc.symm⟩

theorem exists_presentation_two (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (hs : IsEmbBasis N s) (u : modularFunctionFieldBar N)
    (hu : u ∈ riemannRochSpace ((2 : ℤ) • embDivisor N)) :
    ∃ c : (Fin 2 → Fin r) → AlgebraicClosure ℚ, u = ∑ φ : Fin 2 → Fin r, c φ • ∏ l, s (φ l) := by
  classical
  obtain ⟨c, hc⟩ := exists_coeff_of_mem_riemannRochSpace_two_smul N s hs u hu
  refine ⟨fun φ => c (φ 0, φ 1), ?_⟩
  rw [hc]
  refine (Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin r) _ _ fun φ => ?_).symm
  simp [Fin.prod_univ_two, piFinTwoEquiv]

end ConfGlue
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "finiteDimensional_adjoin_range absLogHeight evalVec pointHt pairHt baseHt heightForm Place Place.ord_mul Place.ord_inv Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors riemannRochSpace mem_riemannRochSpace_iff genusFF HasCanonicalDivisor canonicalDivisorOf genus regVal jetMatrix jetMult jetDivisor jetDivisor_apply IsConfluentPattern IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed lSpace_eq_bot_of_degree_neg exists_forall_neg_le_pairHt exists_forall_neg_le_baseHt isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot Place.isRational_iff_deg_eq_one pairHt_comm"
p2m_open "AlgebraicCurve"

section AppendRows

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem jetDivisor_append {m m' : ℕ} (R : Fin m → Place K F) (R' : Fin m' → Place K F) :
    jetDivisor (Fin.append R R') = jetDivisor R + jetDivisor R' := by
  simp only [jetDivisor]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem jetMult_append {m m' : ℕ} (R : Fin m → Place K F) (R' : Fin m' → Place K F) (v : Place K F) :
    jetMult (Fin.append R R') v = jetMult R v + jetMult R' v := by
  have h := congrArg (fun D : Divisor K F => D v) (jetDivisor_append R R')
  simp only [Finsupp.add_apply, jetDivisor_apply] at h
  exact_mod_cast h

theorem jetMult_eq_zero_of_forall_ne {m : ℕ} (R : Fin m → Place K F) {v : Place K F} (h : ∀ i, R i ≠ v) :
    jetMult R v = 0 := by
  classical
  simp only [jetMult, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun i _ hi => h i hi

namespace IsConfluentPattern

private theorem _root_.AlgebraicCurve.IsConfluentPattern.append {m m' : ℕ}
    {R : Fin m → Place K F} {t : Fin m → F} {e : Fin m → ℕ}
    {R' : Fin m' → Place K F} {t' : Fin m' → F} {e' : Fin m' → ℕ}
    (h : IsConfluentPattern R t e) (h' : IsConfluentPattern R' t' e') (hdis : ∀ i i', R i ≠ R' i') :
    IsConfluentPattern (Fin.append R R') (Fin.append t t') (Fin.append e e') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    induction x using Fin.addCases with
    | left i =>
      induction y using Fin.addCases with
      | left i' => simp only [Fin.append_left] at hxy ⊢; exact h1 i i' hxy
      | right j' => simp only [Fin.append_left, Fin.append_right] at hxy; exact absurd hxy (hdis i j')
    | right j =>
      induction y using Fin.addCases with
      | left i' => simp only [Fin.append_left, Fin.append_right] at hxy; exact absurd hxy.symm (hdis i' j)
      | right j' => simp only [Fin.append_right] at hxy ⊢; exact h1' j j' hxy
  · intro x y hxy hexy
    induction x using Fin.addCases with
    | left i =>
      induction y using Fin.addCases with
      | left i' => simp only [Fin.append_left] at hxy hexy; rw [h2 i i' hxy hexy]
      | right j' => simp only [Fin.append_left, Fin.append_right] at hxy; exact absurd hxy (hdis i j')
    | right j =>
      induction y using Fin.addCases with
      | left i' => simp only [Fin.append_left, Fin.append_right] at hxy; exact absurd hxy.symm (hdis i' j)
      | right j' => simp only [Fin.append_right] at hxy hexy; rw [h2' j j' hxy hexy]
  · intro x
    induction x using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      rw [jetMult_append, jetMult_eq_zero_of_forall_ne R' (fun j hj => hdis i j hj.symm), add_zero]
      exact h3 i
    | right j =>
      simp only [Fin.append_right]
      rw [jetMult_append, jetMult_eq_zero_of_forall_ne R (fun i hi => hdis i j hi), zero_add]
      exact h3' j

end IsConfluentPattern
p2m_export "AlgebraicCurve" "IsConfluentPattern.append"
end AppendRows
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

section ConfCoreSec
set_option autoImplicit false
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.AlgebraicCurve ModularCurve KaehlerDifferential"

namespace ConfCore

theorem append_comp_eq {α β : Type*} {m m' : ℕ} (R : Fin m → α) (R' : Fin m' → α) (τ : α → β) :
    Fin.append (fun i => τ (R i)) (fun i => τ (R' i)) = fun x => τ (Fin.append R R' x) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

set_option synthInstance.maxHeartbeats 800000 in

theorem isUnit_det_jetMatrix_frame (N : ℕ) [NeZero N]
    [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))]
    {ω : Ω[↥(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)]} (hω : ω ≠ 0)
    {g m m' : ℕ} (f : Fin g → modularFunctionFieldBar N)
    (hfK : ∀ j, f j ∈ riemannRochSpace (canonicalDivisorOf hω))
    (hfli : LinearIndependent (AlgebraicClosure ℚ) f)
    (h : modularFunctionFieldBar N) (hh0 : h ≠ 0)
    (Bc : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hBc_apply : ∀ v, Bc v = v.ord h + ((2 : ℤ) • embDivisor N) v - (canonicalDivisorOf hω) v)
    (σ : Fin (m + m') ≃ Fin g) (u : Fin (m + m') → modularFunctionFieldBar N) (hu : ∀ j, u j = f (σ j) * h)
    (τ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → modularFunctionFieldBar N)
    (hτ : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.ord (τ v) = 1)
    (R : Fin m → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (e : Fin m → ℕ)
    (R' : Fin m' → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (e' : Fin m' → ℕ)
    (hpatM : IsConfluentPattern R (fun i => τ (R i)) e)
    (hpatF : IsConfluentPattern R' (fun i => τ (R' i)) e')
    (hdisj : ∀ i i', R i ≠ R' i')
    (hRinf : ∀ i, R i ≠ cuspInftyBar N) (hR'inf : ∀ i', R' i' ≠ cuspInftyBar N)
    (hRB : ∀ i, Bc (R i) = 0) (hR'B : ∀ i', Bc (R' i') = 0)
    (hrat : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.IsRational)
    (hbot : riemannRochSpace (canonicalDivisorOf hω - (jetDivisor R + jetDivisor R')) = ⊥) :
    IsUnit (jetMatrix (Fin.append R R') (Fin.append (fun i => τ (R i)) (fun i => τ (R' i)))
      (Fin.append e e') u).det := by
  classical
  set K₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := canonicalDivisorOf hω with hK₀
  set A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := (2 : ℤ) • embDivisor N - Bc with hAdef
  have hA_apply : ∀ v, A v = K₀ v - v.ord h := fun v => by
    simp only [hAdef, Finsupp.coe_sub, Pi.sub_apply, hBc_apply]; ring
  have hE_apply : ∀ v, v ≠ cuspInftyBar N → ((2 : ℤ) • embDivisor N) v = 0 := fun v hv => by
    simp [embDivisor, Ne.symm hv]

  have hpat : IsConfluentPattern (Fin.append R R') (Fin.append (fun i => τ (R i)) (fun i => τ (R' i)))
      (Fin.append e e') := hpatM.append hpatF hdisj
  have hrows_inf : ∀ x, Fin.append R R' x ≠ cuspInftyBar N := fun x => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · simpa using hRinf i
    · simpa using hR'inf j
  have hrows_B : ∀ x, Bc (Fin.append R R' x) = 0 := fun x => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · simpa using hRB i
    · simpa using hR'B j
  have ht1 : ∀ x, (Fin.append R R' x).ord (Fin.append (fun i => τ (R i)) (fun i => τ (R' i)) x) = 1 := by
    intro x
    rw [append_comp_eq]
    exact hτ _
  have hA0 : ∀ x, A (Fin.append R R' x) = 0 := by
    intro x
    have h1 := hrows_B x
    rw [hBc_apply, hE_apply _ (hrows_inf x)] at h1
    rw [hA_apply]
    linarith

  have hf0 : ∀ j, f j ≠ 0 := hfli.ne_zero
  have hfσ : LinearIndependent (AlgebraicClosure ℚ) (f ∘ σ) := hfli.comp σ σ.injective
  have hli : LinearIndependent (AlgebraicClosure ℚ) u := by
    rw [Fintype.linearIndependent_iff] at hfσ ⊢
    intro c hc j
    apply hfσ c _ j
    have hsum : (∑ i, c i • f (σ i)) * h = 0 := by
      rw [Finset.sum_mul]
      have : ∑ i, c i • u i = ∑ i, (c i • f (σ i)) * h :=
        Finset.sum_congr rfl fun i _ => by rw [hu, Algebra.smul_def, Algebra.smul_def, mul_assoc]
      rw [← this]; exact hc
    simpa using (mul_eq_zero.mp hsum).resolve_right hh0
  have huA : ∀ j, u j ∈ riemannRochSpace A := by
    intro j
    rw [mem_riemannRochSpace_iff]
    intro v; right
    rw [hu, Place.ord_mul _ (hf0 _) hh0, hA_apply]
    have := ((mem_riemannRochSpace_iff.mp (hfK (σ j))) v).resolve_left (hf0 _)
    linarith

  rw [AlgebraicCurve.isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot A u hli huA
    (Fin.append R R') _ (Fin.append e e') hpat (fun x => hrat _) ht1 hA0]

  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hx1
  set y : modularFunctionFieldBar N := ∑ i, c i • f (σ i) with hy
  have hxy : ∑ i, c i • u i = y * h := by
    rw [hy, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hu, Algebra.smul_def, Algebra.smul_def, mul_assoc]
  rw [hxy] at hx2 ⊢
  suffices hy0 : y = 0 by rw [hy0, zero_mul]
  have hyK : y ∈ riemannRochSpace (K₀ - (jetDivisor R + jetDivisor R')) := by
    rcases eq_or_ne y 0 with hy0 | hy0
    · rw [hy0]; exact Submodule.zero_mem _
    rw [mem_riemannRochSpace_iff]
    intro v; right
    have hm := (mem_riemannRochSpace_iff.mp hx2) v
    rcases hm with h0 | hle
    · exact absurd h0 (mul_ne_zero hy0 hh0)
    · rw [Place.ord_mul _ hy0 hh0] at hle
      rw [jetDivisor_append] at hle
      simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply, hA_apply] at hle ⊢
      linarith
  rw [hbot] at hyK
  exact (Submodule.mem_bot _).mp hyK

theorem conf_bookkeeping (g m ε ε₁ TM1 TM2 SMM SMF SFF WF SQ SB SPT SDER CL C7 KD KQ KB KT CF Ct : ℝ)
    (hm2 : 2 ≤ m) (hmg : m ≤ g) (hε₁ : ε₁ * (4 * (g + 1)) = ε) (hε₁0 : 0 ≤ ε₁)
    (hCF : 0 ≤ CF) (hCt : 0 ≤ Ct)
    (hL : SMM / 2 + SMF + SQ + SB ≤ 2 * SPT + SDER + CL)
    (hPT : SPT ≤ (2 * g + 1) * TM1 + g * C7)
    (hDER : SDER ≤ (2 * g - 2 + ε₁) * TM2 + KD)
    (hQ : (g - m) * (1 - ε₁) * TM1 - KQ ≤ SQ)
    (hB : (2 * g + 4) * (1 - ε₁) * TM1 - KB ≤ SB)
    (hFF : |SFF| ≤ CF) (hWF : |WF| ≤ CF)
    (hT1 : -(g * Ct) ≤ TM1) (hT2 : TM2 ≤ (g - 1) / 2 * TM1 + KT) :
    SMM / 2 + SMF + SFF / 2 ≤ (g + m - 2 + ε) * TM1 + (2 * g - 2) * TM2 + WF
      + (CL + 2 * g * C7 + KD + KQ + KB + 2 * CF + ε * g * Ct + ε₁ * KT) := by
  have hg0 : 0 ≤ g := by linarith

  have step1 : SMM / 2 + SMF
      ≤ ((g + m - 2) + ε₁ * (3 * g + 4 - m)) * TM1 + (2 * g - 2 + ε₁) * TM2
        + (CL + 2 * g * C7 + KD + KQ + KB) := by
    nlinarith [hL, hPT, hDER, hQ, hB]

  have step2 : ε₁ * TM2 ≤ ε₁ * ((g - 1) / 2 * TM1) + ε₁ * KT := by
    have := mul_le_mul_of_nonneg_left hT2 hε₁0
    linarith

  have step3 : (ε₁ * (3 * g + 4 - m) + ε₁ * ((g - 1) / 2) - ε) * TM1 ≤ ε * g * Ct := by
    have e1 : ε₁ * (3 * g + 4 - m) + ε₁ * ((g - 1) / 2) - ε = -(ε₁ * (m + g / 2 + 1 / 2)) := by
      rw [← hε₁]; ring
    rw [e1]
    have h1 : 0 ≤ ε₁ * (m + g / 2 + 1 / 2) := mul_nonneg hε₁0 (by linarith)
    have h2 : ε₁ * (m + g / 2 + 1 / 2) * (-TM1) ≤ ε₁ * (m + g / 2 + 1 / 2) * (g * Ct) :=
      mul_le_mul_of_nonneg_left (by linarith) h1
    have h3 : (m + g / 2 + 1 / 2) * (g * Ct) ≤ (4 * (g + 1)) * (g * Ct) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hg0 hCt)
    have h4 : ε₁ * ((m + g / 2 + 1 / 2) * (g * Ct)) ≤ ε₁ * ((4 * (g + 1)) * (g * Ct)) :=
      mul_le_mul_of_nonneg_left h3 hε₁0
    calc -(ε₁ * (m + g / 2 + 1 / 2)) * TM1 = ε₁ * (m + g / 2 + 1 / 2) * (-TM1) := by ring
      _ ≤ ε₁ * (m + g / 2 + 1 / 2) * (g * Ct) := h2
      _ = ε₁ * ((m + g / 2 + 1 / 2) * (g * Ct)) := by ring
      _ ≤ ε₁ * ((4 * (g + 1)) * (g * Ct)) := h4
      _ = ε * g * Ct := by rw [← hε₁]; ring

  have hFF' : SFF / 2 ≤ CF := by linarith [le_abs_self SFF, abs_nonneg SFF]
  have hWF' : -CF ≤ WF := by linarith [neg_abs_le WF]
  nlinarith [step1, step2, step3, hFF', hWF']

end ConfCore
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"
end ConfCoreSec
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "finiteDimensional_adjoin_range absLogHeight evalVec pointHt pairHt baseHt heightForm Place Place.ord_mul Place.ord_inv Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors riemannRochSpace mem_riemannRochSpace_iff genusFF HasCanonicalDivisor canonicalDivisorOf genus regVal jetMatrix jetMult jetDivisor jetDivisor_apply IsConfluentPattern IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed lSpace_eq_bot_of_degree_neg exists_forall_neg_le_pairHt exists_forall_neg_le_baseHt isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot Place.isRational_iff_deg_eq_one pairHt_comm"
p2m_open "AlgebraicCurve"

section RowSums

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem sum_rows_eq_jetDivisor_sum {m : ℕ} (R : Fin m → Place K F) (φ : Place K F → ℝ) :
    ∑ i, φ (R i) = (jetDivisor R).sum (fun v n => (n : ℝ) * φ v) := by
  classical
  rw [Finset.sum_comp]
  have hsupp : (jetDivisor R).support ⊆ Finset.univ.image R := by
    intro v hv
    rw [Finsupp.mem_support_iff, jetDivisor_apply] at hv
    have : jetMult R v ≠ 0 := by exact_mod_cast hv
    simp only [jetMult, ne_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_forall, not_not] at this
    obtain ⟨i, -, hi⟩ := this
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  rw [Finsupp.sum_of_support_subset _ hsupp _ (fun v _ => by simp)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [jetDivisor_apply, nsmul_eq_mul]
  simp only [jetMult, Int.cast_natCast]

open Classical in

theorem sum_orders_block {m : ℕ} {R : Fin m → Place K F} {t : Fin m → F} {e : Fin m → ℕ}
    (hpat : IsConfluentPattern R t e) (v : Place K F) :
    ∑ i ∈ Finset.univ.filter (fun i => R i = v), (e i : ℝ) = (jetMult R v : ℝ) * ((jetMult R v : ℝ) - 1) / 2 := by
  classical
  set B := Finset.univ.filter (fun i => R i = v) with hB
  have hcard : B.card = jetMult R v := rfl

  have hinj : Set.InjOn e ↑B := fun i hi i' hi' h =>
    hpat.2.1 i i' ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hi').2.symm) h
  have himg : B.image e = Finset.range (jetMult R v) := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      rw [Finset.mem_range, ← (Finset.mem_filter.mp hi).2]
      exact hpat.2.2 i
    · rw [Finset.card_range, Finset.card_image_of_injOn hinj, hcard]
  calc ∑ i ∈ B, (e i : ℝ) = ∑ k ∈ B.image e, (k : ℝ) := (Finset.sum_image hinj).symm
    _ = ∑ k ∈ Finset.range (jetMult R v), (k : ℝ) := by rw [himg]
    _ = (jetMult R v : ℝ) * ((jetMult R v : ℝ) - 1) / 2 := by
        have h2 := Finset.sum_range_id_mul_two (jetMult R v)
        rcases Nat.eq_zero_or_pos (jetMult R v) with h0 | hpos
        · simp [h0]
        · have h3 : ((∑ k ∈ Finset.range (jetMult R v), k : ℕ) : ℝ) * 2
              = (jetMult R v : ℝ) * ((jetMult R v : ℝ) - 1) := by
            rw [← Nat.cast_pred hpos]
            exact_mod_cast h2
          rw [← Nat.cast_sum]
          linarith

open Classical in

theorem sum_rows_orders_eq_jetDivisor_sum {m : ℕ} {R : Fin m → Place K F} {t : Fin m → F} {e : Fin m → ℕ}
    (hpat : IsConfluentPattern R t e) (ψ : Place K F → ℝ) :
    ∑ i, (e i : ℝ) * ψ (R i) = (jetDivisor R).sum (fun v n => (n : ℝ) * ((n : ℝ) - 1) / 2 * ψ v) := by
  classical

  rw [← Finset.sum_fiberwise_of_maps_to (g := R) (s := Finset.univ) (t := Finset.univ.image R)
        (fun i _ => Finset.mem_image_of_mem R (Finset.mem_univ i))]
  have hsupp : (jetDivisor R).support ⊆ Finset.univ.image R := by
    intro v hv
    rw [Finsupp.mem_support_iff, jetDivisor_apply] at hv
    have : jetMult R v ≠ 0 := by exact_mod_cast hv
    simp only [jetMult, ne_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_forall, not_not] at this
    obtain ⟨i, -, hi⟩ := this
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  rw [Finsupp.sum_of_support_subset _ hsupp _ (fun v _ => by simp)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have : ∑ i ∈ Finset.univ.filter (fun i => R i = v), (e i : ℝ) * ψ (R i)
      = (∑ i ∈ Finset.univ.filter (fun i => R i = v), (e i : ℝ)) * ψ v := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [this, sum_orders_block hpat v, jetDivisor_apply]
  push_cast
  ring

end RowSums
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "finiteDimensional_adjoin_range absLogHeight evalVec pointHt pairHt baseHt heightForm Place Place.ord_mul Place.ord_inv Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors riemannRochSpace mem_riemannRochSpace_iff genusFF HasCanonicalDivisor canonicalDivisorOf genus regVal jetMatrix jetMult jetDivisor jetDivisor_apply IsConfluentPattern IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed lSpace_eq_bot_of_degree_neg exists_forall_neg_le_pairHt exists_forall_neg_le_baseHt isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot Place.isRational_iff_deg_eq_one pairHt_comm"
p2m_open "AlgebraicCurve"

section RowSums2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open Classical in

theorem sum_rows_eq_sum_jetMult {m : ℕ} (R : Fin m → Place K F) (S : Finset (Place K F)) (hS : ∀ i, R i ∈ S)
    (φ : Place K F → ℝ) :
    ∑ i, φ (R i) = ∑ v ∈ S, (jetMult R v : ℝ) * φ v := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := R) (fun i _ => hS i)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have : ∑ i ∈ Finset.univ.filter (fun i => R i = v), φ (R i) = ∑ i ∈ Finset.univ.filter (fun i => R i = v), φ v :=
    Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [this, Finset.sum_const, nsmul_eq_mul]
  rfl

open Classical in

theorem sum_rows_orders_eq_sum_jetMult {m : ℕ} {R : Fin m → Place K F} {t : Fin m → F} {e : Fin m → ℕ}
    (hpat : IsConfluentPattern R t e) (S : Finset (Place K F)) (hS : ∀ i, R i ∈ S) (ψ : Place K F → ℝ) :
    ∑ i, (e i : ℝ) * ψ (R i) = ∑ v ∈ S, (jetMult R v : ℝ) * ((jetMult R v : ℝ) - 1) / 2 * ψ v := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := R) (fun i _ => hS i)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have : ∑ i ∈ Finset.univ.filter (fun i => R i = v), (e i : ℝ) * ψ (R i)
      = (∑ i ∈ Finset.univ.filter (fun i => R i = v), (e i : ℝ)) * ψ v := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  rw [this, sum_orders_block hpat v]

end RowSums2
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

end AlgebraicCurve
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

namespace ConfChild2

open ModularCurve.JZero

noncomputable def jElt (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

noncomputable def tangentHt (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) : ℝ :=
  absLogHeight (fun p : Fin r × Fin r =>
    regVal s v t 1 1 (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))

end ConfChild2
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

namespace ConfChild2

open ModularCurve.JZero

theorem exists_finset_place_card_disjoint (N : ℕ) [NeZero N]
    (X : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) (n : ℕ) :
    ∃ 𝒬 : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), n ≤ 𝒬.card ∧ Disjoint 𝒬 X := by
  classical
  haveI := ModularCurve.infinite_place_modularFunctionFieldBar N
  have hinf : ((↑X : Set (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))ᶜ).Infinite :=
    X.finite_toSet.infinite_compl
  obtain ⟨T, hT, hcard⟩ := hinf.exists_subset_card_eq n
  refine ⟨T, hcard.ge, Finset.disjoint_left.mpr fun v hv hvX => ?_⟩
  exact hT (Finset.mem_coe.mpr hv) (Finset.mem_coe.mpr hvX)

theorem exists_cusp_finset (N : ℕ) [NeZero N] :
    ∃ S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), cuspInftyBar N ∈ S ∧
      ∀ v, v ∉ S → (jElt N : modularFunctionFieldBar N) ∈ v.toValuationSubring := by
  classical
  have hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hc := isCusp_cuspInftyBar N
  have hj0 : (jElt N : modularFunctionFieldBar N) ≠ 0 := by
    intro h0
    unfold jElt at h0
    exact hc (h0 ▸ zero_mem _)
  obtain ⟨Dj, hDj, -⟩ := hPD.exists_divisor (jElt N) hj0
  refine ⟨insert (cuspInftyBar N) Dj.support, Finset.mem_insert_self _ _, fun v hv => ?_⟩
  have hv' : v ∉ Dj.support := fun h => hv (Finset.mem_insert_of_mem h)
  have hord : v.ord (jElt N : modularFunctionFieldBar N) = 0 := by
    rw [← hDj]; exact Finsupp.notMem_support_iff.mp hv'
  by_contra hmem
  have hcv : IsCusp (jElt N : modularFunctionFieldBar N) v := hmem
  rw [isCusp_iff_ord_neg] at hcv
  omega

theorem exists_tangentHt_sub_two_mul_pointHt_le (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (hg : 1 ≤ genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N),
      P ≠ cuspInftyBar N → P.ord t = 1 →
      tangentHt N s P t - 2 * pointHt s P
        ≤ (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2 + ε)
            * baseHt s (cuspInftyBar N) P + C :=
  ModularCurve.JZero.exists_absLogHeight_regVal_sub_two_mul_pointHt_le N s hs hg ε hε

theorem exists_jetDivisor_eq (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ v, 0 ≤ D v)
    (hinf : D (cuspInftyBar N) = 0) :
    ∃ (M : ℕ) (R : Fin M → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (e : Fin M → ℕ),
      (∀ i, R i ≠ cuspInftyBar N) ∧ jetDivisor R = D ∧ (offBaseMass N D : ℤ) = M ∧
      ∀ τ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → modularFunctionFieldBar N,
        IsConfluentPattern R (fun i => τ (R i)) e := by
  classical

  set S := D.support with hS
  set P₀ : Fin S.card → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    fun i => ((S.equivFin.symm i : S) : _) with hP₀
  have hP₀inj : Function.Injective P₀ := fun i j h => S.equivFin.symm.injective (Subtype.ext h)
  have hP₀mem : ∀ i, P₀ i ∈ S := fun i => (S.equivFin.symm i).2
  set n : Fin S.card → ℕ := fun i => (D (P₀ i)).toNat with hn
  have hnD : ∀ i, (n i : ℤ) = D (P₀ i) := fun i => Int.toNat_of_nonneg (hD _)

  set σ : (Σ i, Fin (n i)) ≃ Fin (∑ i, n i) := finSigmaFinEquiv with hσ
  set R : Fin (∑ i, n i) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := fun x => P₀ (σ.symm x).1 with hR

  have hcount : ∀ i₀, jetMult R (P₀ i₀) = n i₀ := by
    intro i₀
    simp only [jetMult, hR]
    rw [← Finset.card_map σ.symm.toEmbedding]
    have h1 : (Finset.univ.filter fun x : Fin (∑ i, n i) => P₀ (σ.symm x).1 = P₀ i₀).map σ.symm.toEmbedding
        = Finset.univ.filter (fun y : Σ i, Fin (n i) => y.1 = i₀) := by
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hP₀inj hx
      · intro hy; exact ⟨σ y, by rw [Equiv.symm_apply_apply]; exact congrArg P₀ hy, σ.symm_apply_apply y⟩
    have h2 : (Finset.univ.filter (fun y : Σ i, Fin (n i) => y.1 = i₀))
        = (Finset.univ : Finset (Fin (n i₀))).map ⟨fun k => (⟨i₀, k⟩ : Σ i, Fin (n i)), fun a b h => eq_of_heq (Sigma.mk.inj h).2⟩ := by
      ext ⟨i, k⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro rfl; exact ⟨k, rfl⟩
      · rintro ⟨k', h⟩; exact (Sigma.mk.inj h).1.symm
    rw [h1, h2, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hcount0 : ∀ v, v ∉ S → jetMult R v = 0 := by
    intro v hv
    simp only [jetMult, hR]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    exact hv (hx ▸ hP₀mem _)
  refine ⟨∑ i, n i, R, fun x => ((σ.symm x).2 : ℕ), ?_, ?_, ?_, ?_⟩
  · intro x h
    have hmem := hP₀mem (σ.symm x).1
    simp only [hR] at h
    rw [h] at hmem
    exact (Finsupp.mem_support_iff.mp hmem) hinf
  · ext v
    rw [jetDivisor_apply]
    by_cases hv : v ∈ S
    · obtain ⟨i₀, rfl⟩ : ∃ i₀, P₀ i₀ = v := ⟨S.equivFin ⟨v, hv⟩, by simp [hP₀]⟩
      rw [hcount, hnD]
    · rw [hcount0 v hv, Finsupp.notMem_support_iff.mp hv]; rfl
  · have herase : D.erase (cuspInftyBar N) = D := by
      ext v; rw [Finsupp.erase_apply]; split_ifs with h
      · rw [h, hinf]
      · rfl
    rw [offBaseMass, herase, Finsupp.sum, Nat.cast_sum]
    calc ∑ v ∈ S, D v = ∑ v : S, D (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := (Finset.sum_coe_sort S _).symm
      _ = ∑ i : Fin S.card, D (P₀ i) := Fintype.sum_equiv S.equivFin _ _ (fun v => by simp [hP₀])
      _ = ∑ i, (n i : ℤ) := Finset.sum_congr rfl fun i _ => (hnD i).symm
  · intro τ
    refine ⟨fun i i' h => congrArg τ h, fun x x' hP he => ?_, fun x => ?_⟩
    · apply σ.symm.injective
      simp only [hR] at hP
      have h1 : (σ.symm x).1 = (σ.symm x').1 := hP₀inj hP
      exact Sigma.ext h1 (by
        have : ((σ.symm x).2 : ℕ) = (σ.symm x').2 := he
        exact (Fin.heq_ext_iff (by rw [h1])).mpr this)
    · show ((σ.symm x).2 : ℕ) < jetMult R (R x)
      simp only [hR]
      rw [hcount]
      exact (σ.symm x).2.isLt

end ConfChild2
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

namespace ConfAssembly2

open ModularCurve.JZero

variable (N : ℕ) [NeZero N]

theorem riemannRochSpace_neg_single_cuspInftyBar :
    riemannRochSpace (-Finsupp.single (cuspInftyBar N) (1 : ℤ)) = ⊥ := by
  haveI := isCurveOver_modularFunctionFieldBar N
  have h : Divisor.degree (-Finsupp.single (cuspInftyBar N) (1 : ℤ)) < 0 := by
    rw [map_neg, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N)]
    norm_num
  exact AlgebraicCurve.lSpace_eq_bot_of_degree_neg h

theorem finrank_riemannRochSpace_canonicalDivisorOf
    [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))]
    {ω : Ω[↥(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)]} (hω : ω ≠ 0) :
    Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (canonicalDivisorOf hω))
      = genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
  have h := finrank_riemannRochSpace_canonicalDivisorOf_sub_erase_add_offBaseMass N hω
    (D := 0) le_rfl (by
      rw [Finsupp.erase_zero, zero_sub]
      exact riemannRochSpace_neg_single_cuspInftyBar N)
  have e : riemannRochSpace (canonicalDivisorOf hω - (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).erase (cuspInftyBar N))
      = riemannRochSpace (canonicalDivisorOf hω) := by
    rw [Finsupp.erase_zero, sub_zero]
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ e)] at h
  simp only [JZero.offBaseMass, Finsupp.erase_zero, Finsupp.sum_zero_index, add_zero] at h
  exact_mod_cast h

end ConfAssembly2
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

namespace ConfChild

open ModularCurve.JZero

set_option maxHeartbeats 16000000 in

theorem star_general (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, 0 ≤ D v) → D (cuspInftyBar N) = 0 →
      riemannRochSpace (D.erase (cuspInftyBar N) - Finsupp.single (cuspInftyBar N) (1 : ℤ)) = ⊥ →
      2 ≤ offBaseMass N D →
      ((D.erase (cuspInftyBar N)).sum fun v n => ((D.erase (cuspInftyBar N)).erase v).sum fun w k =>
          (n : ℝ) * (k : ℝ) * pairHt s v w) / 2
        ≤ ((D.erase (cuspInftyBar N)).sum fun v n =>
            (((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
                + (offBaseMass N D : ℝ) - 2 + ε) * (n : ℝ)
              + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
                * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)
          + C := by
  classical
  haveI := hasCanonicalDivisor_modularFunctionFieldBar N
  haveI := isCurveOver_modularFunctionFieldBar N
  have hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[↥(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)])
  set g : ℕ := genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) with hg
  set K₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := canonicalDivisorOf hω with hK₀
  set E2 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := (2 : ℤ) • embDivisor N with hE2
  have hE2_apply : ∀ v, v ≠ cuspInftyBar N → E2 v = 0 := fun v hv => by
    simp [hE2, embDivisor, Ne.symm hv]

  obtain ⟨Scusp, hinfS, hScusp⟩ := ConfChild2.exists_cusp_finset N

  obtain ⟨h, hh0, hhL, hsep⟩ := ModularCurve.exists_mem_riemannRochSpace_sub_canonicalDivisorOf_forall_ne_not_and N hω (g + 1)
  have hdiv : ∀ a, ∃ Dh : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, Dh v = v.ord (h a)) ∧ Divisor.degree Dh = 0 :=
    fun a => hPD.exists_divisor (h a) (hh0 a)
  choose Dh hDh hDhdeg using hdiv
  set Bc : Fin (g + 1) → Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    fun a => Dh a + E2 - K₀ with hBc
  have hBc_apply : ∀ a v, Bc a v = v.ord (h a) + E2 v - K₀ v := fun a v => by
    simp [hBc, hDh]
  have hBc_nonneg : ∀ a v, 0 ≤ Bc a v := by
    intro a v
    have hm := (mem_riemannRochSpace_iff.mp (hhL a)) v
    rcases hm with h0 | hle
    · exact absurd h0 (hh0 a)
    · rw [hBc_apply]
      simp only [Finsupp.coe_sub, Pi.sub_apply, hE2] at hle ⊢
      linarith

  obtain ⟨𝒬, h𝒬card, h𝒬disj⟩ := ConfChild2.exists_finset_place_card_disjoint N
    (insert (cuspInftyBar N) (Scusp ∪ Finset.univ.biUnion fun a => (Bc a).support)) (2 * g)
  have h𝒬inf : cuspInftyBar N ∉ 𝒬 := fun hq =>
    Finset.disjoint_left.mp h𝒬disj hq (Finset.mem_insert_self _ _)
  have h𝒬B : ∀ a, ∀ q ∈ 𝒬, Bc a q = 0 := by
    intro a q hq
    by_contra hne
    have : q ∈ insert (cuspInftyBar N) (Scusp ∪ Finset.univ.biUnion fun a => (Bc a).support) :=
      Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hne⟩))
    exact Finset.disjoint_left.mp h𝒬disj hq this

  set F : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := Scusp ∪ 𝒬 with hF
  have hFnc : ∀ v, v ∉ F →
      (ConfChild2.jElt N : modularFunctionFieldBar N) ∈ v.toValuationSubring :=
    fun v hv => hScusp v (fun hc => hv (Finset.mem_union_left _ hc))
  have hinfF : cuspInftyBar N ∈ F := Finset.mem_union_left _ hinfS

  obtain ⟨τ, hτ, -⟩ := ConfGlue.exists_uniformiser_assignment N s hs

  have hfinK := ConfAssembly2.finrank_riemannRochSpace_canonicalDivisorOf N hω
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  · refine ⟨0, fun D heff hinf hbot hm2 => ?_⟩
    exfalso
    have hSF := finrank_riemannRochSpace_canonicalDivisorOf_sub_erase_add_offBaseMass N hω
      (D := D) (fun v => heff v) hbot
    have h0 : (0 : ℤ) ≤ Module.finrank (AlgebraicClosure ℚ)
        ↥(riemannRochSpace (canonicalDivisorOf hω - D.erase (cuspInftyBar N))) := by positivity
    have : (offBaseMass N D : ℤ) ≤ g := by push_cast at hSF ⊢; linarith
    omega

  haveI : Module.Free (AlgebraicClosure ℚ) ↥(riemannRochSpace K₀) := Module.Free.of_divisionRing _ _
  haveI : Module.Finite (AlgebraicClosure ℚ) ↥(riemannRochSpace K₀) :=
    Module.finite_of_finrank_pos (by rw [hfinK]; exact hgpos)
  set bK := Module.finBasisOfFinrankEq (AlgebraicClosure ℚ) ↥(riemannRochSpace K₀) hfinK with hbK
  set f : Fin g → modularFunctionFieldBar N := fun j => (bK j : modularFunctionFieldBar N) with hf
  have hfK : ∀ j, f j ∈ riemannRochSpace K₀ := fun j => (bK j).2
  have hf0 : ∀ j, f j ≠ 0 := fun j h0 => bK.ne_zero j (Subtype.ext h0)
  have hfli : LinearIndependent (AlgebraicClosure ℚ) f :=
    bK.linearIndependent.map' (riemannRochSpace K₀).subtype (Submodule.ker_subtype _)
  set u : Fin (g + 1) → Fin g → modularFunctionFieldBar N := fun a j => f j * h a with hu
  have hu0 : ∀ a j, u a j ≠ 0 := fun a j => mul_ne_zero (hf0 j) (hh0 a)
  have hord_u : ∀ a j (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      v.ord (u a j) = v.ord (f j) + v.ord (h a) := fun a j v => Place.ord_mul _ (hf0 j) (hh0 a)
  have hordf : ∀ j (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), -K₀ v ≤ v.ord (f j) := fun j v =>
    ((mem_riemannRochSpace_iff.mp (hfK j)) v).resolve_left (hf0 j)
  have hordh : ∀ a (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), -(E2 - K₀) v ≤ v.ord (h a) := fun a v =>
    ((mem_riemannRochSpace_iff.mp (hhL a)) v).resolve_left (hh0 a)
  have huE2 : ∀ a j, u a j ∈ riemannRochSpace ((2 : ℤ) • embDivisor N) := by
    intro a j
    refine mem_riemannRochSpace_iff.mpr fun v => Or.inr ?_
    rw [hord_u]
    have h1 := hordf j v; have h2 := hordh a v
    simp only [Finsupp.coe_sub, Pi.sub_apply, hE2] at h1 h2 ⊢
    linarith

  have hBcu : ∀ a j w, Bc a w ≤ w.ord (u a j) + ((2 : ℤ) • embDivisor N) w := by
    intro a j w
    rw [hBc_apply, hord_u]
    have h1 := hordf j w
    simp only [hE2] at h1 ⊢
    linarith

  have hpres : ∀ a j, ∃ c : (Fin 2 → Fin r) → AlgebraicClosure ℚ, u a j = ∑ φ : Fin 2 → Fin r, c φ • ∏ l, s (φ l) :=
    fun a j => ConfGlue.exists_presentation_two N s hs (u a j) (huE2 a j)
  choose cpres hcpres using hpres
  obtain ⟨H, hH0, hH⟩ := ConfGlue.exists_forall_le_of_finset (Finset.univ : Finset (Fin (g + 1)))
    (fun a => absLogHeight (fun q : Fin g × (Fin 2 → Fin r) => cpres a q.1 q.2))

  have hJgood := ModularCurve.JZero.jensen_good_at_le N s hs
  have hJbad := fun S₀ => ModularCurve.JZero.jensen_bad_at_le N s hs S₀
  have hJarch := ModularCurve.JZero.jensen_arch_at_le_of_nonCuspidal N s hs
  have hled : ∀ p : Fin (g + 1) × Fin (g + 1), ∃ C : ℝ, _ := fun p =>
    ModularCurve.JZero.sum_pairHt_le_of_isUnit_det_jetMatrix N s hs 2 (p.1 : ℕ) (p.2 : ℕ) hJgood hJbad hJarch H
  choose Cled hCled using hled
  obtain ⟨CL, hCL0, hCL⟩ := ConfGlue.exists_forall_le_of_finset (Finset.univ : Finset (Fin (g + 1) × Fin (g + 1))) Cled

  set ε₁ : ℝ := ε / (4 * ((g : ℝ) + 1)) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  obtain ⟨Cder, hCder⟩ := ModularCurve.JZero.exists_absLogHeight_regVal_sub_two_mul_pointHt_le N s hs hgpos ε₁ hε₁pos

  obtain ⟨Cpt, hCpt⟩ := ModularCurve.JZero.exists_pointHt_le_mul_baseHt N s hs

  set W : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    (F ∪ Finset.univ.biUnion fun a => (Bc a).support) with hW
  have hS4a : ∀ w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ C : ℝ, _ := fun w₀ =>
    ModularCurve.JZero.exists_sub_mul_baseHt_le_pairHt N s hs ε₁ hε₁pos w₀
  choose CS4 hCS4 using hS4a
  obtain ⟨CW, hCW0, hCW⟩ := ConfGlue.exists_forall_le_of_finset W CS4

  obtain ⟨Cpf, hCpf0, hCpf⟩ := AlgebraicCurve.exists_forall_neg_le_pairHt s
  obtain ⟨Cbf, hCbf0, hCbf⟩ := AlgebraicCurve.exists_forall_neg_le_baseHt s

  obtain ⟨CF, hCF⟩ := ConfGlue.exists_bound_cusp_parts N s F g ε

  obtain ⟨Cfix, hCfix0, hCfix⟩ := ConfGlue.exists_forall_le_of_finset
    ((Finset.univ : Finset (Fin (g + 1))) ×ˢ F ×ˢ (Finset.range (g + 1)))
    (fun q : Fin (g + 1) × Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) × ℕ =>
      absLogHeight (fun j : Fin g => (q.2.1).taylorCoeff (τ q.2.1) q.2.2 (u q.1 j)))

  set KONST : ℝ := CL + (g : ℝ) * Cfix + 2 * (g : ℝ) * |Cpt| + (g : ℝ) * g * |Cder| + (g : ℝ) * g * CW
      + (g : ℝ) * (2 * g + 4) * (CW + ε₁ * Cbf) + 2 * |CF| + ε * g * Cbf + ε₁ * ((g : ℝ) * g * Cbf) with hKONST
  refine ⟨KONST, fun D heff hinf hbot hm2 => ?_⟩

  have herase : D.erase (cuspInftyBar N) = D := by
    ext v; rw [Finsupp.erase_apply]; split_ifs with hv
    · rw [hv, hinf]
    · rfl
  have hSF := finrank_riemannRochSpace_canonicalDivisorOf_sub_erase_add_offBaseMass N hω (D := D) (fun v => heff v) hbot
  rw [herase] at hSF
  set n' : ℕ := Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (canonicalDivisorOf hω - D)) with hn'
  have hMg : (offBaseMass N D : ℤ) + n' = g := by linarith
  have hM0 : (0 : ℤ) ≤ offBaseMass N D := by linarith

  have h𝒬card' : 2 * genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) ≤ 𝒬.card + 1 := by
    rw [← hg]; omega
  obtain ⟨Q, hQinj, hQmem, hQbot⟩ :=
    ModularCurve.exists_injective_riemannRochSpace_canonicalDivisorOf_sub_eq_bot N hω (E := D)
      (fun v => heff v) hn'.symm 𝒬 h𝒬card'
  have hQ𝒬 : ∀ l, Q l ∈ 𝒬 := fun l => (hQmem l).1
  have hQD : ∀ l, D (Q l) = 0 := fun l => Finsupp.notMem_support_iff.mp (hQmem l).2
  have hQinf : ∀ l, Q l ≠ cuspInftyBar N := fun l h => h𝒬inf (h ▸ hQ𝒬 l)
  have hQF : ∀ l, Q l ∈ F := fun l => Finset.mem_union_right _ (hQ𝒬 l)

  set Dmov : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := D.filter (fun v => v ∉ F) with hDmov
  set Dfix : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := D.filter (fun v => v ∈ F) with hDfix
  have hDsplit : Dfix + Dmov = D := by rw [hDfix, hDmov]; exact Finsupp.filter_add_filter_not D _
  have hDmov_apply : ∀ v, Dmov v = if v ∉ F then D v else 0 := fun v => by rw [hDmov, Finsupp.filter_apply]
  have hDfix_apply : ∀ v, Dfix v = if v ∈ F then D v else 0 := fun v => by rw [hDfix, Finsupp.filter_apply]
  have hmov_eff : ∀ v, 0 ≤ Dmov v := fun v => by
    rw [hDmov_apply]; split_ifs <;> first | exact heff v | exact le_rfl
  have hfix_eff : ∀ v, 0 ≤ Dfix v := fun v => by
    rw [hDfix_apply]; split_ifs <;> first | exact heff v | exact le_rfl
  have hmov_inf : Dmov (cuspInftyBar N) = 0 := by
    rw [hDmov_apply]; split_ifs <;> first | exact hinf | rfl
  have hfix_inf : Dfix (cuspInftyBar N) = 0 := by
    rw [hDfix_apply]; split_ifs <;> first | exact hinf | rfl
  obtain ⟨m, R, e, hRinf, hRdiv, hRmass, hRpat⟩ := ConfChild2.exists_jetDivisor_eq N Dmov hmov_eff hmov_inf
  obtain ⟨m₂, R₂, e₂, hR₂inf, hR₂div, hR₂mass, hR₂pat⟩ := ConfChild2.exists_jetDivisor_eq N Dfix hfix_eff hfix_inf

  have hRmem : ∀ i, R i ∉ F ∧ D (R i) ≠ 0 := by
    intro i
    have hpos : 0 < jetMult R (R i) := lt_of_le_of_lt (Nat.zero_le _) ((hRpat τ).2.2 i)
    have h1 : Dmov (R i) ≠ 0 := by
      rw [← hRdiv, jetDivisor_apply]; exact_mod_cast hpos.ne'
    rw [hDmov_apply] at h1
    by_cases hF : R i ∈ F
    · simp [hF] at h1
    · exact ⟨hF, by simpa [hF] using h1⟩

  have hR₂mem : ∀ i, R₂ i ∈ F ∧ D (R₂ i) ≠ 0 := by
    intro i
    have hpos : 0 < jetMult R₂ (R₂ i) := lt_of_le_of_lt (Nat.zero_le _) ((hR₂pat τ).2.2 i)
    have h1 : Dfix (R₂ i) ≠ 0 := by
      rw [← hR₂div, jetDivisor_apply]; exact_mod_cast hpos.ne'
    rw [hDfix_apply] at h1
    by_cases hF : R₂ i ∈ F
    · exact ⟨hF, by simpa [hF] using h1⟩
    · simp [hF] at h1

  have hQmult : ∀ l, jetMult Q (Q l) = 1 := by
    intro l
    classical
    simp only [jetMult]
    rw [Finset.card_eq_one]
    exact ⟨l, by ext l'; simp [hQinj.eq_iff]⟩
  have hQpat : IsConfluentPattern Q (fun l => τ (Q l)) (fun _ => (0 : ℕ)) :=
    ⟨fun l l' h => congrArg τ h, fun l l' h _ => hQinj h, fun l => by rw [hQmult]; exact Nat.one_pos⟩

  set R' : Fin (m₂ + n') → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := Fin.append R₂ Q with hR'
  set e' : Fin (m₂ + n') → ℕ := Fin.append e₂ (fun _ => (0 : ℕ)) with he'
  have hR₂Q : ∀ i l, R₂ i ≠ Q l := fun i l h => (hR₂mem i).2 (h ▸ hQD l)
  have hpatF : IsConfluentPattern R' (fun x => τ (R' x)) e' := by
    have := AlgebraicCurve.IsConfluentPattern.append (hR₂pat τ) hQpat hR₂Q
    convert this using 1
    funext x
    induction x using Fin.addCases with
    | left i => simp [hR', Fin.append_left]
    | right l => simp [hR', Fin.append_right]
  have hR'inf : ∀ x, R' x ≠ cuspInftyBar N := fun x => by
    induction x using Fin.addCases with
    | left i => simpa [hR'] using hR₂inf i
    | right l => simpa [hR'] using hQinf l
  have hR'F : ∀ x, R' x ∈ F := fun x => by
    induction x using Fin.addCases with
    | left i => simpa [hR'] using (hR₂mem i).1
    | right l => simpa [hR'] using hQF l
  have hdisj : ∀ i x, R i ≠ R' x := fun i x h => (hRmem i).1 (h ▸ hR'F x)

  have hJ : jetDivisor R + jetDivisor R' = D + ∑ l, Finsupp.single (Q l) (1 : ℤ) := by
    rw [hR', AlgebraicCurve.jetDivisor_append, hRdiv, hR₂div, ← add_assoc, add_comm Dmov Dfix, hDsplit]
    rfl

  have hmass : (m : ℤ) + m₂ = offBaseMass N D := by
    rw [← hRmass, ← hR₂mass, ← hDsplit]
    simp only [offBaseMass, Finsupp.erase_add, add_comm]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  have hMg' : m + (m₂ + n') = g := by
    have : (m : ℤ) + (m₂ + n') = g := by rw [← hMg, ← hmass]; ring
    exact_mod_cast this

  set T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := D.support ∪ Finset.univ.image Q with hT
  have hRT : ∀ i, R i ∈ T := fun i => Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr (hRmem i).2)
  have hR'T : ∀ x, R' x ∈ T := fun x => by
    induction x using Fin.addCases with
    | left i => rw [hR', Fin.append_left]; exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr (hR₂mem i).2)
    | right l => rw [hR', Fin.append_right]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem Q (Finset.mem_univ l))
  have hsuppcard : (D.support.card : ℤ) ≤ offBaseMass N D := by
    rw [offBaseMass, herase, Finsupp.sum, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    have h1 : D v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have h2 := heff v
    push_cast; omega
  have hTcard : T.card < Fintype.card (Fin (g + 1)) := by
    rw [Fintype.card_fin]
    have h1 : T.card ≤ D.support.card + n' :=
      (Finset.card_union_le _ _).trans (by
        gcongr
        exact Finset.card_image_le.trans (by simp))
    have h2 : (D.support.card : ℤ) + n' ≤ g := by linarith
    omega
  obtain ⟨a, ha⟩ := ConfGlue.exists_disjoint_of_card_lt T (fun a => ((Bc a).support).erase (cuspInftyBar N))
    (fun a a' haa' => Finset.disjoint_left.mpr fun w hw hw' => by
      have hw1 := Finset.mem_erase.mp hw; have hw2 := Finset.mem_erase.mp hw'
      exact hsep a a' haa' w hw1.1 ⟨by
        have := Finsupp.mem_support_iff.mp hw1.2; have h0 := hBc_nonneg a w; rw [hBc_apply] at this h0
        show 0 < w.ord (h a) + (E2 - K₀) w
        simp only [Finsupp.coe_sub, Pi.sub_apply] at this h0 ⊢; omega, by
        have := Finsupp.mem_support_iff.mp hw2.2; have h0 := hBc_nonneg a' w; rw [hBc_apply] at this h0
        show 0 < w.ord (h a') + (E2 - K₀) w
        simp only [Finsupp.coe_sub, Pi.sub_apply] at this h0 ⊢; omega⟩) hTcard
  have hBcT : ∀ v ∈ T, v ≠ cuspInftyBar N → Bc a v = 0 := by
    intro v hv hvinf
    by_contra hne
    exact Finset.disjoint_left.mp ha hv (Finset.mem_erase.mpr ⟨hvinf, Finsupp.mem_support_iff.mpr hne⟩)
  have hBcR : ∀ i, Bc a (R i) = 0 := fun i => hBcT _ (hRT i) (hRinf i)
  have hBcR' : ∀ x, Bc a (R' x) = 0 := fun x => hBcT _ (hR'T x) (hR'inf x)

  have hRj : ∀ i, (ConfChild2.jElt N : modularFunctionFieldBar N) ∈ (R i).toValuationSubring :=
    fun i => hFnc _ (hRmem i).1

  have hcert : riemannRochSpace (canonicalDivisorOf hω - jetDivisor R - jetDivisor R') = ⊥ := by
    rw [sub_sub, hJ, ← sub_sub]; exact hQbot

  set σ : Fin (m + (m₂ + n')) ≃ Fin g := finCongr hMg' with hσ
  set uσ : Fin (m + (m₂ + n')) → modularFunctionFieldBar N := fun j => u a (σ j) with huσ
  set cσ : Fin (m + (m₂ + n')) → (Fin 2 → Fin r) → AlgebraicClosure ℚ := fun j => cpres a (σ j) with hcσdef
  have huσ0 : ∀ j, uσ j ≠ 0 := fun j => hu0 a (σ j)
  have hcσ : ∀ j, uσ j = ∑ φ : Fin 2 → Fin r, cσ j φ • ∏ l, s (φ l) := fun j => hcpres a (σ j)
  have hHσ : absLogHeight (fun q : Fin (m + (m₂ + n')) × (Fin 2 → Fin r) => cσ q.1 q.2) ≤ H := by
    have hre := ConfGlue.absLogHeight_comp_equiv (fun q : Fin g × (Fin 2 → Fin r) => cpres a q.1 q.2)
      (σ.prodCongr (Equiv.refl (Fin 2 → Fin r)))
    have hfun : (fun q : Fin (m + (m₂ + n')) × (Fin 2 → Fin r) => cσ q.1 q.2)
        = (fun q : Fin g × (Fin 2 → Fin r) => cpres a q.1 q.2) ∘ (σ.prodCongr (Equiv.refl (Fin 2 → Fin r))) := by
      funext q; simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, hcσdef]
    rw [hfun, hre]
    exact hH a (Finset.mem_univ a)
  have hBuσ : ∀ j w, Bc a w ≤ w.ord (uσ j) + ((2 : ℤ) • embDivisor N) w := fun j w => hBcu a (σ j) w

  have hrat : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v.IsRational := fun v =>
    (Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v)
  have hunit := ConfCore.isUnit_det_jetMatrix_frame N hω f hfK hfli (h a) (hh0 a) (Bc a)
    (fun v => by rw [hBc_apply]) σ uσ (fun j => rfl) τ hτ R e R' e' (hRpat τ) hpatF hdisj hRinf hR'inf
    hBcR hBcR' hrat (by rw [← sub_sub]; exact hcert)

  have hpat : IsConfluentPattern (Fin.append R R') (Fin.append (fun i => τ (R i)) (fun x => τ (R' x)))
      (Fin.append e e') := AlgebraicCurve.IsConfluentPattern.append (hRpat τ) hpatF hdisj
  have hm_le : m < g + 1 := by omega
  have hm'_le : m₂ + n' < g + 1 := by omega
  have hRj' : ∀ i, (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
        ∈ (R i).toValuationSubring := fun i => hRj i
  have hL := hCled (⟨m, hm_le⟩, ⟨m₂ + n', hm'_le⟩) uσ cσ huσ0 hcσ hHσ (Bc a) (hBc_nonneg a) hBuσ
    R (fun i => τ (R i)) e R' (fun x => τ (R' x)) e' hpat hdisj hRinf hR'inf hRj' hBcR hBcR'
    (fun i _ => hτ _) (fun x _ => hτ _) hunit
  have hCLp := hCL (⟨m, hm_le⟩, ⟨m₂ + n', hm'_le⟩) (Finset.mem_univ _)

  set Smov := D.support.filter (fun v => v ∉ F) with hSmov
  set Sfix := D.support.filter (fun v => v ∈ F) with hSfix
  have hRS : ∀ i, R i ∈ Smov := fun i => Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (hRmem i).2, (hRmem i).1⟩
  have hR₂S : ∀ i, R₂ i ∈ Sfix := fun i => Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (hR₂mem i).2, (hR₂mem i).1⟩
  have hmultM : ∀ v ∈ Smov, (jetMult R v : ℝ) = (D v : ℝ) := fun v hv => by
    have h1 := jetDivisor_apply R v
    rw [hRdiv, hDmov_apply, if_pos (Finset.mem_filter.mp hv).2] at h1
    exact_mod_cast h1.symm
  have hmultF : ∀ v ∈ Sfix, (jetMult R₂ v : ℝ) = (D v : ℝ) := fun v hv => by
    have h1 := jetDivisor_apply R₂ v
    rw [hR₂div, hDfix_apply, if_pos (Finset.mem_filter.mp hv).2] at h1
    exact_mod_cast h1.symm

  set tt : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ := fun v => baseHt s (cuspInftyBar N) v with htt
  set TM1 : ℝ := ∑ v ∈ Smov, (D v : ℝ) * tt v with hTM1
  set TM2 : ℝ := ∑ v ∈ Smov, (D v : ℝ) * ((D v : ℝ) - 1) / 2 * tt v with hTM2
  set SPT : ℝ := ∑ v ∈ Smov, (D v : ℝ) * pointHt s v with hSPT
  set SDER : ℝ := ∑ v ∈ Smov, (D v : ℝ) * ((D v : ℝ) - 1) / 2 * (ConfChild2.tangentHt N s v (τ v) - 2 * pointHt s v) with hSDER
  set SMM : ℝ := ∑ v ∈ Smov, ∑ w ∈ Smov.erase v, (D v : ℝ) * (D w : ℝ) * pairHt s v w with hSMM
  set SMF : ℝ := ∑ v ∈ Smov, ∑ w ∈ Sfix, (D v : ℝ) * (D w : ℝ) * pairHt s v w with hSMF
  set SFF : ℝ := ∑ v ∈ Sfix, ∑ w ∈ Sfix.erase v, (D v : ℝ) * (D w : ℝ) * pairHt s v w with hSFF
  set SQ : ℝ := ∑ v ∈ Smov, (D v : ℝ) * ∑ l, pairHt s v (Q l) with hSQ
  set SB : ℝ := ∑ v ∈ Smov, (D v : ℝ) * (Bc a).sum (fun w k => (k : ℝ) * pairHt s v w) with hSB
  set WF : ℝ := ∑ v ∈ Sfix, ((((g : ℝ) + (offBaseMass N D : ℝ) - 2 + ε) * (D v : ℝ)
            + (2 * (g : ℝ) - 2) * ((D v : ℝ) * ((D v : ℝ) - 1) / 2)) * tt v) with hWF

  have hL1 : (∑ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i), pairHt s (R i) (R i')) = SMM := by
    have inner : ∀ i : Fin m, ∑ i' ∈ Finset.univ.filter (fun i' : Fin m => R i' ≠ R i), pairHt s (R i) (R i')
        = ∑ w ∈ Smov.erase (R i), (D w : ℝ) * pairHt s (R i) w := by
      intro i
      rw [Finset.sum_filter, AlgebraicCurve.sum_rows_eq_sum_jetMult R Smov hRS (fun w => if w ≠ R i then pairHt s (R i) w else 0)]
      have hpt : ∀ w ∈ Smov, (jetMult R w : ℝ) * (if w ≠ R i then pairHt s (R i) w else 0)
          = if w ∈ Smov.erase (R i) then (D w : ℝ) * pairHt s (R i) w else 0 := by
        intro w hw
        by_cases hwi : w = R i
        · rw [if_neg (not_not.mpr hwi), if_neg (fun h => (Finset.mem_erase.mp h).1 hwi), mul_zero]
        · rw [if_pos hwi, if_pos (Finset.mem_erase.mpr ⟨hwi, hw⟩), hmultM w hw]
      rw [Finset.sum_congr rfl hpt, Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.erase_subset _ _)]
    simp_rw [inner]
    rw [AlgebraicCurve.sum_rows_eq_sum_jetMult R Smov hRS (fun v => ∑ w ∈ Smov.erase v, (D w : ℝ) * pairHt s v w)]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hmultM v hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring

  have hL2 : (∑ i : Fin m, ∑ x : Fin (m₂ + n'), pairHt s (R i) (R' x)) = SMF + SQ := by
    have inner : ∀ i : Fin m, ∑ x : Fin (m₂ + n'), pairHt s (R i) (R' x)
        = ∑ w ∈ Sfix, (D w : ℝ) * pairHt s (R i) w + ∑ l, pairHt s (R i) (Q l) := by
      intro i
      rw [hR', Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [AlgebraicCurve.sum_rows_eq_sum_jetMult R₂ Sfix hR₂S (fun w => pairHt s (R i) w)]
      exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun w hw => by rw [hmultF w hw]) rfl
    simp_rw [inner]
    rw [Finset.sum_add_distrib, AlgebraicCurve.sum_rows_eq_sum_jetMult R Smov hRS (fun v => ∑ w ∈ Sfix, (D w : ℝ) * pairHt s v w),
      AlgebraicCurve.sum_rows_eq_sum_jetMult R Smov hRS (fun v => ∑ l, pairHt s v (Q l))]
    congr 1
    · refine Finset.sum_congr rfl fun v hv => ?_
      rw [hmultM v hv, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    · exact Finset.sum_congr rfl fun v hv => by rw [hmultM v hv]

  have hL3 : (∑ i : Fin m, (Bc a).sum (fun w k => (k : ℝ) * pairHt s (R i) w)) = SB := by
    rw [AlgebraicCurve.sum_rows_eq_sum_jetMult R Smov hRS (fun v => (Bc a).sum (fun w k => (k : ℝ) * pairHt s v w))]
    exact Finset.sum_congr rfl fun v hv => by rw [hmultM v hv]

  have hL4 : (∑ i : Fin m, ((((2 : ℕ) : ℝ) - 2 * (e i : ℝ)) * pointHt s (R i)
              + (e i : ℝ) * absLogHeight (fun p : Fin r × Fin r =>
                  regVal s (R i) (τ (R i)) 1 1 (evalVec s (R i) p.1 • s p.2 - evalVec s (R i) p.2 • s p.1))))
      = 2 * SPT + SDER := by
    have h1 := AlgebraicCurve.sum_rows_eq_sum_jetMult R Smov hRS (fun v => pointHt s v)
    have h2 := AlgebraicCurve.sum_rows_orders_eq_sum_jetMult (hRpat τ) Smov hRS (fun v => pointHt s v)
    have h3 := AlgebraicCurve.sum_rows_orders_eq_sum_jetMult (hRpat τ) Smov hRS (fun v => ConfChild2.tangentHt N s v (τ v))
    have hsplit : (∑ i : Fin m, ((((2 : ℕ) : ℝ) - 2 * (e i : ℝ)) * pointHt s (R i)
              + (e i : ℝ) * absLogHeight (fun p : Fin r × Fin r =>
                  regVal s (R i) (τ (R i)) 1 1 (evalVec s (R i) p.1 • s p.2 - evalVec s (R i) p.2 • s p.1))))
        = 2 * ∑ i : Fin m, pointHt s (R i) - 2 * ∑ i : Fin m, (e i : ℝ) * pointHt s (R i)
          + ∑ i : Fin m, (e i : ℝ) * ConfChild2.tangentHt N s (R i) (τ (R i)) := by
      simp only [ConfChild2.tangentHt, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    rw [hsplit, h1, h2, h3, hSPT, hSDER, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [hmultM v hv]; ring

  have hL5 : (∑ x : Fin (m₂ + n'), absLogHeight (fun j : Fin (m + (m₂ + n')) =>
      (R' x).taylorCoeff (τ (R' x)) (e' x) (uσ j))) ≤ (g : ℝ) * Cfix := by
    have hx : ∀ x : Fin (m₂ + n'), absLogHeight (fun j : Fin (m + (m₂ + n')) =>
        (R' x).taylorCoeff (τ (R' x)) (e' x) (uσ j)) ≤ Cfix := by
      intro x
      have hre := ConfGlue.absLogHeight_comp_equiv
        (fun j : Fin g => (R' x).taylorCoeff (τ (R' x)) (e' x) (u a j)) σ
      have hfun : (fun j : Fin (m + (m₂ + n')) => (R' x).taylorCoeff (τ (R' x)) (e' x) (uσ j))
          = (fun j : Fin g => (R' x).taylorCoeff (τ (R' x)) (e' x) (u a j)) ∘ σ := by
        funext j; simp only [Function.comp_apply, huσ]
      rw [hfun, hre]
      have he'le : e' x ≤ g := by
        have := hpatF.2.2 x
        have hle : jetMult R' (R' x) ≤ m₂ + n' := by
          unfold jetMult; exact (Finset.card_filter_le _ _).trans_eq (by simp)
        omega
      exact hCfix (a, R' x, e' x) (Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_product.mpr ⟨hR'F x, Finset.mem_range.mpr (Nat.lt_succ_of_le he'le)⟩⟩)
    calc (∑ x : Fin (m₂ + n'), absLogHeight (fun j : Fin (m + (m₂ + n')) =>
            (R' x).taylorCoeff (τ (R' x)) (e' x) (uσ j)))
        ≤ ∑ _x : Fin (m₂ + n'), Cfix := Finset.sum_le_sum fun x _ => hx x
      _ = (m₂ + n' : ℕ) * Cfix := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (g : ℝ) * Cfix := by gcongr; exact_mod_cast (by omega : m₂ + n' ≤ g)

  have hLagg : SMM / 2 + SMF + SQ + SB ≤ 2 * SPT + SDER + (CL + (g : ℝ) * Cfix) := by
    have := hL
    rw [hL1, hL2, hL3, hL4] at this
    linarith only [this, hL5, hCLp]

  have hDpos : ∀ v ∈ Smov, (0 : ℝ) ≤ (D v : ℝ) := fun v _ => by exact_mod_cast heff v
  have hSmov_inf : ∀ v ∈ Smov, v ≠ cuspInftyBar N := fun v hv hv0 =>
    (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hv).1) (hv0 ▸ hinf)
  have hMR : (offBaseMass N D : ℝ) = ∑ v ∈ D.support, (D v : ℝ) := by
    rw [offBaseMass, herase, Finsupp.sum]; push_cast; rfl
  have hMsplit : (∑ v ∈ Smov, (D v : ℝ)) + (∑ v ∈ Sfix, (D v : ℝ)) = (offBaseMass N D : ℝ) := by
    rw [hMR, hSmov, hSfix, Finset.sum_filter_not_add_sum_filter]
  have hMg_real : (offBaseMass N D : ℝ) ≤ g := by
    have : (offBaseMass N D : ℤ) ≤ g := by linarith only [hMg, Int.natCast_nonneg n']
    exact_mod_cast this
  have hM2_real : (2 : ℝ) ≤ (offBaseMass N D : ℝ) := by exact_mod_cast hm2
  have hMmov_le : (∑ v ∈ Smov, (D v : ℝ)) ≤ g := by
    have h2 : (0 : ℝ) ≤ ∑ v ∈ Sfix, (D v : ℝ) := Finset.sum_nonneg fun v _ => by exact_mod_cast heff v
    linarith only [hMsplit, hMg_real, h2]
  have hMmov_nn : (0 : ℝ) ≤ ∑ v ∈ Smov, (D v : ℝ) := Finset.sum_nonneg hDpos
  have hC2nn : ∀ v ∈ Smov, (0 : ℝ) ≤ (D v : ℝ) * ((D v : ℝ) - 1) / 2 := by
    intro v hv
    have h1 : (1 : ℤ) ≤ D v := by
      have := Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hv).1; have := heff v; omega
    have h1' : (1 : ℝ) ≤ (D v : ℝ) := by exact_mod_cast h1
    nlinarith only [h1']
  have hC2le : ∀ v ∈ Smov, (D v : ℝ) * ((D v : ℝ) - 1) / 2 ≤ ((g : ℝ) - 1) / 2 * (D v : ℝ) := by
    intro v hv
    have hDle : (D v : ℝ) ≤ g := le_trans (Finset.single_le_sum (fun w hw => hDpos w hw) hv) hMmov_le
    have h0 := hDpos v hv
    nlinarith only [hDle, h0]
  have hTM2le : (∑ v ∈ Smov, (D v : ℝ) * ((D v : ℝ) - 1) / 2) ≤ (g : ℝ) * g := by
    calc (∑ v ∈ Smov, (D v : ℝ) * ((D v : ℝ) - 1) / 2) ≤ ∑ v ∈ Smov, ((g : ℝ) - 1) / 2 * (D v : ℝ) :=
          Finset.sum_le_sum hC2le
      _ = ((g : ℝ) - 1) / 2 * ∑ v ∈ Smov, (D v : ℝ) := by rw [Finset.mul_sum]
      _ ≤ (g : ℝ) * g := by nlinarith only [hMmov_le, hMmov_nn, (Nat.cast_nonneg g : (0:ℝ) ≤ g)]
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hgpos

  have htt_low : ∀ v, -Cbf ≤ tt v := fun v => hCbf (cuspInftyBar N) v

  have hdeg : (embDegree N : ℝ) = 2 * (g : ℝ) + 1 := by
    have : embDegree N = 2 * genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) + 1 := rfl
    rw [this]; push_cast; rw [hg]
  have hPT : SPT ≤ (2 * (g : ℝ) + 1) * TM1 + g * |Cpt| := by
    calc SPT ≤ ∑ v ∈ Smov, (D v : ℝ) * ((2 * (g : ℝ) + 1) * tt v + |Cpt|) := by
          refine Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left ?_ (hDpos v hv)
          have := hCpt v (hSmov_inf v hv); rw [hdeg] at this; linarith only [this, le_abs_self Cpt]
      _ = (2 * (g : ℝ) + 1) * TM1 + (∑ v ∈ Smov, (D v : ℝ)) * |Cpt| := by
          rw [hTM1, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ (2 * (g : ℝ) + 1) * TM1 + g * |Cpt| := by gcongr

  have hDER : SDER ≤ (2 * (g : ℝ) - 2 + ε₁) * TM2 + (g : ℝ) * g * |Cder| := by
    calc SDER ≤ ∑ v ∈ Smov, (D v : ℝ) * ((D v : ℝ) - 1) / 2 * ((2 * (g : ℝ) - 2 + ε₁) * tt v + |Cder|) := by
          refine Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left ?_ (hC2nn v hv)
          have := hCder v (τ v) (hSmov_inf v hv) (hτ v)
          simp only [ConfChild2.tangentHt]
          rw [← hg] at this
          linarith only [this, le_abs_self Cder]
      _ = (2 * (g : ℝ) - 2 + ε₁) * TM2 + (∑ v ∈ Smov, (D v : ℝ) * ((D v : ℝ) - 1) / 2) * |Cder| := by
          rw [hTM2, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ (2 * (g : ℝ) - 2 + ε₁) * TM2 + (g : ℝ) * g * |Cder| := by gcongr

  have hS4aW : ∀ w₀ ∈ W, ∀ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), u ≠ w₀ → u ≠ cuspInftyBar N →
      (1 - ε₁) * tt u - CW ≤ pairHt s u w₀ := fun w₀ hw₀ u hu huinf => by
    have := hCS4 w₀ u hu huinf; linarith only [this, hCW w₀ hw₀]
  have hQW : ∀ l, Q l ∈ W := fun l => Finset.mem_union_left _ (hQF l)
  have hQ : ((g : ℝ) - (offBaseMass N D : ℝ)) * (1 - ε₁) * TM1 - (g : ℝ) * g * CW ≤ SQ := by
    have hn'R : (n' : ℝ) = (g : ℝ) - (offBaseMass N D : ℝ) := by
      have : (n' : ℤ) = g - offBaseMass N D := by linarith only [hMg]
      exact_mod_cast this
    calc ((g : ℝ) - (offBaseMass N D : ℝ)) * (1 - ε₁) * TM1 - (g : ℝ) * g * CW
        ≤ (n' : ℝ) * (1 - ε₁) * TM1 - (∑ v ∈ Smov, (D v : ℝ)) * n' * CW := by
          rw [hn'R]
          have : (∑ v ∈ Smov, (D v : ℝ)) * ((g : ℝ) - offBaseMass N D) ≤ (g : ℝ) * g := by
            nlinarith only [hMmov_le, hMmov_nn, hMg_real, hM2_real]
          nlinarith only [this, hCW0]
      _ = ∑ v ∈ Smov, (D v : ℝ) * ∑ _l : Fin n', ((1 - ε₁) * tt v - CW) := by
          rw [hTM1]; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum, Finset.sum_mul,
            ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ SQ := by
          refine Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) (hDpos v hv)
          exact hS4aW (Q l) (hQW l) v
            (fun h => (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hv).1) (h ▸ hQD l)) (hSmov_inf v hv)

  have hdegBc : ((Bc a).sum fun _ k => (k : ℝ)) = 2 * (g : ℝ) + 4 := by

    have hdegE : Divisor.degree (embDivisor N) = 2 * (g : ℤ) + 1 := by
      show Divisor.degree ((embDegree N : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) = _
      rw [map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N]
      simp [embDegree, hg]
    have hdegK : Divisor.degree K₀ = 2 * (g : ℤ) - 2 := by
      rw [hK₀, ModularCurve.degree_canonicalDivisorOf_modularFunctionFieldBar N hω,
        ModularCurve.genus_eq_genusFF_modularFunctionFieldBar N]
    have hdegB : Divisor.degree (Bc a) = 2 * (g : ℤ) + 4 := by
      rw [hBc, map_sub, map_add, hDhdeg a, hE2, map_zsmul, hdegE, hdegK]; ring
    have hsumdeg : Divisor.degree (Bc a) = (Bc a).sum fun _ k => k := by
      conv_lhs => rw [← Finsupp.sum_single (Bc a)]
      rw [Finsupp.sum, map_sum, Finsupp.sum]
      exact Finset.sum_congr rfl fun v _ => by rw [Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N]; ring
    have : ((Bc a).sum fun _ k => (k : ℝ)) = ((((Bc a).sum fun _ k => k) : ℤ) : ℝ) := by
      rw [Finsupp.sum, Finsupp.sum]; push_cast; rfl
    rw [this, ← hsumdeg, hdegB]; push_cast; ring
  have hBW : ∀ w ∈ (Bc a).support, w ≠ cuspInftyBar N → w ∈ W := fun w hw _ =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hw⟩)
  have hB : (2 * (g : ℝ) + 4) * (1 - ε₁) * TM1 - (g : ℝ) * (2 * g + 4) * (CW + ε₁ * Cbf) ≤ SB := by

    have hper : ∀ v ∈ Smov, (2 * (g : ℝ) + 4) * ((1 - ε₁) * tt v - (CW + ε₁ * Cbf))
        ≤ (Bc a).sum (fun w k => (k : ℝ) * pairHt s v w) := by
      intro v hv
      rw [← hdegBc, Finsupp.sum_mul, Finsupp.sum, Finsupp.sum]
      refine Finset.sum_le_sum fun w hw => ?_
      have hk : (0 : ℝ) ≤ (Bc a w : ℝ) := by exact_mod_cast hBc_nonneg a w
      have hvw : v ≠ w := fun h => (Finsupp.mem_support_iff.mp hw) (h ▸ hBcT v (Finset.mem_union_left _ (Finset.mem_filter.mp hv).1) (hSmov_inf v hv))
      refine mul_le_mul_of_nonneg_left ?_ hk
      by_cases hwinf : w = cuspInftyBar N
      ·
        subst hwinf
        have : pairHt s v (cuspInftyBar N) = tt v := by
          simp only [htt, baseHt, if_neg (hSmov_inf v hv)]
        rw [this]
        have := htt_low v
        nlinarith only [this, hε₁pos.le, hCW0, hCbf0]
      · have := hS4aW w (hBW w hw hwinf) v hvw (hSmov_inf v hv)
        nlinarith only [this, hε₁pos.le, hCbf0]
    calc (2 * (g : ℝ) + 4) * (1 - ε₁) * TM1 - (g : ℝ) * (2 * g + 4) * (CW + ε₁ * Cbf)
        ≤ (2 * (g : ℝ) + 4) * (1 - ε₁) * TM1 - (∑ v ∈ Smov, (D v : ℝ)) * (2 * g + 4) * (CW + ε₁ * Cbf) := by
          have hc : 0 ≤ (2 * (g : ℝ) + 4) * (CW + ε₁ * Cbf) := by positivity
          nlinarith only [hMmov_le, hc]
      _ = ∑ v ∈ Smov, (D v : ℝ) * ((2 * (g : ℝ) + 4) * ((1 - ε₁) * tt v - (CW + ε₁ * Cbf))) := by
          rw [hTM1, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ SB := Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (hper v hv) (hDpos v hv)

  have hMg_int : offBaseMass N D ≤ (g : ℤ) := by linarith only [hMg, Int.natCast_nonneg n']
  obtain ⟨hWF', hFF'⟩ := hCF D (fun v => heff v) hinf hMg_int
  have hWF : |WF| ≤ |CF| := hWF'.trans (le_abs_self CF)
  have hFF : |SFF| ≤ |CF| := hFF'.trans (le_abs_self CF)

  have hT1 : -((g : ℝ) * Cbf) ≤ TM1 := by
    calc -((g : ℝ) * Cbf) ≤ -((∑ v ∈ Smov, (D v : ℝ)) * Cbf) := by nlinarith only [hMmov_le, hCbf0]
      _ = ∑ v ∈ Smov, (D v : ℝ) * (-Cbf) := by rw [Finset.sum_mul, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun v _ => by ring
      _ ≤ TM1 := Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (htt_low v) (hDpos v hv)
  have hT2 : TM2 ≤ ((g : ℝ) - 1) / 2 * TM1 + (g : ℝ) * g * Cbf := by

    have hper : ∀ v ∈ Smov, (D v : ℝ) * ((D v : ℝ) - 1) / 2 * tt v
        ≤ ((g : ℝ) - 1) / 2 * ((D v : ℝ) * tt v) + ((g : ℝ) - 1) / 2 * (D v : ℝ) * Cbf := by
      intro v hv
      have h1 := hC2le v hv; have h2 := hC2nn v hv; have h3 := htt_low v
      have key : 0 ≤ (((g : ℝ) - 1) / 2 * (D v : ℝ) - (D v : ℝ) * ((D v : ℝ) - 1) / 2) * (tt v + Cbf) :=
        mul_nonneg (by linarith only [h1]) (by linarith only [h3])
      nlinarith only [key, mul_nonneg h2 hCbf0]
    calc TM2 ≤ ∑ v ∈ Smov, (((g : ℝ) - 1) / 2 * ((D v : ℝ) * tt v) + ((g : ℝ) - 1) / 2 * (D v : ℝ) * Cbf) :=
          Finset.sum_le_sum hper
      _ = ((g : ℝ) - 1) / 2 * TM1 + ((g : ℝ) - 1) / 2 * (∑ v ∈ Smov, (D v : ℝ)) * Cbf := by
          rw [Finset.sum_add_distrib, hTM1, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      _ ≤ ((g : ℝ) - 1) / 2 * TM1 + (g : ℝ) * g * Cbf := by
          have hle : ((g : ℝ) - 1) / 2 * (∑ v ∈ Smov, (D v : ℝ)) ≤ (g : ℝ) * g := by
            nlinarith only [hMmov_le, hMmov_nn, hg1]
          have := mul_le_mul_of_nonneg_right hle hCbf0
          linarith only [this]

  have hbk := ConfCore.conf_bookkeeping (g : ℝ) (offBaseMass N D : ℝ) ε ε₁ TM1 TM2 SMM SMF SFF WF SQ SB SPT SDER
    (CL + (g : ℝ) * Cfix) |Cpt| ((g : ℝ) * g * |Cder|) ((g : ℝ) * g * CW) ((g : ℝ) * (2 * g + 4) * (CW + ε₁ * Cbf))
    ((g : ℝ) * g * Cbf) |CF| Cbf hM2_real hMg_real (by rw [hε₁]; field_simp) hε₁pos.le (abs_nonneg _) hCbf0
    hLagg hPT hDER hQ hB hFF hWF hT1 hT2

  have hLHS : ((D.erase (cuspInftyBar N)).sum fun v n => ((D.erase (cuspInftyBar N)).erase v).sum fun w k =>
          (n : ℝ) * (k : ℝ) * pairHt s v w) = SMM + 2 * SMF + SFF := by
    rw [herase, ConfGlue.finsupp_sum_erase_sum_eq D (fun v w => pairHt s v w),
      ConfGlue.sum_erase_split D.support F (fun v w => (D v : ℝ) * (D w : ℝ) * pairHt s v w)]
    have hFM : (∑ v ∈ Sfix, ∑ w ∈ Smov, (D v : ℝ) * (D w : ℝ) * pairHt s v w) = SMF := by
      rw [hSMF, Finset.sum_comm]
      exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => by
        rw [AlgebraicCurve.pairHt_comm s v w]; ring
    rw [← hSmov, ← hSfix] at *
    linarith only [hFM]
  have hRHS : ((D.erase (cuspInftyBar N)).sum fun v n =>
            (((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
                + (offBaseMass N D : ℝ) - 2 + ε) * (n : ℝ)
              + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
                * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)
      = ((g : ℝ) + (offBaseMass N D : ℝ) - 2 + ε) * TM1 + (2 * (g : ℝ) - 2) * TM2 + WF := by
    rw [herase, ConfGlue.finsupp_sum_split D F]
    rw [← hSmov, ← hSfix, ← hg]
    have h1 : (∑ v ∈ Smov, (((g : ℝ) + (offBaseMass N D : ℝ) - 2 + ε) * (D v : ℝ)
              + (2 * (g : ℝ) - 2) * ((D v : ℝ) * ((D v : ℝ) - 1) / 2)) * tt v)
        = ((g : ℝ) + (offBaseMass N D : ℝ) - 2 + ε) * TM1 + (2 * (g : ℝ) - 2) * TM2 := by
      rw [hTM1, hTM2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [h1]
  rw [hLHS, hRHS]
  have hKONST' : KONST = CL + (g : ℝ) * Cfix + 2 * (g : ℝ) * |Cpt| + (g : ℝ) * g * |Cder| + (g : ℝ) * g * CW
      + (g : ℝ) * (2 * g + 4) * (CW + ε₁ * Cbf) + 2 * |CF| + ε * g * Cbf + ε₁ * ((g : ℝ) * g * Cbf) := hKONST
  linarith only [hbk, hKONST']

end ConfChild
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

namespace ConfAssembly

open ModularCurve.JZero

variable (N : ℕ) [NeZero N]

theorem heightForm_ge_of_pair_le {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (ε C : ℝ)
    (h : ((D.erase (cuspInftyBar N)).sum fun v n => ((D.erase (cuspInftyBar N)).erase v).sum fun w k =>
          (n : ℝ) * (k : ℝ) * pairHt s v w) / 2
        ≤ ((D.erase (cuspInftyBar N)).sum fun v n =>
            (((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
                + (offBaseMass N D : ℝ) - 2 + ε) * (n : ℝ)
              + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
                * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)
          + C) :
    (1 - ε) * baseMass N s D - C ≤ JZero.heightForm N s D := by
  have hQB := ModularCurve.JZero.heightForm_sub_baseMass_eq N s D
  have hsplit : ((D.erase (cuspInftyBar N)).sum fun v n =>
            (((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
                + (offBaseMass N D : ℝ) - 2 + ε) * (n : ℝ)
              + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
                * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)
      = ((D.erase (cuspInftyBar N)).sum fun v n =>
            (((genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
                + (offBaseMass N D : ℝ) - 2) * (n : ℝ)
              + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 2)
                * ((n : ℝ) * ((n : ℝ) - 1) / 2)) * baseHt s (cuspInftyBar N) v)
        + ε * baseMass N s D := by
    rw [baseMass, Finsupp.mul_sum, ← Finsupp.sum_add]
    exact Finsupp.sum_congr fun v _ => by ring
  rw [hsplit] at h
  linarith

end ConfAssembly
p2m_reactivate "P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le.ConfGlue"

open ModularCurve.JZero in
theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ η C : ℝ, 0 < η ∧ ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ v, 0 ≤ D v) → (∃ v, 2 ≤ D v) → D (cuspInftyBar N) = 0 →
      riemannRochSpace (D.erase (cuspInftyBar N) - Finsupp.single (cuspInftyBar N) (1 : ℤ)) = ⊥ →
      2 ≤ offBaseMass N D →
      η * baseMass N s D - C ≤ heightForm N s D := by
  obtain ⟨C, hC⟩ := ConfChild.star_general N s hs (1 / 2) (by norm_num)
  refine ⟨1 / 2, C, by norm_num, fun D heff _ hinf hbot hm2 => ?_⟩
  have h := ConfAssembly.heightForm_ge_of_pair_le N s D (1 / 2) C (hC D heff hinf hbot hm2)
  norm_num at h ⊢
  linarith

end S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le
end P2MW
export P2MW.S_ModularCurve_JZero_exists_baseMass_le_heightForm_of_exists_two_le (solution)
