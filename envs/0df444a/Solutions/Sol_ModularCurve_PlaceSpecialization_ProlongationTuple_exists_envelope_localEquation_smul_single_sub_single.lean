-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_envelope_localEquation_smul_single_sub_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ae4e7583-6d8b-5c07-8eb1-c1f32eb113f1

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeValueLaw_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv
import Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_eq_modularFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_envelope_localEquation_smul_single_sub_single
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

namespace MOVNCore
section Bookkeeping

variable {α β : Type*}

private theorem mapDomain_apply_eq_sum [DecidableEq β] (E : α →₀ ℤ) (r : α → β) (v : β) :
    Finsupp.mapDomain r E v = ∑ W ∈ E.support, if r W = v then E W else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.single_apply]

private theorem le_mapDomain (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, r W = v → 0 ≤ E W) {V : α} (hV : r V = v) :
    E V ≤ Finsupp.mapDomain r E v := by
  classical
  rw [mapDomain_apply_eq_sum]
  by_cases hs : V ∈ E.support
  · rw [← Finset.add_sum_erase _ _ hs, if_pos hV]
    refine le_add_of_nonneg_right (Finset.sum_nonneg fun W _ => ?_)
    split_ifs with h'
    · exact h W h'
    · exact le_rfl
  · rw [Finsupp.notMem_support_iff.mp hs]
    exact Finset.sum_nonneg fun W _ => by
      split_ifs with h'
      · exact h W h'
      · exact le_rfl

private theorem add_le_mapDomain (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, r W = v → 0 ≤ E W) {V V' : α} (hne : V ≠ V') (hV : r V = v) (hV' : r V' = v) :
    E V + E V' ≤ Finsupp.mapDomain r E v := by
  classical
  have hEV' : E V' = (E.erase V) V' := by rw [Finsupp.erase_ne (Ne.symm hne)]
  have herase : ∀ W, r W = v → 0 ≤ (E.erase V) W := by
    intro W hW
    by_cases hWV : W = V
    · rw [hWV, Finsupp.erase_same]
    · rw [Finsupp.erase_ne hWV]; exact h W hW
  have hsplit : Finsupp.mapDomain r E v = E V + Finsupp.mapDomain r (E.erase V) v := by
    conv_lhs => rw [← Finsupp.single_add_erase V E]
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
      if_pos hV]
  rw [hsplit, hEV']
  gcongr
  exact le_mapDomain (E.erase V) r v herase hV'

private theorem le_mapDomain_filter (D : α →₀ ℤ) (p : α → Prop) [DecidablePred p] (r : α → β) (v : β)
    (h : ∀ W, p W → r W = v → 0 ≤ D W) {V : α} (hp : p V) (hV : r V = v) :
    D V ≤ Finsupp.mapDomain r (D.filter p) v := by
  have hDV : D V = (D.filter p) V := by rw [Finsupp.filter_apply, if_pos hp]
  rw [hDV]
  refine le_mapDomain _ r v (fun W hW => ?_) hV
  rw [Finsupp.filter_apply]
  split_ifs with hp'
  · exact h W hp' hW
  · exact le_rfl

private theorem add_le_mapDomain_filter (D : α →₀ ℤ) (p : α → Prop) [DecidablePred p] (r : α → β) (v : β)
    (h : ∀ W, p W → r W = v → 0 ≤ D W) {V V' : α} (hne : V ≠ V')
    (hp : p V) (hV : r V = v) (hp' : p V') (hV' : r V' = v) :
    D V + D V' ≤ Finsupp.mapDomain r (D.filter p) v := by
  have hDV : D V = (D.filter p) V := by rw [Finsupp.filter_apply, if_pos hp]
  have hDV' : D V' = (D.filter p) V' := by rw [Finsupp.filter_apply, if_pos hp']
  rw [hDV, hDV']
  refine add_le_mapDomain _ r v (fun W hW => ?_) hne hV hV'
  rw [Finsupp.filter_apply]
  split_ifs with hp''
  · exact h W hp'' hW
  · exact le_rfl

private theorem sum_single_apply {ι : Type*} [Fintype ι] (Q : ι → α) (W : α) [DecidableEq α] :
    (∑ i, Finsupp.single (Q i) (1 : ℤ)) W = ∑ i, if Q i = W then (1 : ℤ) else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.single_apply]

private theorem sum_single_apply_nonneg {ι : Type*} [Fintype ι] (Q : ι → α) (W : α) :
    0 ≤ (∑ i, Finsupp.single (Q i) (1 : ℤ)) W := by
  classical
  rw [sum_single_apply]
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

private theorem sum_single_apply_eq_zero {ι : Type*} [Fintype ι] (Q : ι → α) (W : α) (h : ∀ i, Q i ≠ W) :
    (∑ i, Finsupp.single (Q i) (1 : ℤ)) W = 0 := by
  classical
  rw [sum_single_apply]
  exact Finset.sum_eq_zero fun i _ => if_neg (h i)

private theorem exists_of_sum_single_apply_ne_zero {ι : Type*} [Fintype ι] (Q : ι → α) (W : α)
    (h : (∑ i, Finsupp.single (Q i) (1 : ℤ)) W ≠ 0) : ∃ i, Q i = W := by
  by_contra hne
  push Not at hne
  exact h (sum_single_apply_eq_zero Q W hne)

end Bookkeeping

section PlaceValues

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem HasValue.sub {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨sub_mem hg hg', ?_⟩
  have hx : (⟨g - g', sub_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ - ⟨g', hg'⟩ := rfl
  rw [hx, map_sub, hr, hr', map_sub]

private theorem HasValue.sub_const {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (b : K) :
    v.HasValue (g - algebraMap K F b) (a - b) :=
  HasValue.sub h (v.hasValue_algebraMap b)

private theorem ord_pos_of_hasValue_zero (v : Place K F) {g : F} (hg : g ≠ 0) (h : v.HasValue g 0) :
    0 < v.ord g := by
  have hmem := h.mem
  have hres : IsLocalRing.residue v.toValuationSubring ⟨g, hmem⟩ = 0 := by
    rw [h.residue_eq, map_zero]
  have hmax : (⟨g, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres
  have h0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hmem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax hu

private theorem hasValue_of_ord_sub_pos (v : Place K F) {g : F} {b : K}
    (h : 0 < v.ord (g - algebraMap K F b)) : v.HasValue g b := by
  have hne : g - algebraMap K F b ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : g - algebraMap K F b ∈ v.toValuationSubring := v.mem_of_ord_nonneg hne h.le
  have hmax : (⟨_, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (g - algebraMap K F b) = 0 at h0
    omega
  have hgmem : g ∈ v.toValuationSubring := by
    have : g = (g - algebraMap K F b) + algebraMap K F b := by ring
    rw [this]
    exact add_mem hmem (v.algebraMap_mem' b)
  refine ⟨hgmem, ?_⟩
  have hx : (⟨g, hgmem⟩ : v.toValuationSubring) =
      ⟨_, hmem⟩ + ⟨algebraMap K F b, v.algebraMap_mem' b⟩ := Subtype.ext (by push_cast; ring)
  rw [hx, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add]
  exact v.residue_algebraMap b

private theorem ord_sub_eq_zero_of_hasValue_ne (v : Place K F) {g : F} {a b : K}
    (h : v.HasValue g a) (hab : a ≠ b) : v.ord (g - algebraMap K F b) = 0 :=
  (HasValue.sub_const h b).ord_eq_zero (sub_ne_zero.mpr hab)

private theorem ord_sub_pos_of_hasValue (v : Place K F) {g : F} {b : K}
    (h : v.HasValue g b) (hne : g - algebraMap K F b ≠ 0) : 0 < v.ord (g - algebraMap K F b) := by
  have h' := HasValue.sub_const h b
  rw [sub_self] at h'
  exact ord_pos_of_hasValue_zero v hne h'

private theorem eq_of_ord_sub_pos_of_hasValue (v : Place K F) {g : F} {a b : K}
    (ha : v.HasValue g a) (h : 0 < v.ord (g - algebraMap K F b)) : b = a :=
  (hasValue_of_ord_sub_pos v h).unique ha

private theorem ord_sub_const_nonneg (v : Place K F) {g : F} (hg : g = 0 ∨ 0 ≤ v.ord g) (b : K) :
    0 ≤ v.ord (g - algebraMap K F b) := by
  have hmem : g ∈ v.toValuationSubring := by
    rcases hg with rfl | hg
    · exact zero_mem _
    · by_cases h0 : g = 0
      · rw [h0]; exact zero_mem _
      · exact v.mem_of_ord_nonneg h0 hg
  exact v.ord_nonneg_of_mem (sub_mem hmem (v.algebraMap_mem' b))

private theorem ord_nonneg_of_mem_riemannRochSpace {D : Divisor K F} {g : F} (hg : g ∈ riemannRochSpace D)
    (v : Place K F) (hv : D v = 0) : g = 0 ∨ 0 ≤ v.ord g := by
  have h := (mem_riemannRochSpace_iff.mp hg) v
  rw [hv, neg_zero] at h
  exact h

private theorem riemannRochSpace_mono {D D' : Divisor K F} (h : ∀ v, D v ≤ D' v) :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro g hg
  rw [mem_riemannRochSpace_iff] at hg ⊢
  intro v
  rcases hg v with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (le_trans (neg_le_neg (h v)) h1)

private theorem ord_neg_of_ord_sub_const_neg (v : Place K F) {g : F} {b : K}
    (h : v.ord (g - algebraMap K F b) < 0) : g ≠ 0 ∧ v.ord g < 0 := by
  by_contra hc
  have : g = 0 ∨ 0 ≤ v.ord g := by
    by_cases h0 : g = 0
    · exact Or.inl h0
    · exact Or.inr (not_lt.mp fun hlt => hc ⟨h0, hlt⟩)
  exact absurd (ord_sub_const_nonneg v this b) (not_le.mpr h)

private theorem surjective_algebraMap_residueField [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

private theorem exists_hasValue_of_ord_nonneg [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) {g : F}
    (hg : g = 0 ∨ 0 ≤ v.ord g) : ∃ a : K, v.HasValue g a := by
  have hmem : g ∈ v.toValuationSubring := by
    rcases hg with rfl | hg
    · exact zero_mem _
    · by_cases h0 : g = 0
      · rw [h0]; exact zero_mem _
      · exact v.mem_of_ord_nonneg h0 hg
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective (surjective_algebraMap_residueField v) hmem
  exact ⟨a, ha⟩

private theorem ord_const_mul (v : Place K F) {c : K} (hc : c ≠ 0) (g : F) :
    v.ord (algebraMap K F c * g) = v.ord g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [mul_zero]
  · rw [v.ord_mul ((map_ne_zero _).mpr hc) hg]
    have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
      (v.hasValue_algebraMap c).isUnit hc
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (algebraMap K F c) = 0 at h0
    rw [h0, zero_add]

end PlaceValues

section GeometryN

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

private theorem trichotomy (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.IsStrictFst W ∨ P.IsStrictSnd W ∨
    (φ (φ (P.reduceFst W)) = P.reduceFst W ∧ P.reduceSnd W = φ (P.reduceFst W)) := by
  rcases P.d1 W with h | h
  ·
    change P.reduceFst W = φ (P.reduceSnd W) at h
    by_cases hfix : φ (φ (P.reduceSnd W)) = P.reduceSnd W
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [h, hfix]
      · rw [h, hfix]
    · exact Or.inr (Or.inl ⟨h, hfix⟩)
  · change φ (P.reduceFst W) = P.reduceSnd W at h
    by_cases hfix : φ (φ (P.reduceFst W)) = P.reduceFst W
    · exact Or.inr (Or.inr ⟨hfix, h.symm⟩)
    · exact Or.inl ⟨h, hfix⟩

variable {P}

private theorem not_fixed_reduceFst_of_isStrictFst {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictFst W) : φ (φ (P.reduceFst W)) ≠ P.reduceFst W := h.2

private theorem not_fixed_reduceSnd_of_isStrictSnd {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictSnd W) : φ (φ (P.reduceSnd W)) ≠ P.reduceSnd W := h.2

private theorem not_fixed_reduceFst_of_isStrictSnd {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h : P.IsStrictSnd W) : φ (φ (P.reduceFst W)) ≠ P.reduceFst W := by
  intro hfix
  apply h.2
  have e : P.reduceFst W = φ (P.reduceSnd W) := h.1
  rw [e] at hfix
  exact frobOnPlacesGeomLevel_injective k N data hKr hfix

private theorem not_isStrictSnd_of_isStrictFst {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))}
    (h1 : P.IsStrictFst W) (h2 : P.IsStrictSnd W) : False := by
  apply h2.2
  have e1 : φ (P.reduceFst W) = P.reduceSnd W := h1.1
  have e2 : P.reduceFst W = φ (P.reduceSnd W) := h2.1
  rw [e2] at e1
  exact e1

end GeometryN

section CountN

private theorem ord_algebraMap_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, Place.ord_zero]
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr
set_option hygiene false in
local notation "F" => ↥(modularFunctionFieldBar (N * q))
set_option hygiene false in
local notation "Ck" => ↥(modularFunctionFieldC k N)

variable (P : PlaceSpecialization A q N data hKr k red hα hβ)

private theorem kind
    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) F, ¬ IsAffineGeomPlace k N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) F, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (V : Place (AlgebraicClosure ℚ) F) :
    P.IsStrictFst V ∨ P.IsStrictSnd V ∨
    (φ (φ (P.reduceFst V)) = P.reduceFst V ∧ IsAffineGeomPlace k N (P.reduceFst V) ∧ P.reduceSnd V = φ (P.reduceFst V)) ∨
    (ProlongationTuple.IsInftySide P V ∧ φ (φ (P.reduceFst V)) = P.reduceFst V ∧ P.reduceSnd V = φ (P.reduceFst V)) ∨
    (ProlongationTuple.IsZeroSide P V ∧ φ (φ (P.reduceFst V)) = P.reduceFst V ∧ P.reduceSnd V = φ (P.reduceFst V)) := by
  rcases trichotomy P V with h | h | ⟨hfix, hsnd⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · by_cases haff : IsAffineGeomPlace k N (P.reduceFst V)
    · exact Or.inr (Or.inr (Or.inl ⟨hfix, haff, hsnd⟩))
    · rcases hsplit V (hcusp V haff) with hs | hs
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, hfix, hsnd⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hs, hfix, hsnd⟩)))

variable {P}

variable {D : Divisor (AlgebraicClosure ℚ) F} {Z : Set (Place k Ck)}

private theorem nonneg_fst_fibre
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    {v : Place k Ck} (hv : v ∈ Z) :
    ∀ W, P.IsStrictFst W → P.reduceFst W = v → 0 ≤ D W := by
  intro W h1 hW
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨-, hZ⟩ | ⟨h2, -⟩
  · exact hZ (by rw [hW]; exact hv)
  · exact not_isStrictSnd_of_isStrictFst h1 h2

private theorem nonneg_snd_fibre
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    {v : Place k Ck} (hv : v ∈ Z) :
    ∀ W, P.IsStrictSnd W → P.reduceSnd W = v → 0 ≤ D W := by
  intro W h2 hW
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨h1, -⟩ | ⟨-, hZ⟩
  · exact not_isStrictSnd_of_isStrictFst h1 h2
  · exact hZ (by rw [hW]; exact hv)

private theorem nonneg_fixed_fibre
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    {v : Place k Ck} (hv : φ (φ v) = v) :
    ∀ W, P.reduceFst W = v → 0 ≤ D W := by
  intro W hW
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨h1, -⟩ | ⟨h2, -⟩
  · exact not_fixed_reduceFst_of_isStrictFst h1 (by rw [hW]; exact hv)
  · exact not_fixed_reduceFst_of_isStrictSnd h2 (by rw [hW]; exact hv)

private theorem nonneg_infty_fibre
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (hZcusp : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (c : Place (AlgebraicClosure ℚ) F) :
    ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W = P.reduceFst c → 0 ≤ D W := by
  intro W hW _
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨-, hZ⟩ | ⟨-, hZ⟩
  · exact hZ (hZcusp W hW).1
  · exact hZ (hZcusp W hW).2

private theorem nonneg_zero_fibre
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (hZcusp' : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (c : Place (AlgebraicClosure ℚ) F) :
    ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceSnd W = P.reduceSnd c → 0 ≤ D W := by
  intro W hW _
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨-, hZ⟩ | ⟨-, hZ⟩
  · exact hZ (hZcusp' W hW).1
  · exact hZ (hZcusp' W hW).2

private theorem rawResidue₁_ne_zero (R : ProlongationTuple P) {x : R.R₁.integers} (h : R.residue₁ x ≠ 0) :
    R.R₁.residue x ≠ 0 := by
  intro h0; apply h; rw [ProlongationTuple.residue₁_apply, h0, map_zero]

private theorem rawResidue₂_ne_zero (R : ProlongationTuple P) {x : R.R₂.integers} (h : R.residue₂ x ≠ 0) :
    R.R₂.residue x ≠ 0 := by
  intro h0; apply h; rw [ProlongationTuple.residue₂_apply, h0, map_zero]

private theorem classBound (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) F, ¬ IsAffineGeomPlace k N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) F, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (f : F) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hf₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ W, D W = W.ord f)
    (Z : Set (Place k Ck))
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (hZcusp : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (hZcusp' : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (V : Place (AlgebraicClosure ℚ) F) (hz₁ : P.reduceFst V ∈ Z) (hz₂ : P.reduceSnd V ∈ Z) :
    (P.IsStrictFst V ∧
      D V ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩) ∧
      ∀ V', V' ≠ V → P.IsStrictFst V' → P.reduceFst V' = P.reduceFst V →
        D V + D V' ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩)) ∨
    (P.IsStrictSnd V ∧
      D V ≤ (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩) ∧
      ∀ V', V' ≠ V → P.IsStrictSnd V' → P.reduceSnd V' = P.reduceSnd V →
        D V + D V' ≤ (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩)) ∨
    ((φ (φ (P.reduceFst V)) = P.reduceFst V ∧ IsAffineGeomPlace k N (P.reduceFst V) ∧ P.reduceSnd V = φ (P.reduceFst V)) ∧
      D V ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩) + (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩) ∧
      ∀ V', V' ≠ V → P.reduceFst V' = P.reduceFst V →
        D V + D V' ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩) + (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩)) ∨
    ((ProlongationTuple.IsInftySide P V ∧ φ (φ (P.reduceFst V)) = P.reduceFst V ∧ P.reduceSnd V = φ (P.reduceFst V)) ∧
      D V ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩) ∧
      ∀ V', V' ≠ V → ProlongationTuple.IsInftySide P V' → P.reduceFst V' = P.reduceFst V →
        D V + D V' ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩)) ∨
    ((ProlongationTuple.IsZeroSide P V ∧ φ (φ (P.reduceFst V)) = P.reduceFst V ∧ P.reduceSnd V = φ (P.reduceFst V)) ∧
      D V ≤ (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩) ∧
      ∀ V', V' ≠ V → ProlongationTuple.IsZeroSide P V' → P.reduceSnd V' = P.reduceSnd V →
        D V + D V' ≤ (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩)) := by
  classical
  obtain ⟨hDF, hDS, hCI, hCZ⟩ : R.DivisorLawFst ∧ R.DivisorLawSnd ∧ R.CuspLawInfty ∧ R.CuspLawZero := hR
  have hf₁' : R.R₁.residue ⟨f, h₁⟩ ≠ 0 := rawResidue₁_ne_zero R hf₁
  have hf₂' : R.R₂.residue ⟨f, h₂⟩ ≠ 0 := rawResidue₂_ne_zero R hf₂
  rcases kind P hcusp hsplit V with hk | hk | hk | hk | hk
  · have hlaw := hDF f h₁ h₂ hf₁' hf₂' D hD (P.reduceFst V) hk.2
    refine Or.inl ⟨hk, ?_, ?_⟩
    · rw [← hlaw]
      exact le_mapDomain_filter D P.IsStrictFst P.reduceFst _ (nonneg_fst_fibre hDpole hz₁) hk rfl
    · intro V' hne h1' hV'
      rw [← hlaw]
      exact add_le_mapDomain_filter D P.IsStrictFst P.reduceFst _
        (nonneg_fst_fibre hDpole hz₁) (Ne.symm hne) hk rfl h1' hV'
  · have hlaw := hDS f h₁ h₂ hf₁' hf₂' D hD (P.reduceSnd V) hk.2
    refine Or.inr (Or.inl ⟨hk, ?_, ?_⟩)
    · rw [← hlaw]
      exact le_mapDomain_filter D P.IsStrictSnd P.reduceSnd _ (nonneg_snd_fibre hDpole hz₂) hk rfl
    · intro V' hne h2' hV'
      rw [← hlaw]
      exact add_le_mapDomain_filter D P.IsStrictSnd P.reduceSnd _
        (nonneg_snd_fibre hDpole hz₂) (Ne.symm hne) hk rfl h2' hV'
  · obtain ⟨hfix, haff, hsnd⟩ := hk
    have hlaw := hO f h₁ h₂ hf₁' hf₂' D hD (P.reduceFst V) hfix haff
    refine Or.inr (Or.inr (Or.inl ⟨⟨hfix, haff, hsnd⟩, ?_, ?_⟩))
    · rw [hsnd, ← hlaw]
      exact le_mapDomain D P.reduceFst _ (nonneg_fixed_fibre hDpole hfix) rfl
    · intro V' hne hV'
      rw [hsnd, ← hlaw]
      exact add_le_mapDomain D P.reduceFst _ (nonneg_fixed_fibre hDpole hfix) (Ne.symm hne) rfl hV'
  · have hlaw := hCI f h₁ h₂ hf₁' hf₂' D hD V hk.1
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, ?_, ?_⟩)))
    · rw [← hlaw]
      exact le_mapDomain_filter D (ProlongationTuple.IsInftySide P) P.reduceFst _
        (nonneg_infty_fibre hDpole hZcusp V) hk.1 rfl
    · intro V' hne hs' hV'
      rw [← hlaw]
      exact add_le_mapDomain_filter D (ProlongationTuple.IsInftySide P) P.reduceFst _
        (nonneg_infty_fibre hDpole hZcusp V) (Ne.symm hne) hk.1 rfl hs' hV'
  · have hlaw := hCZ f h₁ h₂ hf₁' hf₂' D hD V hk.1
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hk, ?_, ?_⟩)))
    · rw [← hlaw]
      exact le_mapDomain_filter D (ProlongationTuple.IsZeroSide P) P.reduceSnd _
        (nonneg_zero_fibre hDpole hZcusp' V) hk.1 rfl
    · intro V' hne hs' hV'
      rw [← hlaw]
      exact add_le_mapDomain_filter D (ProlongationTuple.IsZeroSide P) P.reduceSnd _
        (nonneg_zero_fibre hDpole hZcusp' V) (Ne.symm hne) hk.1 rfl hs' hV'

end CountN

section ZeroCountN

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr
set_option hygiene false in
local notation "F" => ↥(modularFunctionFieldBar (N * q))
set_option hygiene false in
local notation "Ck" => ↥(modularFunctionFieldC k N)

private theorem one_le_ord_residue_or (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) F, ¬ IsAffineGeomPlace k N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) F, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (f : F) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hf₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) F) (hD : ∀ W, D W = W.ord f)
    (Z : Set (Place k Ck))
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (hZcusp : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (hZcusp' : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (V₀ : Place (AlgebraicClosure ℚ) F) (hDV₀ : 1 ≤ D V₀)
    (hd₁ : P.reduceFst V₀ ∈ Z) (hd₂ : P.reduceSnd V₀ ∈ Z)
    (hreg₁ : 0 ≤ (P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩))
    (hreg₂ : 0 ≤ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩)) :
    1 ≤ (P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩) ∨ 1 ≤ (P.reduceSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) := by
  rcases classBound R hR hO hcusp hsplit f h₁ h₂ hf₁ hf₂ D hD Z hDpole hZcusp hZcusp' V₀ hd₁ hd₂ with
    ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩
  · exact Or.inl (hDV₀.trans hb)
  · exact Or.inr (hDV₀.trans hb)
  · rcases le_or_gt 1 ((P.reduceFst V₀).ord (R.residue₁ ⟨f, h₁⟩)) with h | h
    · exact Or.inl h
    · right; omega
  · exact Or.inl (hDV₀.trans hb)
  · exact Or.inr (hDV₀.trans hb)

end ZeroCountN

section SeamN

private theorem residue_inv_eq_zero_of_not_mem {A : ValuationSubring (AlgebraicClosure ℚ)} {c : AlgebraicClosure ℚ} (hc : c ∉ A) (hc' : c⁻¹ ∈ A) :
    IsLocalRing.residue A ⟨c⁻¹, hc'⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  apply hc
  have hc0 : c ≠ 0 := fun h0 => hc (h0 ▸ A.zero_mem)
  have h1 : c⁻¹ * (w : AlgebraicClosure ℚ) = 1 := by
    have := congrArg Subtype.val hw
    simpa using this
  have : (w : AlgebraicClosure ℚ) = c := by
    calc (w : AlgebraicClosure ℚ) = c * (c⁻¹ * w) := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      _ = c := by rw [h1, mul_one]
  rw [← this]
  exact w.2

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  [CharP (ResidueField A) q]
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
  (R : ProlongationTuple P)

private theorem redBar_eq_id : R.redBar = RingHom.id (ResidueField A) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  exact R.redBar_residue a

private theorem coeffMap_id' (y : LaurentSeries (ResidueField A)) : coeffMap (RingHom.id (ResidueField A)) y = y := by
  ext n; rfl

private theorem coe_ι (g : ↥(modularFunctionFieldFullC (ResidueField A) N)) :
    ((R.ι g : ↥(modularFunctionFieldC (ResidueField A) N)) : LaurentSeries (ResidueField A)) =
      (g : LaurentSeries (ResidueField A)) := by
  rw [R.ι_coe, redBar_eq_id, coeffMap_id']

private theorem ι_algebraMap (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N) c)
      = algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) c := by
  apply Subtype.ext
  rw [coe_ι]
  exact ((IsScalarTower.algebraMap_apply (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N)
        (LaurentSeries (ResidueField A)) c).symm.trans
      (IsScalarTower.algebraMap_apply (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)
        (LaurentSeries (ResidueField A)) c))

private theorem algebraMap_mem_integers₁ (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
  (R.R₁.algebraMap_mem_iff a).mpr a.2

private theorem algebraMap_mem_integers₂ (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
  (R.R₂.algebraMap_mem_iff a).mpr a.2

private theorem residue₁_algebraMap (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h⟩ =
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) := by
  rw [ProlongationTuple.residue₁_apply, ← ι_algebraMap R]
  congr 1
  exact R.R₁.residue_algebraMap a

private theorem residue₂_algebraMap (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h⟩ =
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) := by
  rw [ProlongationTuple.residue₂_apply, ← ι_algebraMap R]
  congr 1
  exact R.R₂.residue_algebraMap a

private theorem residue₁_sub_algebraMap (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₁.integers) (a : A)
    (h' : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h'⟩ = R.residue₁ ⟨f, h⟩ -
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) := by
  rw [← residue₁_algebraMap R a (algebraMap_mem_integers₁ R a), ← map_sub]
  rfl

private theorem residue₂_sub_algebraMap (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₂.integers) (a : A)
    (h' : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h'⟩ = R.residue₂ ⟨f, h⟩ -
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) := by
  rw [← residue₂_algebraMap R a (algebraMap_mem_integers₂ R a), ← map_sub]
  rfl

private theorem residue₁_one_sub_smul (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₁.integers) (a : A)
    (ha : IsLocalRing.residue A a = 0)
    (h' : 1 - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) * f ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h'⟩ = 1 := by
  have hx : (⟨_, h'⟩ : R.R₁.integers) = 1 - ⟨_, algebraMap_mem_integers₁ R a⟩ * ⟨f, h⟩ := rfl
  rw [hx, map_sub, map_one, map_mul, residue₁_algebraMap R a, ha, map_zero, zero_mul, sub_zero]

private theorem residue₂_one_sub_smul (f : ↥(modularFunctionFieldBar (N * q))) (h : f ∈ R.R₂.integers) (a : A)
    (ha : IsLocalRing.residue A a = 0)
    (h' : 1 - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) * f ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h'⟩ = 1 := by
  have hx : (⟨_, h'⟩ : R.R₂.integers) = 1 - ⟨_, algebraMap_mem_integers₂ R a⟩ * ⟨f, h⟩ := rfl
  rw [hx, map_sub, map_one, map_mul, residue₂_algebraMap R a, ha, map_zero, zero_mul, sub_zero]

end SeamN

section CoreN

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  [CharP (ResidueField A) q]
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
  [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))] [DecidableEq (ResidueField A)]

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel (ResidueField A) N data hKr
set_option hygiene false in
local notation "FNq" => ↥(modularFunctionFieldBar (N * q))
set_option hygiene false in
local notation "FN" => ↥(modularFunctionFieldC (ResidueField A) N)
set_option hygiene false in
local notation "PlFN" => Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)

set_option maxHeartbeats 6400000 in

private theorem mem_of_hasValue (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hcusp : ∀ V : Place (AlgebraicClosure ℚ) FNq, ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V) → ProlongationTuple.IsCuspidal P V)
    (hsplit : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsCuspidal P V →
      ProlongationTuple.IsInftySide P V ∨ ProlongationTuple.IsZeroSide P V)
    (hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V))
    (hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) FNq, ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V))
    (hφaff : ∀ v : PlFN, IsAffineGeomPlace (ResidueField A) N v → IsAffineGeomPlace (ResidueField A) N (φ v))
    (Z : Set PlFN)
    (hZcusp : ∀ W, ProlongationTuple.IsInftySide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z)
    (hZcusp' : ∀ W, ProlongationTuple.IsZeroSide P W → P.reduceFst W ∈ Z ∧ P.reduceSnd W ∈ Z) (G : FNq) (hG₁ : G ∈ R.R₁.integers) (hG₂ : G ∈ R.R₂.integers)
    (hGpole : ∀ W : Place (AlgebraicClosure ℚ) FNq, W.ord G < 0 →
      (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z))
    (V₀ : Place (AlgebraicClosure ℚ) FNq) (hd₁ : P.reduceFst V₀ ∈ Z) (hd₂ : P.reduceSnd V₀ ∈ Z)
    (c : AlgebraicClosure ℚ) (hc : V₀.HasValue G c)
    (hf0 : G - algebraMap (AlgebraicClosure ℚ) FNq c ≠ 0) : c ∈ A := by
  classical
  by_contra hcA
  have hc0 : c ≠ 0 := fun h => hcA (by rw [h]; exact A.zero_mem)
  have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  have ha0 := residue_inv_eq_zero_of_not_mem hcA hcinv
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ hf0
  have hDV₀ : 1 ≤ D V₀ := by
    have := ord_sub_pos_of_hasValue V₀ hc hf0
    rw [hD]; omega
  have hDpole : ∀ W, D W < 0 →
      (P.IsStrictFst W ∧ P.reduceFst W ∉ Z) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Z) := by
    intro W hW
    rw [hD] at hW
    exact hGpole W (ord_neg_of_ord_sub_const_neg W hW).2
  set H : FNq := 1 - algebraMap (AlgebraicClosure ℚ) FNq (((⟨c⁻¹, hcinv⟩ : A) : AlgebraicClosure ℚ)) * G
    with hH
  have hH₁ : H ∈ R.R₁.integers := sub_mem (one_mem _) (mul_mem (algebraMap_mem_integers₁ R _) hG₁)
  have hH₂ : H ∈ R.R₂.integers := sub_mem (one_mem _) (mul_mem (algebraMap_mem_integers₂ R _) hG₂)
  have hrH₁ : R.residue₁ ⟨H, hH₁⟩ = 1 := residue₁_one_sub_smul R G hG₁ ⟨c⁻¹, hcinv⟩ ha0 hH₁
  have hrH₂ : R.residue₂ ⟨H, hH₂⟩ = 1 := residue₂_one_sub_smul R G hG₂ ⟨c⁻¹, hcinv⟩ ha0 hH₂
  have hHf : H = algebraMap (AlgebraicClosure ℚ) FNq (-c⁻¹) * (G - algebraMap (AlgebraicClosure ℚ) FNq c) := by
    rw [hH, (algebraMap (AlgebraicClosure ℚ) FNq).map_neg, neg_mul, mul_sub, ← map_mul,
      inv_mul_cancel₀ hc0, map_one, neg_sub]
  have hDH : ∀ W, D W = W.ord H := fun W => by
    rw [hD, hHf, ord_const_mul W (neg_ne_zero.mpr (inv_ne_zero hc0))]
  rcases one_le_ord_residue_or R hR hO hcusp hsplit H hH₁ hH₂ (by rw [hrH₁]; exact one_ne_zero)
      (by rw [hrH₂]; exact one_ne_zero) D hDH Z hDpole hZcusp hZcusp' V₀ hDV₀ hd₁ hd₂
      (show (P.reduceFst V₀).ord (R.residue₁ ⟨H, hH₁⟩) = 0 by rw [hrH₁, Place.ord_one]).ge
      (show (P.reduceSnd V₀).ord (R.residue₂ ⟨H, hH₂⟩) = 0 by rw [hrH₂, Place.ord_one]).ge with h | h
  · rw [hrH₁, Place.ord_one] at h; exact absurd h (by norm_num)
  · rw [hrH₂, Place.ord_one] at h; exact absurd h (by norm_num)

end CoreN

section FrobAffine

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k]
  (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k N data hKr

omit [CharP k q] in

private theorem exists_pow_eq_of_isAlgClosed (c : k) : ∃ d : k, d ^ q = c :=
  IsAlgClosed.exists_pow_nat_eq c (Fact.out : q.Prime).pos

private theorem isAffineGeomPlace_of_frob
    (hfin : {v : Place k ↥(modularFunctionFieldC k N) | ¬ IsAffineGeomPlace k N v}.Finite)
    (hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (v : Place k ↥(modularFunctionFieldC k N)) (h : IsAffineGeomPlace k N (φ v)) : IsAffineGeomPlace k N v := by
  classical
  by_contra hv
  have hinj := ModularCurve.frobOnPlacesGeomLevel_injective k N data hKr
  have hsurj := ModularCurve.frobOnPlacesGeomLevel_surjective k N data hKr (exists_pow_eq_of_isAlgClosed (q := q))
  set S := hfin.toFinset with hS
  have hmemS : ∀ w, w ∈ S ↔ ¬ IsAffineGeomPlace k N w := fun w => by rw [hS, Set.Finite.mem_toFinset]; rfl
  have hsub : S ⊆ S.image φ := by
    intro w hw
    obtain ⟨u, rfl⟩ := hsurj w
    refine Finset.mem_image.mpr ⟨u, ?_, rfl⟩
    rw [hmemS] at hw ⊢
    exact fun hu => hw (hfwd u hu)
  have hcard : (S.image φ).card ≤ S.card := Finset.card_image_le
  have heq : S.image φ = S := (Finset.eq_of_subset_of_card_le hsub hcard).symm
  have hvS : v ∈ S := (hmemS v).mpr hv
  have : φ v ∈ S := by rw [← heq]; exact Finset.mem_image_of_mem _ hvS
  exact ((hmemS _).mp this) h

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {red : A →+* k}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

omit [IsAlgClosed k] in
private theorem not_isAffineGeomPlace_reduceSnd_of_reduceFst
    (hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (hbwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N (φ v) → IsAffineGeomPlace k N v)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (h : ¬ IsAffineGeomPlace k N (P.reduceFst V)) :
    ¬ IsAffineGeomPlace k N (P.reduceSnd V) := by
  intro hs
  rcases P.d1 V with e | e
  · change P.reduceFst V = φ (P.reduceSnd V) at e
    exact h (e ▸ hfwd _ hs)
  · change φ (P.reduceFst V) = P.reduceSnd V at e
    exact h (hbwd _ (e ▸ hs))

omit [IsAlgClosed k] in
private theorem not_isAffineGeomPlace_reduceFst_of_reduceSnd
    (hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (hbwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N (φ v) → IsAffineGeomPlace k N v)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))} (h : ¬ IsAffineGeomPlace k N (P.reduceSnd V)) :
    ¬ IsAffineGeomPlace k N (P.reduceFst V) := by
  intro hs
  rcases P.d1 V with e | e
  · change P.reduceFst V = φ (P.reduceSnd V) at e
    exact h (hbwd _ (e ▸ hs))
  · change φ (P.reduceFst V) = P.reduceSnd V at e
    exact h (e ▸ hfwd _ hs)

omit [IsAlgClosed k] in

private theorem not_isAffineGeomPlace_reduceSnd_of_isInftySide
    (hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (hbwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N (φ v) → IsAffineGeomPlace k N v)
    (hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ProlongationTuple.IsInftySide P V → ¬ IsAffineGeomPlace k N (P.reduceFst V))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : ProlongationTuple.IsInftySide P V) :
    ¬ IsAffineGeomPlace k N (P.reduceSnd V) :=
  not_isAffineGeomPlace_reduceSnd_of_reduceFst data hKr P hfwd hbwd (hInftyNA V hV)

omit [IsAlgClosed k] in

private theorem not_isAffineGeomPlace_reduceFst_of_isZeroSide
    (hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v))
    (hbwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N (φ v) → IsAffineGeomPlace k N v)
    (hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ProlongationTuple.IsZeroSide P V → ¬ IsAffineGeomPlace k N (P.reduceSnd V))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : ProlongationTuple.IsZeroSide P V) :
    ¬ IsAffineGeomPlace k N (P.reduceFst V) :=
  not_isAffineGeomPlace_reduceFst_of_reduceSnd data hKr P hfwd hbwd (hZeroNA V hV)

end FrobAffine

end MOVNCore

section Dict

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

namespace MOVNAsm

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem not_isAffineGeomPlace_reduceSnd_of_isCuspidal'
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : ProlongationTuple.IsCuspidal' P V) :
    ¬ IsAffineGeomPlace k N (P.reduceSnd V) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set jN : modularFunctionFieldBar N :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩ with hjN
  have hβj : heckeBetaBar (AlgebraicClosure ℚ) N q jN = ProlongationTuple.jQFun N q := by
    apply Subtype.ext
    rw [coe_heckeBetaBar]
    show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
    rw [coeffEmb, coeffMap_qExpand]
  have he : 0 < Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) V := by
    letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N q)
    haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) N q)
    haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
    exact V.ramificationIndex_pos (F := modularFunctionFieldBar N)
  have hcusp : ∀ a : A, (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).ord
      (jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro a
    have hle := hV a
    have key := Place.ord_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V
      (jN - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
    rw [map_sub, hβj, AlgHom.commutes] at key
    rw [key] at hle
    by_contra hpos
    push Not at hpos
    exact absurd hle (not_le.mpr (mul_pos (by exact_mod_cast he) hpos))
  have hpole := P.d0_j_pole (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) hcusp
  intro haff
  have h0 := (P.reduceSnd V).ord_nonneg_of_mem haff.1
  exact absurd hpole (not_lt.mpr h0)

end MOVNAsm

end Dict

section Zone

p2m_open "AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~IsCuspidal~IsZeroSide~IsCuspidal'"

namespace MOVNAsm

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]
    {k : Type} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}

omit [DecidableEq k] in
open Classical in

private theorem finite_setOf_not_isAffineGeomPlace :
    {v : Place k ↥(modularFunctionFieldC k N) | ¬ IsAffineGeomPlace k N v}.Finite := by
  classical
  haveI : IsCurveOver k (modularFunctionFieldC k N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  have hj0 : (jGeomGen k N : modularFunctionFieldC k N) ≠ 0 := by
    simpa using jGeomGen_sub_algebraMap_ne_zero k N 0
  have hjN0 : (jNGeomGen k N : modularFunctionFieldC k N) ≠ 0 := by
    simpa using jNGeomGen_sub_algebraMap_ne_zero k N 0
  haveI hPD : HasPrincipalDivisors k (modularFunctionFieldC k N) := IsCurveOver.hasPrincipalDivisors
  obtain ⟨Dj, hDj, -⟩ := hPD.exists_divisor (jGeomGen k N) hj0
  obtain ⟨DN, hDN, -⟩ := hPD.exists_divisor (jNGeomGen k N) hjN0
  refine (Dj.support.finite_toSet.union DN.support.finite_toSet).subset ?_
  intro v hv
  rw [Set.mem_setOf_eq, IsAffineGeomPlace, not_and_or] at hv
  rcases hv with h | h
  · left
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hDj]
    intro h0
    exact h (v.mem_of_ord_nonneg hj0 (le_of_eq h0.symm))
  · right
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hDN]
    intro h0
    exact h (v.mem_of_ord_nonneg hjN0 (le_of_eq h0.symm))

private theorem mem_ssPlaces_frob_iff
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (v : Place k ↥(modularFunctionFieldC k N)) :
    frobOnPlacesGeomLevel k N data hKr v ∈ ssPlaces q N k ↔ v ∈ ssPlaces q N k := by
  classical
  have hfwd : ∀ w ∈ ssPlaces q N k, frobOnPlacesGeomLevel k N data hKr w ∈ ssPlaces q N k := by
    intro w hw
    rw [← ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w]
    exact ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k w hw
  refine ⟨fun h => ?_, hfwd v⟩
  have hinj := ModularCurve.frobOnPlacesGeomLevel_injective k N data hKr
  have hmaps : Set.MapsTo (frobOnPlacesGeomLevel k N data hKr) (↑W : Set _) (↑W : Set _) := by
    intro w hw
    exact Finset.mem_coe.mpr ((hW _).mpr (hfwd w ((hW w).mp (Finset.mem_coe.mp hw))))
  have hsurj : Set.SurjOn (frobOnPlacesGeomLevel k N data hKr) (↑W : Set _) (↑W : Set _) :=
    (Finset.surjOn_of_injOn_of_card_le _ (fun w hw => hmaps hw) (hinj.injOn) le_rfl)
  obtain ⟨w, hw, hwv⟩ := hsurj (Finset.mem_coe.mpr ((hW _).mpr h))
  rw [hinj hwv] at hw
  exact (hW v).mp (Finset.mem_coe.mp hw)

private theorem exists_zone
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (T : Finset (Place k ↥(modularFunctionFieldC k N))) (hT : ∀ t ∈ T, t ∉ ssPlaces q N k) :
    ∃ Z : Finset (Place k ↥(modularFunctionFieldC k N)),
      (∀ v ∈ T, v ∈ Z) ∧
      (∀ v ∈ T, frobOnPlacesGeomLevel k N data hKr v ∈ Z) ∧
      (∀ v, frobOnPlacesGeomLevel k N data hKr v ∈ T → v ∈ Z) ∧
      (∀ v, ¬ IsAffineGeomPlace k N v → v ∈ Z) ∧
      (∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        v ∉ ssPlaces q N k → v ∈ Z) ∧
      (∀ v ∈ Z, v ∉ ssPlaces q N k) := by
  classical
  set φ := frobOnPlacesGeomLevel k N data hKr with hφ
  have hinj : Function.Injective φ := ModularCurve.frobOnPlacesGeomLevel_injective k N data hKr
  obtain ⟨NA, hNA⟩ := (finite_setOf_not_isAffineGeomPlace (k := k) (N := N)).exists_finset_coe
  haveI : IsCurveOver k (modularFunctionFieldC k N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  obtain ⟨FX, hFX⟩ := ((ModularCurve.finite_setOf_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self k N data hKr).diff
    (t := ssPlaces q N k)).exists_finset_coe
  refine ⟨T ∪ T.image φ ∪ T.preimage φ hinj.injOn ∪ NA ∪ FX, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; simp [hv]
  · intro v hv; simp only [Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨v, hv, rfl⟩)))
  · intro v hv; simp only [Finset.mem_union, Finset.mem_preimage]; exact Or.inl (Or.inl (Or.inr hv))
  · intro v hv
    simp only [Finset.mem_union]
    left; right
    rw [← Finset.mem_coe, hNA]; exact hv
  · intro v hfix hss
    simp only [Finset.mem_union]
    right
    rw [← Finset.mem_coe, hFX]
    exact ⟨hfix, hss⟩
  · intro v hv hss
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_preimage] at hv
    rcases hv with (((hv | ⟨w, hw, rfl⟩) | hv) | hv) | hv
    · exact hT v hv hss
    · exact hT w hw ((mem_ssPlaces_frob_iff W hW w).mp hss)
    · exact hT _ hv ((mem_ssPlaces_frob_iff W hW v).mpr hss)
    · rw [← Finset.mem_coe, hNA, Set.mem_setOf_eq] at hv
      exact hv hss.2.1
    · rw [← Finset.mem_coe, hFX] at hv
      exact hv.2 hss

end MOVNAsm

end Zone

namespace NodeEnvelope
open ModularCurve.PlaceSpecialization.ProlongationTuple

private theorem finsuppDegree_sum_single {α ι : Type*} [DecidableEq α] [Fintype ι] (Q : ι → α) :
    Finsupp.degree (∑ i, Finsupp.single (Q i) (1 : ℤ)) = Fintype.card ι := by
  classical
  rw [map_sum]
  simp [Finsupp.degree_single]

private theorem one_le_sum_single_apply_self {α ι : Type*} [Fintype ι] (Q : ι → α) (i : ι) :
    1 ≤ (∑ j, Finsupp.single (Q j) (1 : ℤ)) (Q i) := by
  classical
  rw [MOVNCore.sum_single_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num)

private theorem mapDomain_sum_single {α β : Type*} {ι : Type*} [Fintype ι] (r : α → β) (Q : ι → α) :
    Finsupp.mapDomain r (∑ i, Finsupp.single (Q i) (1 : ℤ)) = ∑ i, Finsupp.single (r (Q i)) (1 : ℤ) := by
  classical
  rw [Finsupp.mapDomain_finsetSum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single

section TwistCore

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem tw_mapDomain_congr {α β : Type*} (D₁ D₂ : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ a, r a = v → D₁ a = D₂ a) : Finsupp.mapDomain r D₁ v = Finsupp.mapDomain r D₂ v := by
  classical
  have key : ∀ (D : α →₀ ℤ) (s : Finset α), D.support ⊆ s →
      Finsupp.mapDomain r D v = ∑ a ∈ s, if r a = v then D a else 0 := by
    intro D s hs
    rw [MOVNCore.mapDomain_apply_eq_sum]
    refine Finset.sum_subset hs fun a _ ha => ?_
    rw [Finsupp.notMem_support_iff.mp ha]
    split_ifs <;> rfl
  rw [key D₁ (D₁.support ∪ D₂.support) Finset.subset_union_left,
    key D₂ (D₁.support ∪ D₂.support) Finset.subset_union_right]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with hr
  · exact h a hr
  · rfl

omit [IsAlgClosed k] [DecidableEq k] in

private theorem tw_residue₁_sub (R : ProlongationTuple P) (f : ↥(modularFunctionFieldBar (N * q)))
    (h : f ∈ R.R₁.integers) (a : A) (ha : IsLocalRing.residue A a = 0)
    (h' : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)
      ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h'⟩ = R.residue₁ ⟨f, h⟩ := by
  have hx : (⟨_, h'⟩ : R.R₁.integers) = ⟨f, h⟩ - ⟨_, (R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ := rfl
  rw [hx, map_sub, sub_eq_self, ProlongationTuple.residue₁_apply, R.R₁.residue_algebraMap a, ha, map_zero, map_zero]

omit [IsAlgClosed k] [DecidableEq k] in

private theorem tw_residue₂_sub (R : ProlongationTuple P) (f : ↥(modularFunctionFieldBar (N * q)))
    (h : f ∈ R.R₂.integers) (a : A) (ha : IsLocalRing.residue A a = 0)
    (h' : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)
      ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h'⟩ = R.residue₂ ⟨f, h⟩ := by
  have hx : (⟨_, h'⟩ : R.R₂.integers) = ⟨f, h⟩ - ⟨_, (R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2⟩ := rfl
  rw [hx, map_sub, sub_eq_self, ProlongationTuple.residue₂_apply, R.R₂.residue_algebraMap a, ha, map_zero, map_zero]

omit [DecidableEq k] in

private theorem tw_zero (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (f : ↥(modularFunctionFieldBar (N * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hf₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∨ P.IsStrictSnd W) ∧
      IsAffineGeomPlace k N (P.reduceFst W) ∧ IsAffineGeomPlace k N (P.reduceSnd W))
    (hna : ∀ z : Place k ↥(modularFunctionFieldC k N), ¬ IsAffineGeomPlace k N z →
      z.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      z.ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : 0 < D V) :
    (IsAffineGeomPlace k N (P.reduceFst V) ∧ IsAffineGeomPlace k N (P.reduceSnd V)) ∧
    (¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) = P.reduceFst V ∧
      P.reduceSnd V = frobOnPlacesGeomLevel k N data hKr (P.reduceFst V) ∧
      1 ≤ (P.reduceFst V).ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N))
        + (P.reduceSnd V).ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N))) := by
  classical

  have hcusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ¬ IsAffineGeomPlace k N (P.reduceFst V) → IsCuspidal P V :=
    fun V h => isCuspidal_of_not_isAffineGeomPlace_reduceFst P V h
  have hsplit : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), IsCuspidal P V →
      IsInftySide P V ∨ IsZeroSide P V :=
    fun V h => isInftySide_or_isZeroSide_of_isCuspidal P hqN V h
  have hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v →
      IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) :=
    fun v hv => ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr v hv
  have hbwd : ∀ v : Place k ↥(modularFunctionFieldC k N),
      IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr v) → IsAffineGeomPlace k N v :=
    MOVNCore.isAffineGeomPlace_of_frob data hKr (MOVNAsm.finite_setOf_not_isAffineGeomPlace (k := k) (N := N)) hfwd
  have hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      IsInftySide P V → ¬ IsAffineGeomPlace k N (P.reduceFst V) :=
    fun V h => not_isAffineGeomPlace_reduceFst_of_isCuspidal P V h.1
  have hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      IsZeroSide P V → ¬ IsAffineGeomPlace k N (P.reduceSnd V) :=
    fun V h => MOVNAsm.not_isAffineGeomPlace_reduceSnd_of_isCuspidal' P V h.1

  let Zs : Set (Place k ↥(modularFunctionFieldC k N)) :=
    {v | frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v ∨ ¬ IsAffineGeomPlace k N v}
  have hZpole : ∀ W, D W < 0 → (P.IsStrictFst W ∧ P.reduceFst W ∉ Zs) ∨ (P.IsStrictSnd W ∧ P.reduceSnd W ∉ Zs) := by
    intro W hW
    obtain ⟨hs, ha₁, ha₂⟩ := hDpole W hW
    rcases hs with hs | hs
    · exact Or.inl ⟨hs, fun hz => by
        rcases hz with hz | hz
        exacts [MOVNCore.not_fixed_reduceFst_of_isStrictFst hs hz, hz ha₁]⟩
    · exact Or.inr ⟨hs, fun hz => by
        rcases hz with hz | hz
        exacts [MOVNCore.not_fixed_reduceSnd_of_isStrictSnd hs hz, hz ha₂]⟩
  have hZcusp : ∀ W, IsInftySide P W → P.reduceFst W ∈ Zs ∧ P.reduceSnd W ∈ Zs := fun W hW =>
    ⟨Or.inr (hInftyNA W hW),
      Or.inr (MOVNCore.not_isAffineGeomPlace_reduceSnd_of_isInftySide data hKr P hfwd hbwd hInftyNA W hW)⟩
  have hZcusp' : ∀ W, IsZeroSide P W → P.reduceFst W ∈ Zs ∧ P.reduceSnd W ∈ Zs := fun W hW =>
    ⟨Or.inr (MOVNCore.not_isAffineGeomPlace_reduceFst_of_isZeroSide data hKr P hfwd hbwd hZeroNA W hW),
      Or.inr (hZeroNA W hW)⟩

  have haff : IsAffineGeomPlace k N (P.reduceFst V) ∧ IsAffineGeomPlace k N (P.reduceSnd V) := by
    by_contra hnot
    have hna₁ : ¬ IsAffineGeomPlace k N (P.reduceFst V) := by
      intro h1
      have h2 : ¬ IsAffineGeomPlace k N (P.reduceSnd V) := fun h2 => hnot ⟨h1, h2⟩
      exact MOVNCore.not_isAffineGeomPlace_reduceFst_of_reduceSnd data hKr P hfwd hbwd h2 h1
    have hna₂ : ¬ IsAffineGeomPlace k N (P.reduceSnd V) :=
      MOVNCore.not_isAffineGeomPlace_reduceSnd_of_reduceFst data hKr P hfwd hbwd hna₁
    rcases MOVNCore.classBound R hR hO hcusp hsplit f h₁ h₂ hf₁ hf₂ D hD Zs hZpole hZcusp hZcusp' V
        (Or.inr hna₁) (Or.inr hna₂) with
      ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨⟨-, hk, -⟩, -, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩
    · rw [(hna _ hna₁).1] at hb; omega
    · rw [(hna _ hna₂).2] at hb; omega
    · exact hna₁ hk
    · rw [(hna _ hna₁).1] at hb; omega
    · rw [(hna _ hna₂).2] at hb; omega
  refine ⟨haff, fun hn₁ hn₂ => ?_⟩

  obtain ⟨hfix, hsnd⟩ : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V))
      = P.reduceFst V ∧ P.reduceSnd V = frobOnPlacesGeomLevel k N data hKr (P.reduceFst V) := by
    rcases MOVNCore.trichotomy P V with h | h | h
    · exact absurd h hn₁
    · exact absurd h hn₂
    · exact h
  have hfix₂ : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V))
      = P.reduceSnd V := by rw [hsnd, hfix]
  rcases MOVNCore.classBound R hR hO hcusp hsplit f h₁ h₂ hf₁ hf₂ D hD Zs hZpole hZcusp hZcusp' V
      (Or.inl hfix) (Or.inl hfix₂) with
    ⟨hk, -, -⟩ | ⟨hk, -, -⟩ | ⟨-, hb, -⟩ | ⟨⟨hk, -, -⟩, -, -⟩ | ⟨⟨hk, -, -⟩, -, -⟩
  · exact absurd hk hn₁
  · exact absurd hk hn₂
  · exact ⟨hfix, hsnd, by omega⟩
  · exact absurd haff.1 (hInftyNA V hk)
  · exact absurd haff.2 (hZeroNA V hk)

private theorem tw_lead {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (v : Place K F) {p r : F} (hp0 : p ≠ 0) (hr0 : r ≠ 0) (hp : v.ord p = 1) (hr : v.ord r = 1) :
    ∃ l : K, l ≠ 0 ∧ v.HasValue (p ^ (-((1 : ℕ) : ℤ)) * r) l := by
  have hT : v.ord (p⁻¹ * r) = 0 := by
    rw [v.ord_mul (inv_ne_zero hp0) hr0, v.ord_inv, hp, hr]; norm_num
  obtain ⟨l, hl⟩ := MOVNCore.exists_hasValue_of_ord_nonneg v (g := p⁻¹ * r) (Or.inr hT.ge)
  refine ⟨l, ?_, by rwa [Nat.cast_one, zpow_neg, zpow_one]⟩
  rintro rfl
  have h := MOVNCore.ord_pos_of_hasValue_zero v (mul_ne_zero (inv_ne_zero hp0) hr0) hl
  rw [hT] at h
  exact lt_irrefl _ h

private theorem tw_zw (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (w : Place k ↥(modularFunctionFieldC k N))
    (f : ↥(modularFunctionFieldBar (N * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hf₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (hDpole : ∀ W, D W < 0 → (P.IsStrictFst W ∨ P.IsStrictSnd W) ∧
      IsAffineGeomPlace k N (P.reduceFst W) ∧ IsAffineGeomPlace k N (P.reduceSnd W))
    (hW' : ∀ v ∈ W, v ≠ w →
      v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0)
    (Z : Finset (Place k ↥(modularFunctionFieldC k N)))
    (hZna : ∀ v, ¬ IsAffineGeomPlace k N v → v ∈ Z)
    (hZfix : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      v ∉ ssPlaces q N k → v ∈ Z)
    (hZunit : ∀ v ∈ Z, v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      v.ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : 0 < D V)
    (hn₁ : ¬ P.IsStrictFst V) (hn₂ : ¬ P.IsStrictSnd V) : P.reduceFst V = w := by
  classical
  have hna : ∀ z : Place k ↥(modularFunctionFieldC k N), ¬ IsAffineGeomPlace k N z →
      z.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      z.ord (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0 :=
    fun z hz => hZunit z (hZna z hz)
  obtain ⟨-, hrest⟩ := tw_zero hqN R hR hO f h₁ h₂ hf₁ hf₂ D hD hDpole hna V hV
  obtain ⟨hfix, hsnd, hsum⟩ := hrest hn₁ hn₂
  by_contra hne
  rw [hsnd] at hsum
  by_cases hss : P.reduceFst V ∈ ssPlaces q N k
  · obtain ⟨e₁, e₂⟩ := hW' _ ((hW _).mpr hss) hne
    rw [e₁, e₂] at hsum
    omega
  · have hz₁ : P.reduceFst V ∈ Z := hZfix _ hfix hss
    have hfix' : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
        (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)))
          = frobOnPlacesGeomLevel k N data hKr (P.reduceFst V) := by
      rw [hfix]
    have hss' : frobOnPlacesGeomLevel k N data hKr (P.reduceFst V) ∉ ssPlaces q N k := fun h =>
      hss ((MOVNAsm.mem_ssPlaces_frob_iff W hW _).mp h)
    have hz₂ : frobOnPlacesGeomLevel k N data hKr (P.reduceFst V) ∈ Z := hZfix _ hfix' hss'
    rw [(hZunit _ hz₁).1, (hZunit _ hz₂).2] at hsum
    omega

set_option maxHeartbeats 6400000 in

private theorem tw_core (hqN : ¬ q ∣ N) (R : ProlongationTuple P) (hR : R.IsModel)
    (W : Finset (Place k ↥(modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hO : R.OrderLawFixed)
    (π : Place k ↥(modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N)) (hπ : ∀ w ∈ W, w.ord (π w) = 1)
    (w : Place k ↥(modularFunctionFieldC k N)) (hw : w ∈ W)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hV : P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
    (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers) (u : (↥A)ˣ)
    (hres₁ : (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k N))
      = algebraMap k ↥(modularFunctionFieldC k N) (red (u : A)))
    (hres₂ : (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N)) = 1)
    (htord : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') →
      V'.ord t = ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
          • (Finsupp.single V (1 : ℤ))
        - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V')
    (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
    (hpole : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V'.ord G < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V')
    (hpoleAff : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      V'.ord G < 0 → IsAffineGeomPlace k N (P.reduceFst V') ∧ IsAffineGeomPlace k N (P.reduceSnd V'))
    (hw₁ : w.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) = 1)
    (hw₂ : (arithFrobC q k N • w).ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) = 1)
    (hW' : ∀ v ∈ W, v ≠ w →
      v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      (arithFrobC q k N • v).ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0)
    (Z : Finset (Place k ↥(modularFunctionFieldC k N)))
    (hZna : ∀ v, ¬ IsAffineGeomPlace k N v → v ∈ Z)
    (hZfix : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      v ∉ ssPlaces q N k → v ∈ Z)
    (hZunit : ∀ v ∈ Z, v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      v.ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) = 0)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (hVa : 0 < V.ord
      (G - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ))) :
    ∃ (g : ↥(modularFunctionFieldBar (N * q)))
      (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
      (hg₁ : t * g ∈ R.R₁.integers) (hg₂ : t * g ∈ R.R₂.integers) (n₁ n₂ : ℕ) (l₁ l₂ : k),
      0 < V.ord g ∧
      (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        V'.ord g < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V') ∧
      (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        E V' = ((arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ
            • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V'
          + max (V'.ord g) 0) ∧
      (∀ V', 0 ≤ E V') ∧
      (∀ V' ∈ E.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
        (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V')) ∧
      (∀ V' ∈ E.support, ¬ IsCuspidal P V' ∧ ¬ IsCuspidal' P V') ∧
      (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') → V'.ord (t * g) = E V') ∧
      l₁ ≠ 0 ∧ l₂ ≠ 0 ∧
      ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E w ∧
      w.HasValue (π w ^ (-(n₁ : ℤ))
        * (R.residue₁ ⟨t * g, hg₁⟩ : ↥(modularFunctionFieldC k N))) l₁ ∧
      (arithFrobC q k N • w).HasValue
        ((arithFrobC q k N • π w) ^ (-(n₂ : ℤ))
          * (R.residue₂ ⟨t * g, hg₂⟩ : ↥(modularFunctionFieldC k N))) l₂ := by
  classical
  haveI : IsCurveOver k ↥(modularFunctionFieldC k N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)

  set φ := frobOnPlacesGeomLevel k N data hKr with hφdef
  set τ := arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) σ with hτdef
  have hφw : arithFrobC q k N • w = φ w := ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w
  have hwss : w ∈ ssPlaces q N k := (hW w).mp hw
  have hwfix : φ (φ w) = w := frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces hqN P w hwss
  have hwaff : IsAffineGeomPlace k N w := hwss.2.1
  have hfwd : ∀ v : Place k ↥(modularFunctionFieldC k N), IsAffineGeomPlace k N v → IsAffineGeomPlace k N (φ v) :=
    fun v hv => ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k N data hKr v hv

  have ha0 : IsLocalRing.residue A a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
  set g := G - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) with hgdef
  have hamem₁ :
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
    (R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2
  have hamem₂ :
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
    (R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2
  have hg₁ : g ∈ R.R₁.integers := sub_mem h₁ hamem₁
  have hg₂ : g ∈ R.R₂.integers := sub_mem h₂ hamem₂
  have hrg₁ : R.residue₁ ⟨g, hg₁⟩ = R.residue₁ ⟨G, h₁⟩ := tw_residue₁_sub R G h₁ a ha0 hg₁
  have hrg₂ : R.residue₂ ⟨g, hg₂⟩ = R.residue₂ ⟨G, h₂⟩ := tw_residue₂_sub R G h₂ a ha0 hg₂
  have hG₁0 : (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hw₁; exact zero_ne_one hw₁
  have hG₂0 : (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hw₂; exact zero_ne_one hw₂
  have hgr₁0 : R.residue₁ ⟨g, hg₁⟩ ≠ 0 := by rw [hrg₁]; exact hG₁0
  have hgr₂0 : R.residue₂ ⟨g, hg₂⟩ ≠ 0 := by rw [hrg₂]; exact hG₂0
  have hg0 : g ≠ 0 := by
    intro h0; apply hgr₁0
    have : (⟨g, hg₁⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have htr0 : (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by rw [hres₂]; exact one_ne_zero
  have ht0 : t ≠ 0 := by
    intro h0; apply htr0
    have : (⟨t, ht₂⟩ : R.R₂.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hu0 : red (u : A) ≠ 0 := (u.isUnit.map red).ne_zero

  have hgpole : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V'.ord g < 0 →
      (P.IsStrictFst V' ∨ P.IsStrictSnd V') ∧
        IsAffineGeomPlace k N (P.reduceFst V') ∧ IsAffineGeomPlace k N (P.reduceSnd V') := by
    intro V' hV'
    have hG : V'.ord G < 0 := (MOVNCore.ord_neg_of_ord_sub_const_neg V' hV').2
    exact ⟨hpole V' hG, hpoleAff V' hG⟩

  have hgw : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V' = w → 0 ≤ V'.ord g := by
    intro V' hV'
    by_contra hlt
    push Not at hlt
    rcases (hgpole V' hlt).1 with hs | hs
    · exact MOVNCore.not_fixed_reduceFst_of_isStrictFst hs (by rw [hV']; exact hwfix)
    · exact MOVNCore.not_fixed_reduceFst_of_isStrictSnd hs (by rw [hV']; exact hwfix)

  obtain ⟨Dg, hDg, -⟩ := hPD.exists_divisor g hg0
  set E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    τ • Finsupp.single V (1 : ℤ) + Finsupp.single V (-1) + Dg.filter (fun V' => 0 < Dg V') with hEdef
  have hEshape : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      E V' = (τ • Finsupp.single V (1 : ℤ) - Finsupp.single V 1 :
          Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) V' + max (V'.ord g) 0 := by
    intro V'
    simp only [hEdef, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.filter_apply, Finsupp.single_apply,
      AlgebraicCurve.SemilinearAut.smul_single, hDg, max_def]
    split_ifs <;> omega

  have hna : ∀ z : Place k ↥(modularFunctionFieldC k N), ¬ IsAffineGeomPlace k N z →
      z.ord (R.residue₁ ⟨g, hg₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      z.ord (R.residue₂ ⟨g, hg₂⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
    intro z hz; rw [hrg₁, hrg₂]; exact hZunit z (hZna z hz)
  have hDgpole : ∀ W, Dg W < 0 → (P.IsStrictFst W ∨ P.IsStrictSnd W) ∧
      IsAffineGeomPlace k N (P.reduceFst W) ∧ IsAffineGeomPlace k N (P.reduceSnd W) :=
    fun W hW => hgpole W (by rw [← hDg]; exact hW)
  have hzero := tw_zero hqN R hR hO g hg₁ hg₂ hgr₁0 hgr₂0 Dg hDg hDgpole hna

  have hW'g : ∀ v ∈ W, v ≠ w → v.ord (R.residue₁ ⟨g, hg₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨g, hg₂⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
    intro v hv hne
    obtain ⟨e₁, e₂⟩ := hW' v hv hne
    rw [ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr] at e₂
    rw [hrg₁, hrg₂]
    exact ⟨e₁, e₂⟩
  have hZunitg : ∀ v ∈ Z, v.ord (R.residue₁ ⟨g, hg₁⟩ : ↥(modularFunctionFieldC k N)) = 0 ∧
      v.ord (R.residue₂ ⟨g, hg₂⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
    intro v hv
    rw [hrg₁, hrg₂]
    exact hZunit v hv
  have hzw : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), 0 < V'.ord g →
      ¬ P.IsStrictFst V' → ¬ P.IsStrictSnd V' → P.reduceFst V' = w := fun V' hV' hn₁ hn₂ =>
    tw_zw hqN R hR hO W hW w g hg₁ hg₂ hgr₁0 hgr₂0 Dg hDg hDgpole hW'g Z hZna hZfix hZunitg V' (by rw [hDg]; exact hV')
      hn₁ hn₂

  have hsuppE : ∀ V' ∈ E.support, V' = τ • V ∨ V' = V ∨ 0 < V'.ord g := by
    intro V' hV'
    by_cases h1 : V' = τ • V
    · exact Or.inl h1
    by_cases h2 : V' = V
    · exact Or.inr (Or.inl h2)
    right; right
    have hne : E V' ≠ 0 := Finsupp.mem_support_iff.mp hV'
    rw [hEshape V', Finsupp.sub_apply, AlgebraicCurve.SemilinearAut.smul_single, Finsupp.single_apply,
      Finsupp.single_apply, if_neg (Ne.symm h1), if_neg (Ne.symm h2)] at hne
    by_contra hle
    push Not at hle
    rw [max_eq_right hle] at hne
    exact hne (by norm_num)
  have hτV : P.reduceFst (τ • V) = w := by rw [hτdef, reduceFst_arithmeticGalois_smul P σ hσ V]; exact hV.1
  have hτS : P.reduceSnd (τ • V) = P.reduceSnd V := by rw [hτdef, reduceSnd_arithmeticGalois_smul P σ hσ V]
  have hτns : ¬ P.IsStrictFst (τ • V) ∧ ¬ P.IsStrictSnd (τ • V) := by
    have e₁ : P.reduceFst (τ • V) = P.reduceFst V := hτV.trans hV.1.symm
    constructor
    · intro h; apply hV.2.1; unfold IsStrictFst at h ⊢; rw [e₁, hτS] at h; exact h
    · intro h; apply hV.2.2; unfold IsStrictSnd at h ⊢; rw [e₁, hτS] at h; exact h
  have hVsnd : P.reduceSnd V = φ w := by
    rcases MOVNCore.trichotomy P V with h | h | h
    · exact absurd h hV.2.1
    · exact absurd h hV.2.2
    · rw [h.2, hV.1]

  have hmul₁ : t * g ∈ R.R₁.integers := mul_mem ht₁ hg₁
  have hmul₂ : t * g ∈ R.R₂.integers := mul_mem ht₂ hg₂
  have hres_tg₁ : (R.residue₁ ⟨t * g, hmul₁⟩ : ↥(modularFunctionFieldC k N))
      = algebraMap k ↥(modularFunctionFieldC k N) (red (u : A)) * R.residue₁ ⟨G, h₁⟩ := by
    have hx : (⟨t * g, hmul₁⟩ : R.R₁.integers) = ⟨t, ht₁⟩ * ⟨g, hg₁⟩ := rfl
    rw [hx, map_mul, hres₁, hrg₁]
  have hres_tg₂ : (R.residue₂ ⟨t * g, hmul₂⟩ : ↥(modularFunctionFieldC k N)) = R.residue₂ ⟨G, h₂⟩ := by
    have hx : (⟨t * g, hmul₂⟩ : R.R₂.integers) = ⟨t, ht₂⟩ * ⟨g, hg₂⟩ := rfl
    rw [hx, map_mul, hres₂, hrg₂, one_mul]
  have hπ0 : π w ≠ 0 := by
    intro h0; have := hπ w hw; rw [h0, Place.ord_zero] at this; exact zero_ne_one this

  have hrG₁ : w.ord (R.residue₁ ⟨t * g, hmul₁⟩ : ↥(modularFunctionFieldC k N)) = 1 := by
    rw [hres_tg₁, MOVNCore.ord_const_mul w hu0, hw₁]
  have htg₁0 : (R.residue₁ ⟨t * g, hmul₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    rw [hres_tg₁]; exact mul_ne_zero ((map_ne_zero _).mpr hu0) hG₁0
  obtain ⟨l₁, hl₁, hl₁v⟩ := tw_lead w hπ0 htg₁0 (hπ w hw) hrG₁
  have hπ₂0 : arithFrobC q k N • π w ≠ 0 := by
    rw [Ne, smul_eq_zero_iff_eq]; exact hπ0
  have hπ₂ : (arithFrobC q k N • w).ord (arithFrobC q k N • π w) = 1 := by
    rw [AlgebraicCurve.SemilinearAut.ord_smul, hπ w hw]
  have hrG₂ : (arithFrobC q k N • w).ord (R.residue₂ ⟨t * g, hmul₂⟩ : ↥(modularFunctionFieldC k N)) = 1 := by
    rw [hres_tg₂, hw₂]
  have htg₂0 : (R.residue₂ ⟨t * g, hmul₂⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
    rw [hres_tg₂]; exact hG₂0
  obtain ⟨l₂, hl₂, hl₂v⟩ := tw_lead (arithFrobC q k N • w) hπ₂0 htg₂0 hπ₂ hrG₂

  have hraw₁ : R.R₁.residue ⟨g, hg₁⟩ ≠ 0 := MOVNCore.rawResidue₁_ne_zero R hgr₁0
  have hraw₂ : R.R₂.residue ⟨g, hg₂⟩ ≠ 0 := MOVNCore.rawResidue₂_ne_zero R hgr₂0
  have hlaw : Finsupp.mapDomain P.reduceFst Dg w
      = w.ord (R.residue₁ ⟨g, hg₁⟩) + (φ w).ord (R.residue₂ ⟨g, hg₂⟩) :=
    hO g hg₁ hg₂ hraw₁ hraw₂ Dg hDg w hwfix hwaff
  have hfilt : Finsupp.mapDomain P.reduceFst (Dg.filter (fun V' => 0 < Dg V')) w
      = Finsupp.mapDomain P.reduceFst Dg w := by
    refine tw_mapDomain_congr _ _ _ _ fun V' hV' => ?_
    rw [Finsupp.filter_apply]
    split_ifs with hp
    · rfl
    · have := hgw V' hV'; rw [← hDg] at this; omega
  have hn : ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = Finsupp.mapDomain P.reduceFst E w := by
    simp only [hEdef, Finsupp.mapDomain_add, Finsupp.add_apply, AlgebraicCurve.SemilinearAut.smul_single,
      Finsupp.mapDomain_single, Finsupp.single_apply]
    rw [if_pos hτV, if_pos hV.1, hfilt, hlaw, hrg₁, hrg₂, ← hφw, hw₁, hw₂]
    norm_num

  refine ⟨g, E, hmul₁, hmul₂, 1, 1, l₁, l₂, hVa, fun V' hV' => (hgpole V' hV').1, hEshape, ?_, ?_, ?_, ?_, hl₁, hl₂,
    hn, hl₁v, hl₂v⟩
  ·
    intro V'
    rw [hEshape V', Finsupp.sub_apply, AlgebraicCurve.SemilinearAut.smul_single, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases h2 : V = V'
    · subst h2
      have : 1 ≤ max (V.ord g) 0 := le_trans (by omega) (le_max_left _ _)
      split_ifs <;> omega
    · rw [if_neg h2]
      have : 0 ≤ max (V'.ord g) 0 := le_max_right _ _
      split_ifs <;> omega
  ·
    intro V' hV'
    by_cases hs₁ : P.IsStrictFst V'
    · exact Or.inl hs₁
    by_cases hs₂ : P.IsStrictSnd V'
    · exact Or.inr (Or.inl hs₂)
    refine Or.inr (Or.inr ⟨?_, hs₁, hs₂⟩)
    rcases hsuppE V' hV' with h | h | h
    · rw [h]; exact hτV
    · rw [h]; exact hV.1
    · exact hzw V' h hs₁ hs₂
  ·
    intro V' hV'
    have haff : IsAffineGeomPlace k N (P.reduceFst V') ∧ IsAffineGeomPlace k N (P.reduceSnd V') := by
      rcases hsuppE V' hV' with h | h | h
      · rw [h, hτV, hτS, hVsnd]; exact ⟨hwaff, hfwd w hwaff⟩
      · rw [h, hV.1, hVsnd]; exact ⟨hwaff, hfwd w hwaff⟩
      · exact (hzero V' (by rw [hDg]; exact h)).1
    exact ⟨fun hc => not_isAffineGeomPlace_reduceFst_of_isCuspidal P V' hc haff.1,
      fun hc => MOVNAsm.not_isAffineGeomPlace_reduceSnd_of_isCuspidal' P V' hc haff.2⟩
  ·
    intro V' hV'
    rw [hEshape V', max_eq_left (hgw V' hV'.1), V'.ord_mul ht0 hg0, htord V' hV']

end TwistCore

set_option maxHeartbeats 19200000 in

private theorem sideData
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed)
      (π : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) →
        modularFunctionFieldC (ResidueField A) N)
      (hπ : ∀ w ∈ W, w.ord (π w) = 1)
      (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (hw : w ∈ W),
      ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
          (hV : P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
          (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers) (u : (↥A)ˣ)
          (hres₁ : (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N))
            = algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A (u : A)))
          (hres₂ : (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 1)
          (htord : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
            (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') →
            V'.ord t = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V'),
          ∃ (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
            (Z : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              V'.ord G < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V') ∧
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              V'.ord G < 0 → IsAffineGeomPlace (ResidueField A) N (P.reduceFst V') ∧
                IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V')) ∧
            w.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 1 ∧
            (arithFrobC q (ResidueField A) N • w).ord
              (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 1 ∧
            (∀ v ∈ W, v ≠ w →
              v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 0 ∧
              (arithFrobC q (ResidueField A) N • v).ord
                (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 0) ∧
            (∀ v, ¬ IsAffineGeomPlace (ResidueField A) N v → v ∈ Z) ∧
            (∀ v, frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr v)
              = v → v ∉ ssPlaces q N (ResidueField A) → v ∈ Z) ∧
            (∀ v ∈ Z, v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 0 ∧
              v.ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 0) ∧
            ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
              0 < V.ord (G - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) := by
  intro W hW data hKr hα hβ P R hR hRL hO π hπ w hw σ hσ V hV t ht₁ ht₂ u hres₁ hres₂ htord
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
    ModularCurve.isCurveOver_modularFunctionFieldBar (N * q)
  haveI hIC : IsCurveOver (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) N
  haveI : Infinite (ResidueField A) := inferInstance
  have hNV : R.NodeValueLaw W := nodeValueLaw_of_regularityLaw P hqN hW R hRL

  have hcusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V) → IsCuspidal P V :=
    fun V h => isCuspidal_of_not_isAffineGeomPlace_reduceFst P V h
  have hsplit : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), IsCuspidal P V →
      IsInftySide P V ∨ IsZeroSide P V :=
    fun V h => isInftySide_or_isZeroSide_of_isCuspidal P hqN V h
  have hInftyNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      IsInftySide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V) :=
    fun V h => not_isAffineGeomPlace_reduceFst_of_isCuspidal P V h.1
  have hZeroNA : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      IsZeroSide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V) :=
    fun V h => MOVNAsm.not_isAffineGeomPlace_reduceSnd_of_isCuspidal' P V h.1
  have hφaff : ∀ v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N),
      IsAffineGeomPlace (ResidueField A) N v →
        IsAffineGeomPlace (ResidueField A) N (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) :=
    fun v h => ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel (ResidueField A) N data hKr v h
  have hbwd : ∀ v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N),
      IsAffineGeomPlace (ResidueField A) N (frobOnPlacesGeomLevel (ResidueField A) N data hKr v) →
        IsAffineGeomPlace (ResidueField A) N v :=
    fun v h => MOVNCore.isAffineGeomPlace_of_frob data hKr
      (MOVNAsm.finite_setOf_not_isAffineGeomPlace (k := ResidueField A) (N := N)) hφaff v h
  have hInftyNA' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      IsInftySide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V) :=
    fun V h => MOVNCore.not_isAffineGeomPlace_reduceSnd_of_isInftySide data hKr P hφaff hbwd hInftyNA V h
  have hZeroNA' : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      IsZeroSide P V → ¬ IsAffineGeomPlace (ResidueField A) N (P.reduceFst V) :=
    fun V h => MOVNCore.not_isAffineGeomPlace_reduceFst_of_isZeroSide data hKr P hφaff hbwd hZeroNA V h
  have hWss : ∀ v ∈ W, v ∈ ssPlaces q N (ResidueField A) := fun v hv => (hW v).mp hv
  have hfrob : ∀ v : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N),
      arithFrobC q (ResidueField A) N • v = frobOnPlacesGeomLevel (ResidueField A) N data hKr v :=
    fun v => ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q (ResidueField A) N data hKr v
  have hφinj := ModularCurve.frobOnPlacesGeomLevel_injective (ResidueField A) N data hKr
  have hWfrob : ∀ v ∈ W, arithFrobC q (ResidueField A) N • v ∈ W :=
    fun v hv => (hW _).mpr (ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N (ResidueField A) v (hWss v hv))

  obtain ⟨Z, -, -, -, hZna, hZfix, hZss⟩ :=
    MOVNAsm.exists_zone (data := data) (hKr := hKr) W hW ∅ (fun t ht => absurd ht (Finset.notMem_empty t))
  have hZW : ∀ v ∈ Z, v ∉ W := fun v hvZ hvW => hZss v hvZ (hWss v hvW)
  have hwZ : w ∉ Z := fun h => hZss w h (hWss w hw)
  set w' := arithFrobC q (ResidueField A) N • w with hw'
  have hw'W : w' ∈ W := hWfrob w hw
  have hw'Z : w' ∉ Z := fun h => hZss w' h (hWss w' hw'W)

  set m : ℕ := 2 * genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) + W.card + 2 with hm
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hinj₁, hinj₂, hB₁, hB₂, -, -⟩ :=
    ModularCurve.PlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq P hqN (Z ∪ W) m m
  have hB₁Z : ∀ i, P.reduceFst (Q₁ i) ∉ Z := fun i h => hB₁ i (Finset.mem_union_left _ h)
  have hB₂Z : ∀ j, P.reduceSnd (Q₂ j) ∉ Z := fun j h => hB₂ j (Finset.mem_union_left _ h)
  have hB₁W : ∀ i, P.reduceFst (Q₁ i) ∉ W := fun i h => hB₁ i (Finset.mem_union_right _ h)
  have hB₂W : ∀ j, P.reduceSnd (Q₂ j) ∉ W := fun j h => hB₂ j (Finset.mem_union_right _ h)
  set E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) with hE₁
  set E₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE₂
  set Daux : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) := E₁ + E₂ with hDaux
  have hDaux0 : ∀ V', 0 ≤ Daux V' := fun V' => by
    rw [hDaux, Finsupp.add_apply]
    exact add_nonneg (MOVNCore.sum_single_apply_nonneg Q₁ V') (MOVNCore.sum_single_apply_nonneg Q₂ V')
  have hDaux_cases : ∀ V', Daux V' ≠ 0 → (∃ i, Q₁ i = V') ∨ (∃ j, Q₂ j = V') := by
    intro V' hV'
    by_contra hc
    push Not at hc
    apply hV'
    rw [hDaux, Finsupp.add_apply, MOVNCore.sum_single_apply_eq_zero Q₁ V' hc.1,
      MOVNCore.sum_single_apply_eq_zero Q₂ V' hc.2, add_zero]
  have hgood : P.IsGoodDiv Daux := by
    intro V' hV'
    rcases hDaux_cases V' (Finsupp.mem_support_iff.mp hV') with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl (hQ₁ i)
    · exact Or.inr (hQ₂ j)
  have hfst : P.fstDiv Daux = E₁ := by
    unfold PlaceSpecialization.fstDiv
    rw [hDaux, Finsupp.filter_add]
    have h1 : E₁.filter P.IsStrictFst = E₁ := by
      rw [Finsupp.filter_eq_self_iff]
      intro V' hV'
      obtain ⟨i, rfl⟩ := MOVNCore.exists_of_sum_single_apply_ne_zero Q₁ V' hV'
      exact hQ₁ i
    have h2 : E₂.filter P.IsStrictFst = 0 := by
      rw [Finsupp.filter_eq_zero_iff]
      intro V' hV'
      by_contra h0
      obtain ⟨j, rfl⟩ := MOVNCore.exists_of_sum_single_apply_ne_zero Q₂ V' h0
      exact MOVNCore.not_isStrictSnd_of_isStrictFst hV' (hQ₂ j)
    rw [h1, h2, add_zero]
  have hsnd : P.sndDiv Daux = E₂ := by
    unfold PlaceSpecialization.sndDiv
    rw [hDaux, Finsupp.filter_add]
    have h1 : E₁.filter P.IsStrictSnd = 0 := by
      rw [Finsupp.filter_eq_zero_iff]
      intro V' hV'
      by_contra h0
      obtain ⟨i, rfl⟩ := MOVNCore.exists_of_sum_single_apply_ne_zero Q₁ V' h0
      exact MOVNCore.not_isStrictSnd_of_isStrictFst (hQ₁ i) hV'
    have h2 : E₂.filter P.IsStrictSnd = E₂ := by
      rw [Finsupp.filter_eq_self_iff]
      intro V' hV'
      obtain ⟨j, rfl⟩ := MOVNCore.exists_of_sum_single_apply_ne_zero Q₂ V' hV'
      exact hQ₂ j
    rw [h1, h2, zero_add]

  set U₁ : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) :=
    Finset.univ.image (fun i => P.reduceFst (Q₁ i)) with hU₁
  set U₂ : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N)) :=
    Finset.univ.image (fun j => P.reduceSnd (Q₂ j)) with hU₂
  have hU₁card : U₁.card = m := by
    rw [hU₁, Finset.card_image_of_injective _ hinj₁, Finset.card_univ, Fintype.card_fin]
  have hU₂card : U₂.card = m := by
    rw [hU₂, Finset.card_image_of_injective _ hinj₂, Finset.card_univ, Fintype.card_fin]
  have hmemU₁ : ∀ {v}, v ∈ U₁ → ∃ i, P.reduceFst (Q₁ i) = v := fun {v} hv => by simpa [hU₁] using hv
  have hmemU₂ : ∀ {v}, v ∈ U₂ → ∃ j, P.reduceSnd (Q₂ j) = v := fun {v} hv => by simpa [hU₂] using hv
  have hU₁Z : ∀ v ∈ U₁, v ∉ Z := by intro v hv; obtain ⟨i, rfl⟩ := hmemU₁ hv; exact hB₁Z i
  have hU₂Z : ∀ v ∈ U₂, v ∉ Z := by intro v hv; obtain ⟨j, rfl⟩ := hmemU₂ hv; exact hB₂Z j
  have hU₁W : ∀ v ∈ U₁, v ∉ W := by intro v hv; obtain ⟨i, rfl⟩ := hmemU₁ hv; exact hB₁W i
  have hU₂W : ∀ v ∈ U₂, v ∉ W := by intro v hv; obtain ⟨j, rfl⟩ := hmemU₂ hv; exact hB₂W j
  have hsumU : ∀ (U : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N))) v,
      (∑ u ∈ U, Finsupp.single u (1 : ℤ)) v = if v ∈ U then 1 else 0 := by
    intro U v
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq']
  have hmapE₁ : Finsupp.mapDomain P.reduceFst E₁ = ∑ i, Finsupp.single (P.reduceFst (Q₁ i)) (1 : ℤ) :=
    NodeEnvelope.mapDomain_sum_single _ _
  have hmapE₂ : Finsupp.mapDomain P.reduceSnd E₂ = ∑ j, Finsupp.single (P.reduceSnd (Q₂ j)) (1 : ℤ) :=
    NodeEnvelope.mapDomain_sum_single _ _
  have hL₁ : riemannRochSpace (∑ u ∈ U₁, Finsupp.single u (1 : ℤ)) ≤
      riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv Daux)) := by
    refine MOVNCore.riemannRochSpace_mono fun v => ?_
    rw [hsumU, hfst, hmapE₁]
    split_ifs with hv
    · obtain ⟨i, rfl⟩ := hmemU₁ hv
      exact NodeEnvelope.one_le_sum_single_apply_self (fun i => P.reduceFst (Q₁ i)) i
    · exact MOVNCore.sum_single_apply_nonneg _ _
  have hL₂ : riemannRochSpace (∑ u ∈ U₂, Finsupp.single u (1 : ℤ)) ≤
      riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv Daux)) := by
    refine MOVNCore.riemannRochSpace_mono fun v => ?_
    rw [hsumU, hsnd, hmapE₂]
    split_ifs with hv
    · obtain ⟨j, rfl⟩ := hmemU₂ hv
      exact NodeEnvelope.one_le_sum_single_apply_self (fun j => P.reduceSnd (Q₂ j)) j
    · exact MOVNCore.sum_single_apply_nonneg _ _
  have hdeg₁ : 2 * (genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) : ℤ) - 1 + W.card ≤
      (Finsupp.mapDomain P.reduceFst (P.fstDiv Daux)).degree := by
    rw [hfst, hmapE₁, NodeEnvelope.finsuppDegree_sum_single, Fintype.card_fin, hm]; push_cast; omega
  have hdeg₂ : 2 * (genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) : ℤ) - 1 ≤
      (Finsupp.mapDomain P.reduceSnd (P.sndDiv Daux)).degree := by
    rw [hsnd, hmapE₂, NodeEnvelope.finsuppDegree_sum_single, Fintype.card_fin, hm]; push_cast; omega

  have hEq : modularFunctionFieldFullC (ResidueField A) N = modularFunctionFieldC (ResidueField A) N :=
    ModularCurve.modularFunctionFieldFullC_eq_modularFunctionFieldC_residueField N q hqN A hA
  have hINTERP := ModularCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_modularFunctionFieldFullC (ResidueField A) N
  rw [hEq] at hINTERP
  obtain ⟨γ₀, hγ₀⟩ := Infinite.exists_notMem_finset ({(0 : ResidueField A)} : Finset (ResidueField A))
  have hγ₀0 : γ₀ ≠ 0 := by simpa using hγ₀
  have hU₁Wv : Disjoint U₁ (W.erase w) := Finset.disjoint_left.mpr fun v hvU hvW => hU₁W v hvU (Finset.mem_of_mem_erase hvW)
  have hU₂Wv : Disjoint U₂ (W.erase w') := Finset.disjoint_left.mpr fun v hvU hvW => hU₂W v hvU (Finset.mem_of_mem_erase hvW)
  have hU₁Z' : Disjoint U₁ Z := Finset.disjoint_left.mpr fun v hvU hvZ => hU₁Z v hvU hvZ
  have hU₂Z' : Disjoint U₂ Z := Finset.disjoint_left.mpr fun v hvU hvZ => hU₂Z v hvU hvZ
  have hWvZ : Disjoint (W.erase w) Z := Finset.disjoint_left.mpr fun v hvW hvZ => hZW v hvZ (Finset.mem_of_mem_erase hvW)
  have hWv'Z : Disjoint (W.erase w') Z := Finset.disjoint_left.mpr fun v hvW hvZ => hZW v hvZ (Finset.mem_of_mem_erase hvW)
  have hwU₁ : w ∉ U₁ := fun h => hU₁W w h hw
  have hw'U₂ : w' ∉ U₂ := fun h => hU₂W w' h hw'W
  have hcard₁ : (W.erase w).card + 2 * genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) + 2 ≤ U₁.card := by
    rw [hU₁card, hm]; have := Finset.card_erase_le (s := W) (a := w); omega
  have hcard₂ : (W.erase w').card + 2 * genusFF (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) + 2 ≤ U₂.card := by
    rw [hU₂card, hm]; have := Finset.card_erase_le (s := W) (a := w'); omega
  obtain ⟨g₁, hg₁L, hg₁d, hg₁W, hg₁Z⟩ := hINTERP U₁ (W.erase w) Z w 0 (fun _ => γ₀) {0}
    hU₁Wv hU₁Z' hWvZ hwU₁ (Finset.notMem_erase w W) hwZ hcard₁
  obtain ⟨g₂, hg₂L, hg₂d, hg₂W, hg₂Z⟩ := hINTERP U₂ (W.erase w') Z w' 0 (fun _ => γ₀) {0}
    hU₂Wv hU₂Z' hWv'Z hw'U₂ (Finset.notMem_erase w' W) hw'Z hcard₂
  rw [map_zero, sub_zero] at hg₁d hg₂d
  have hg₁val : w.HasValue g₁ 0 := MOVNCore.hasValue_of_ord_sub_pos _ (by rw [map_zero, sub_zero, hg₁d]; norm_num)
  have hg₂val : w'.HasValue g₂ 0 := MOVNCore.hasValue_of_ord_sub_pos _ (by rw [map_zero, sub_zero, hg₂d]; norm_num)

  let toFull : ↥(modularFunctionFieldC (ResidueField A) N) → ↥(modularFunctionFieldFullC (ResidueField A) N) :=
    fun g => ⟨(g : LaurentSeries (ResidueField A)), modularFunctionFieldC_le_full (ResidueField A) N g.2⟩
  have ι_toFull : ∀ g, R.ι (toFull g) = g := fun g => Subtype.ext (MOVNCore.coe_ι R (toFull g))
  have hg₁F : (R.ι (toFull g₁) : ↥(modularFunctionFieldC (ResidueField A) N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceFst (P.fstDiv Daux)) := by
    rw [ι_toFull]; exact hL₁ hg₁L
  have hg₂F : (R.ι (toFull g₂) : ↥(modularFunctionFieldC (ResidueField A) N)) ∈
      riemannRochSpace (Finsupp.mapDomain P.reduceSnd (P.sndDiv Daux)) := by
    rw [ι_toFull]; exact hL₂ hg₂L
  have hnode : ∀ s ∈ nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W, ∃ c : ResidueField A,
      s.1.HasValue (R.ι (toFull g₁) : ↥(modularFunctionFieldC (ResidueField A) N)) c ∧
      s.2.HasValue (R.ι (toFull g₂) : ↥(modularFunctionFieldC (ResidueField A) N)) c := by
    intro s hs
    obtain ⟨v, hvW, rfl⟩ := (mem_nodePairsOfPlaces_iff _ _ _).mp hs
    by_cases hvw : v = w
    · subst hvw
      exact ⟨0, by rw [ι_toFull]; exact hg₁val, by rw [ι_toFull]; exact hg₂val⟩
    · refine ⟨γ₀, ?_, ?_⟩
      · rw [ι_toFull]; exact hg₁W v (Finset.mem_erase.mpr ⟨hvw, hvW⟩)
      · rw [ι_toFull]
        refine hg₂W _ (Finset.mem_erase.mpr ⟨?_, hWfrob v hvW⟩)
        intro h
        change arithFrobC q (ResidueField A) N • v = w' at h
        rw [hw', hfrob, hfrob] at h
        exact hvw (hφinj h)
  obtain ⟨G, hG₁, hG₂, hGL, hr₁, hr₂, -⟩ :=
    IsModel.exists_mem_riemannRochSpace_residue_eq_forall_arithmeticGalois_smul_eq_of_isGoodDiv hqN hW R hR hRL hNV hO
      ∅ (fun _ h => absurd h (Set.notMem_empty _)) Daux (fun V' => hDaux0 V') hgood
      (fun _ _ _ h => absurd h (Set.notMem_empty _)) hdeg₁ hdeg₂ (toFull g₁) (toFull g₂) hg₁F hg₂F hnode
  have hresG₁ : R.residue₁ ⟨G, hG₁⟩ = g₁ := by rw [residue₁_apply, hr₁, ι_toFull]
  have hresG₂ : R.residue₂ ⟨G, hG₂⟩ = g₂ := by rw [residue₂_apply, hr₂, ι_toFull]
  have hg₁ne : g₁ ≠ 0 := by intro h; rw [h, Place.ord_zero] at hg₁d; exact zero_ne_one hg₁d
  have hG0 : G ≠ 0 := by
    intro h0
    apply hg₁ne
    rw [← hresG₁]
    have : (⟨G, hG₁⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hGpole : ∀ V', V'.ord G < 0 → (∃ i, Q₁ i = V') ∨ (∃ j, Q₂ j = V') := by
    intro V' hV'
    apply hDaux_cases
    rcases (mem_riemannRochSpace_iff.mp hGL) V' with h | h
    · exact absurd h hG0
    · omega
  have hGpoleZW : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V'.ord G < 0 →
      (P.IsStrictFst V' ∧ P.reduceFst V' ∉ (↑(Z ∪ W) : Set _)) ∨ (P.IsStrictSnd V' ∧ P.reduceSnd V' ∉ (↑(Z ∪ W) : Set _)) := by
    intro V' hV'
    rcases hGpole V' hV' with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨hQ₁ i, fun h => hB₁ i (Finset.mem_coe.mp h)⟩
    · exact Or.inr ⟨hQ₂ j, fun h => hB₂ j (Finset.mem_coe.mp h)⟩
  have hZWcusp : ∀ V', IsInftySide P V' → P.reduceFst V' ∈ (↑(Z ∪ W) : Set _) ∧ P.reduceSnd V' ∈ (↑(Z ∪ W) : Set _) :=
    fun V' h => ⟨Finset.mem_coe.mpr (Finset.mem_union_left _ (hZna _ (hInftyNA V' h))),
      Finset.mem_coe.mpr (Finset.mem_union_left _ (hZna _ (hInftyNA' V' h)))⟩
  have hZWcusp' : ∀ V', IsZeroSide P V' → P.reduceFst V' ∈ (↑(Z ∪ W) : Set _) ∧ P.reduceSnd V' ∈ (↑(Z ∪ W) : Set _) :=
    fun V' h => ⟨Finset.mem_coe.mpr (Finset.mem_union_left _ (hZna _ (hZeroNA' V' h))),
      Finset.mem_coe.mpr (Finset.mem_union_left _ (hZna _ (hZeroNA V' h)))⟩

  obtain ⟨hVw, hVs₁, hVs₂⟩ := hV
  have hVsnd' : P.reduceSnd V = w' := by
    rcases MOVNCore.trichotomy P V with h | h | ⟨-, h⟩
    · exact absurd h hVs₁
    · exact absurd h hVs₂
    · rw [h, hVw, hw', hfrob]
  have hVsnd : P.reduceSnd V ∈ W := by rw [hVsnd']; exact hw'W
  have hVfst : P.reduceFst V ∈ W := by rw [hVw]; exact hw

  have hDauxV : Daux V = 0 := by
    by_contra h
    rcases hDaux_cases V h with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact hB₁W i (by rw [hi]; exact hVfst)
    · exact hB₂W j (by rw [hj]; exact hVsnd)
  obtain ⟨c, hc⟩ := MOVNCore.exists_hasValue_of_ord_nonneg V (MOVNCore.ord_nonneg_of_mem_riemannRochSpace hGL V hDauxV)
  have hf0 : G - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c ≠ 0 := by
    intro h0
    have hGc : G = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c := sub_eq_zero.mp h0
    have hcA : c ∈ A := (R.R₁.algebraMap_mem_iff c).mp (by rw [← hGc]; exact hG₁)
    have hconst : g₁ = algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A ⟨c, hcA⟩) := by
      rw [← hresG₁]
      have hx : (⟨G, hG₁⟩ : R.R₁.integers) =
          ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (((⟨c, hcA⟩ : A) : AlgebraicClosure ℚ)),
            MOVNCore.algebraMap_mem_integers₁ R ⟨c, hcA⟩⟩ :=
        Subtype.ext hGc
      rw [hx, MOVNCore.residue₁_algebraMap]
    rw [hconst, MOVNCore.ord_algebraMap_eq_zero] at hg₁d
    exact zero_ne_one hg₁d
  have hcA : c ∈ A := MOVNCore.mem_of_hasValue R hR hO hcusp hsplit hInftyNA hZeroNA hφaff (↑(Z ∪ W)) hZWcusp hZWcusp'
    G hG₁ hG₂ hGpoleZW V (Finset.mem_coe.mpr (Finset.mem_union_right _ hVfst)) (Finset.mem_coe.mpr (Finset.mem_union_right _ hVsnd))
    c hc hf0
  set a : A := ⟨c, hcA⟩ with ha_def

  have hf₁ : G - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c ∈ R.R₁.integers :=
    sub_mem hG₁ (MOVNCore.algebraMap_mem_integers₁ R a)
  have hf₂ : G - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c ∈ R.R₂.integers :=
    sub_mem hG₂ (MOVNCore.algebraMap_mem_integers₂ R a)
  set cbar : ResidueField A := IsLocalRing.residue A a with hcbar
  have hrf₁ : R.residue₁ ⟨_, hf₁⟩ = g₁ - algebraMap (ResidueField A) _ cbar := by
    rw [← hresG₁]; exact MOVNCore.residue₁_sub_algebraMap R G hG₁ a hf₁
  have hrf₂ : R.residue₂ ⟨_, hf₂⟩ = g₂ - algebraMap (ResidueField A) _ cbar := by
    rw [← hresG₂]; exact MOVNCore.residue₂_sub_algebraMap R G hG₂ a hf₂
  have hfV : 0 < V.ord (G - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c) :=
    MOVNCore.ord_sub_pos_of_hasValue V hc hf0
  have hcbar0 : cbar = 0 := by
    by_contra hcb
    have hrf₁0 : R.residue₁ ⟨_, hf₁⟩ ≠ 0 := by
      rw [hrf₁]; intro h0
      have hconst : g₁ = algebraMap (ResidueField A) _ cbar := sub_eq_zero.mp h0
      rw [hconst, MOVNCore.ord_algebraMap_eq_zero] at hg₁d
      exact zero_ne_one hg₁d
    have hrf₂0 : R.residue₂ ⟨_, hf₂⟩ ≠ 0 := by
      rw [hrf₂]; intro h0
      have hconst : g₂ = algebraMap (ResidueField A) _ cbar := sub_eq_zero.mp h0
      rw [hconst, MOVNCore.ord_algebraMap_eq_zero] at hg₂d
      exact zero_ne_one hg₂d
    obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ hf0
    have hDfpole : ∀ V', Df V' < 0 →
        (P.IsStrictFst V' ∧ P.reduceFst V' ∉ (↑(Z ∪ W) : Set _)) ∨ (P.IsStrictSnd V' ∧ P.reduceSnd V' ∉ (↑(Z ∪ W) : Set _)) := by
      intro V' hV'
      rw [hDf] at hV'
      exact hGpoleZW V' (MOVNCore.ord_neg_of_ord_sub_const_neg V' hV').2
    have hreg₁ : 0 ≤ (P.reduceFst V).ord (R.residue₁ ⟨_, hf₁⟩) := by
      rw [hrf₁]
      exact MOVNCore.ord_sub_const_nonneg _
        (MOVNCore.ord_nonneg_of_mem_riemannRochSpace hg₁L _ (by rw [hsumU, if_neg (fun h => hU₁W _ h hVfst)])) cbar
    have hreg₂ : 0 ≤ (P.reduceSnd V).ord (R.residue₂ ⟨_, hf₂⟩) := by
      rw [hrf₂]
      exact MOVNCore.ord_sub_const_nonneg _
        (MOVNCore.ord_nonneg_of_mem_riemannRochSpace hg₂L _ (by rw [hsumU, if_neg (fun h => hU₂W _ h hVsnd)])) cbar
    rcases MOVNCore.one_le_ord_residue_or R hR hO hcusp hsplit _ hf₁ hf₂ hrf₁0 hrf₂0 Df hDf (↑(Z ∪ W)) hDfpole hZWcusp hZWcusp'
        V (by rw [hDf]; exact hfV) (Finset.mem_coe.mpr (Finset.mem_union_right _ hVfst))
        (Finset.mem_coe.mpr (Finset.mem_union_right _ hVsnd)) hreg₁ hreg₂ with h | h
    · rw [hrf₁, hVw] at h
      exact hcb (MOVNCore.eq_of_ord_sub_pos_of_hasValue _ hg₁val (by omega))
    · rw [hrf₂, hVsnd'] at h
      exact hcb (MOVNCore.eq_of_ord_sub_pos_of_hasValue _ hg₂val (by omega))
  have ha : a ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.residue_eq_zero_iff a).mp hcbar0

  have hunit₁ : ∀ z : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N), z.HasValue g₁ γ₀ → z.ord g₁ = 0 := fun z hz => by
    have := MOVNCore.ord_sub_eq_zero_of_hasValue_ne z hz hγ₀0
    rwa [map_zero, sub_zero] at this
  have hunit₂ : ∀ z : Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N), z.HasValue g₂ γ₀ → z.ord g₂ = 0 := fun z hz => by
    have := MOVNCore.ord_sub_eq_zero_of_hasValue_ne z hz hγ₀0
    rwa [map_zero, sub_zero] at this
  refine ⟨G, hG₁, hG₂, Z, ?_, ?_, ?_, ?_, ?_, hZna, hZfix, ?_, a, ha, ?_⟩
  · intro V' hV'
    rcases hGpole V' hV' with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl (hQ₁ i)
    · exact Or.inr (hQ₂ j)
  · intro V' hV'
    have haff₁ : ∀ i, IsAffineGeomPlace (ResidueField A) N (P.reduceFst (Q₁ i)) :=
      fun i => by by_contra h; exact hB₁Z i (hZna _ h)
    have haff₂ : ∀ j, IsAffineGeomPlace (ResidueField A) N (P.reduceSnd (Q₂ j)) :=
      fun j => by by_contra h; exact hB₂Z j (hZna _ h)
    rcases hGpole V' hV' with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · refine ⟨haff₁ i, ?_⟩
      rw [← (hQ₁ i).1]
      exact hφaff _ (haff₁ i)
    · refine ⟨?_, haff₂ j⟩
      rw [(hQ₂ j).1]
      exact hφaff _ (haff₂ j)
  · rw [hresG₁]; exact hg₁d
  · rw [hresG₂]; exact hg₂d
  · intro v hvW hvw
    refine ⟨?_, ?_⟩
    · rw [hresG₁]; exact hunit₁ v (hg₁W v (Finset.mem_erase.mpr ⟨hvw, hvW⟩))
    · rw [hresG₂]
      refine hunit₂ _ (hg₂W _ (Finset.mem_erase.mpr ⟨?_, hWfrob v hvW⟩))
      intro h
      rw [hw', hfrob, hfrob] at h
      exact hvw (hφinj h)
  · intro v hvZ
    obtain ⟨γ₁, hγ₁, hv₁⟩ := hg₁Z v hvZ
    obtain ⟨γ₂, hγ₂, hv₂⟩ := hg₂Z v hvZ
    have hγ₁0 : γ₁ ≠ 0 := by simpa using hγ₁
    have hγ₂0 : γ₂ ≠ 0 := by simpa using hγ₂
    refine ⟨?_, ?_⟩
    · rw [hresG₁]
      have := MOVNCore.ord_sub_eq_zero_of_hasValue_ne v hv₁ hγ₁0
      rwa [map_zero, sub_zero] at this
    · rw [hresG₂]
      have := MOVNCore.ord_sub_eq_zero_of_hasValue_ne v hv₂ hγ₂0
      rwa [map_zero, sub_zero] at this
  · exact hfV

set_option maxHeartbeats 3200000 in

private theorem twist
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed)
      (π : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) →
        modularFunctionFieldC (ResidueField A) N)
      (hπ : ∀ w ∈ W, w.ord (π w) = 1)
      (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (hw : w ∈ W),
      ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
          (hV : P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
          (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers) (u : (↥A)ˣ)
          (hres₁ : (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N))
            = algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A (u : A)))
          (hres₂ : (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 1)
          (htord : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
            (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') →
            V'.ord t = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V')
          (G : ↥(modularFunctionFieldBar (N * q))) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers)
          (Z : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
          (hpole : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
            V'.ord G < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V')
          (hpoleAff : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), V'.ord G < 0 →
            IsAffineGeomPlace (ResidueField A) N (P.reduceFst V') ∧
              IsAffineGeomPlace (ResidueField A) N (P.reduceSnd V'))
          (hw₁ : w.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 1)
          (hw₂ : (arithFrobC q (ResidueField A) N • w).ord
            (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 1)
          (hW' : ∀ v ∈ W, v ≠ w →
            v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 0 ∧
            (arithFrobC q (ResidueField A) N • v).ord
              (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 0)
          (hZna : ∀ v, ¬ IsAffineGeomPlace (ResidueField A) N v → v ∈ Z)
          (hZfix : ∀ v, frobOnPlacesGeomLevel (ResidueField A) N data hKr (frobOnPlacesGeomLevel (ResidueField A) N data hKr v)
            = v → v ∉ ssPlaces q N (ResidueField A) → v ∈ Z)
          (hZunit : ∀ v ∈ Z, v.ord (R.residue₁ ⟨G, h₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 0 ∧
            v.ord (R.residue₂ ⟨G, h₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 0)
          (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
          (hVa : 0 < V.ord (G - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ))),
          ∃ (g : ↥(modularFunctionFieldBar (N * q)))
            (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
            (hg₁ : t * g ∈ R.R₁.integers) (hg₂ : t * g ∈ R.R₂.integers) (n₁ n₂ : ℕ) (l₁ l₂ : ResidueField A),
            0 < V.ord g ∧
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              V'.ord g < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V') ∧
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              E V' = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
                - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V'
                + max (V'.ord g) 0) ∧
            (∀ V', 0 ≤ E V') ∧
            (∀ V' ∈ E.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
              (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V')) ∧
            (∀ V' ∈ E.support, ¬ IsCuspidal P V' ∧ ¬ IsCuspidal' P V') ∧
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') → V'.ord (t * g) = E V') ∧
            l₁ ≠ 0 ∧ l₂ ≠ 0 ∧
            ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E w ∧
            w.HasValue (π w ^ (-(n₁ : ℤ))
              * (R.residue₁ ⟨t * g, hg₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N))) l₁ ∧
            (arithFrobC q (ResidueField A) N • w).HasValue
              ((arithFrobC q (ResidueField A) N • π w) ^ (-(n₂ : ℤ))
                * (R.residue₂ ⟨t * g, hg₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N))) l₂ := by
  intro W hW data hKr hα hβ P R hR hRL hO π hπ w hw σ hσ V hV t ht₁ ht₂ u hres₁ hres₂ htord G h₁ h₂ Z hpole hpoleAff
    hw₁ hw₂ hW' hZna hZfix hZunit a ha hVa
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  exact tw_core hqN R hR W hW hO π hπ w hw σ hσ V hV t ht₁ ht₂ u hres₁ hres₂ htord G h₁ h₂ hpole hpoleAff hw₁ hw₂ hW'
    Z hZna hZfix hZunit a ha hVa

set_option maxHeartbeats 3200000 in

private theorem main
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed)
      (π : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) →
        modularFunctionFieldC (ResidueField A) N)
      (hπ : ∀ w ∈ W, w.ord (π w) = 1)
      (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (hw : w ∈ W),
      ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
          (hV : P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
          (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers) (u : (↥A)ˣ)
          (hres₁ : (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N))
            = algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A (u : A)))
          (hres₂ : (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 1)
          (htord : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
            (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') →
            V'.ord t = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V'),
          ∃ (g : ↥(modularFunctionFieldBar (N * q)))
            (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
            (hg₁ : t * g ∈ R.R₁.integers) (hg₂ : t * g ∈ R.R₂.integers) (n₁ n₂ : ℕ) (l₁ l₂ : ResidueField A),
            0 < V.ord g ∧
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              V'.ord g < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V') ∧
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              E V' = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
                - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V'
                + max (V'.ord g) 0) ∧
            (∀ V', 0 ≤ E V') ∧
            (∀ V' ∈ E.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
              (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V')) ∧
            (∀ V' ∈ E.support, ¬ IsCuspidal P V' ∧ ¬ IsCuspidal' P V') ∧
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') → V'.ord (t * g) = E V') ∧
            l₁ ≠ 0 ∧ l₂ ≠ 0 ∧
            ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E w ∧
            w.HasValue (π w ^ (-(n₁ : ℤ))
              * (R.residue₁ ⟨t * g, hg₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N))) l₁ ∧
            (arithFrobC q (ResidueField A) N • w).HasValue
              ((arithFrobC q (ResidueField A) N • π w) ^ (-(n₂ : ℤ))
                * (R.residue₂ ⟨t * g, hg₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N))) l₂ := by
  intro W hW data hKr hα hβ P R hR hRL hO π hπ w hw σ hσ V hV t ht₁ ht₂ u hres₁ hres₂ htord
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  obtain ⟨G, h₁, h₂, Z, hpole, hpoleAff, hw₁, hw₂, hW', hZna, hZfix, hZunit, a, ha, hVa⟩ :=
    NodeEnvelope.sideData N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hO π hπ w hw σ hσ V hV t ht₁ ht₂ u hres₁ hres₂ htord
  exact NodeEnvelope.twist N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hO π hπ w hw σ hσ V hV t ht₁ ht₂ u hres₁ hres₂ htord
    G h₁ h₂ Z hpole hpoleAff hw₁ hw₂ hW' hZna hZfix hZunit a ha hVa

end NodeEnvelope

open ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed)
      (π : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) →
        modularFunctionFieldC (ResidueField A) N)
      (hπ : ∀ w ∈ W, w.ord (π w) = 1)
      (w : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (hw : w ∈ W),
      ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
          (hV : P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V)
          (t : ↥(modularFunctionFieldBar (N * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers) (u : (↥A)ˣ)
          (hres₁ : (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N))
            = algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A (u : A)))
          (hres₂ : (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N)) = 1)
          (htord : ∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
            (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') →
            V'.ord t = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V'),
          ∃ (g : ↥(modularFunctionFieldBar (N * q)))
            (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
            (hg₁ : t * g ∈ R.R₁.integers) (hg₂ : t * g ∈ R.R₂.integers) (n₁ n₂ : ℕ) (l₁ l₂ : ResidueField A),
            0 < V.ord g ∧
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              V'.ord g < 0 → P.IsStrictFst V' ∨ P.IsStrictSnd V') ∧
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              E V' = ((arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
                - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) V'
                + max (V'.ord g) 0) ∧
            (∀ V', 0 ≤ E V') ∧
            (∀ V' ∈ E.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨
              (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V')) ∧
            (∀ V' ∈ E.support, ¬ IsCuspidal P V' ∧ ¬ IsCuspidal' P V') ∧
            (∀ V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
              (P.reduceFst V' = w ∧ ¬ P.IsStrictFst V' ∧ ¬ P.IsStrictSnd V') → V'.ord (t * g) = E V') ∧
            l₁ ≠ 0 ∧ l₂ ≠ 0 ∧
            ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.reduceFst E w ∧
            w.HasValue (π w ^ (-(n₁ : ℤ))
              * (R.residue₁ ⟨t * g, hg₁⟩ : ↥(modularFunctionFieldC (ResidueField A) N))) l₁ ∧
            (arithFrobC q (ResidueField A) N • w).HasValue
              ((arithFrobC q (ResidueField A) N • π w) ^ (-(n₂ : ℤ))
                * (R.residue₂ ⟨t * g, hg₂⟩ : ↥(modularFunctionFieldC (ResidueField A) N))) l₂ := by
  exact NodeEnvelope.main N q hq hqN A hA

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_envelope_localEquation_smul_single_sub_single
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_envelope_localEquation_smul_single_sub_single (solution)
