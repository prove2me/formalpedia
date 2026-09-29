-- Prove2me | solution 1 for ModPForms.exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/218a1ad0-9e92-55a1-90e9-a77f32d5ffeb

import Definitions.Def_CuspForm_ModPForms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic
import Theorems.Thm_ModPForms_nonempty_ssDatum_algebraicClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.Gamma0Pair.isElliptic ModularCurve.SpecializationWitnessData.addCommGroup ModularCurve.CommutingHeckeFamily.commRing_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free ModularCurve.instIsElliptic_tateBase CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteProjLineCusps HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.numberField_of_finiteDimensional ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC ModularCurve.CommutingHeckeFamily.mk.injEq ModularCurve.SpecializationWitnessData.mk.sizeOf_spec ModularCurve.SpecializationWitnessData.mk.injEq ModularCurve.CommutingHeckeFamily.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff"
p2m_attr_erase "simp" "ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T HeckeEis.binaryFormEval_mk HeckeEis.binaryFormAlphaAdj_apply_coe HeckeEis.binaryFormRepSL_apply_coe ModularCurve.ProjectiveLine.vecMulRow_snd HeckeEis.projLineRepSL_apply HeckeEis.projLineAct_one HeckeEis.projLineRep_apply HeckeEis.projLineAlphaAdj_apply ModularCurve.ProjectiveLine.vecMulRow_fst ModularCurve.ProjectiveLine.vecMul_mk HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero HeckeEis.coe_linePow ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.symPoly_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.serrePairing_apply_mk AlgebraicCurve.residueSumOffChartLinear_apply"
set_option autoImplicit false

namespace SupersingularWindow

open ModPForms

private def CoreRow (p : ℕ) (N' : ℕ) (S₀ : Set ℕ) (F : Type) [Field F] [CharP F p] : Prop :=
  ∀ (w₀ : ℤ) (φ : PowerSeries F) (lam : ℕ → F), (p : ℤ) + 2 ≤ w₀ →
    φ ∈ modPMod N' w₀ F → φ ∉ modPMod N' (w₀ - ((p : ℤ) - 1)) F →
    IsModPEigen N' S₀ w₀ φ lam →
    ∃ k' : ℤ, 2 ≤ k' ∧ k' ≤ (p : ℤ) + 1 ∧ ∃ (j : ℕ) (ψ : PowerSeries F) (mu : ℕ → F),
      ψ ∈ modPMod N' k' F ∧ IsModPEigen N' S₀ k' ψ mu ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → mu ℓ = (ℓ : F) ^ j * lam ℓ

private theorem cast_pow_p_sub_one (p : ℕ) (hp : p.Prime) (F : Type) [Field F] [CharP F p]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) : ((ℓ : F)) ^ (p - 1) = 1 := by
  haveI := Fact.mk hp
  have hy : ((ℓ : ZMod p)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h).symm
  have hz : ((ℓ : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hy
  have hmap : ((ℓ : F)) = (ZMod.castHom (dvd_refl p) F) ((ℓ : ZMod p)) := by
    rw [map_natCast]
  rw [hmap, ← map_pow, hz, map_one]

private theorem walk_step (p : ℕ) (hp : p.Prime) (N' : ℕ) (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (F : Type) [Field F] [CharP F p] (dat : SSDatum p N' S₀ F) (k : ℤ) (hk1 : 1 ≤ k)
    (v : dat.S (k + ((p : ℤ) + 1))) (sys : ℕ → F)
    (hv0 : letI := dat.addCommGroup (k + ((p : ℤ) + 1)); v ≠ 0)
    (hveig : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ →
      letI := dat.addCommGroup (k + ((p : ℤ) + 1)); letI := dat.module (k + ((p : ℤ) + 1));
      dat.T (k + ((p : ℤ) + 1)) ℓ v = sys ℓ • v) :
    ∃ u : dat.S k, (letI := dat.addCommGroup k; u ≠ 0) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ →
        letI := dat.addCommGroup k; letI := dat.module k;
        dat.T k ℓ u = ((ℓ : F) ^ (p - 2) * sys ℓ) • u := by
  letI := dat.addCommGroup k; letI := dat.module k
  letI := dat.addCommGroup (k + ((p : ℤ) + 1)); letI := dat.module (k + ((p : ℤ) + 1))
  refine ⟨(dat.bIso k hk1).symm v, fun hu0 => hv0 ?_, fun ℓ hℓ hℓN hℓS => ?_⟩
  · rw [← (dat.bIso k hk1).apply_symm_apply v, hu0, map_zero]
  · have hℓp : ℓ ≠ p := fun he => hℓS (he ▸ hS₀p)
    have hx0 : (ℓ : F) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff F p]
      exact fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h).symm
    set u := (dat.bIso k hk1).symm v with hu
    have hbu : dat.bIso k hk1 u = v := (dat.bIso k hk1).apply_symm_apply v
    have hequi := dat.bIso_equivariant k hk1 ℓ hℓ hℓN hℓS u
    rw [hbu] at hequi
    have hTv := hveig ℓ hℓ hℓN hℓS
    rw [hequi] at hTv
    have hsv : (sys ℓ) • v = dat.bIso k hk1 ((sys ℓ) • u) := by rw [map_smul, hbu]
    rw [hsv, ← map_smul] at hTv
    have hkey : (ℓ : F) • dat.T k ℓ u = (sys ℓ) • u := (dat.bIso k hk1).injective hTv
    have hscale := congrArg (fun z => ((ℓ : F) ^ (p - 2)) • z) hkey
    simp only [smul_smul] at hscale
    have hfer : (ℓ : F) ^ (p - 2) * (ℓ : F) = 1 := by
      rw [show (ℓ : F) ^ (p - 2) * (ℓ : F) = (ℓ : F) ^ (p - 2 + 1) by rw [pow_succ]]
      rw [show p - 2 + 1 = p - 1 from by have := hp.two_le; omega]
      exact cast_pow_p_sub_one p hp F hℓ hℓp
    rw [hfer, one_smul] at hscale
    exact hscale

private theorem ss_walk (p : ℕ) (hp : p.Prime) (N' : ℕ) (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (F : Type) [Field F] [CharP F p] (dat : SSDatum p N' S₀ F) (n : ℕ) :
    ∀ (k : ℤ), 1 ≤ k → k ≤ (p : ℤ) + 1 + (n : ℤ) * ((p : ℤ) + 1) →
    ∀ (v : dat.S k), (letI := dat.addCommGroup k; v ≠ 0) →
    ∀ (sys : ℕ → F), (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ →
      letI := dat.addCommGroup k; letI := dat.module k; dat.T k ℓ v = sys ℓ • v) →
    ∃ (k' : ℤ) (m : ℕ), 1 ≤ k' ∧ k' ≤ (p : ℤ) + 1 ∧
      ∃ w : dat.S k', (letI := dat.addCommGroup k'; w ≠ 0) ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ →
          letI := dat.addCommGroup k'; letI := dat.module k';
          dat.T k' ℓ w = ((ℓ : F) ^ ((p - 2) * m) * sys ℓ) • w := by
  induction n with
  | zero =>
    intro k hk1 hbound v hv0 sys hsys
    refine ⟨k, 0, hk1, by push_cast at hbound; linarith, v, hv0, fun ℓ hℓ hℓN hℓS => ?_⟩
    rw [Nat.mul_zero, pow_zero, one_mul]
    exact hsys ℓ hℓ hℓN hℓS
  | succ n ih =>
    intro k hk1 hbound v hv0 sys hsys
    by_cases hwin : k ≤ (p : ℤ) + 1
    · refine ⟨k, 0, hk1, hwin, v, hv0, fun ℓ hℓ hℓN hℓS => ?_⟩
      rw [Nat.mul_zero, pow_zero, one_mul]
      exact hsys ℓ hℓ hℓN hℓS
    · rw [not_le] at hwin
      obtain ⟨k₀, rfl⟩ : ∃ k₀ : ℤ, k = k₀ + ((p : ℤ) + 1) := ⟨k - ((p : ℤ) + 1), by ring⟩
      have hk₀1 : 1 ≤ k₀ := by linarith
      obtain ⟨u, hu0, hueig⟩ :=
        walk_step p hp N' S₀ hS₀p F dat k₀ hk₀1 v sys hv0 hsys
      have hb₀ : k₀ ≤ (p : ℤ) + 1 + (n : ℤ) * ((p : ℤ) + 1) := by
        push_cast at hbound
        linarith
      obtain ⟨k', m', h1, h2, w, hw0, hweig⟩ :=
        ih k₀ hk₀1 hb₀ u hu0 (fun ℓ => (ℓ : F) ^ (p - 2) * sys ℓ) hueig
      refine ⟨k', m' + 1, h1, h2, w, hw0, fun ℓ hℓ hℓN hℓS => ?_⟩
      have hsc : (ℓ : F) ^ ((p - 2) * (m' + 1)) * sys ℓ
          = (ℓ : F) ^ ((p - 2) * m') * ((ℓ : F) ^ (p - 2) * sys ℓ) := by
        rw [show (p - 2) * (m' + 1) = (p - 2) * m' + (p - 2) from by ring, pow_add]
        ring
      rw [hsc]
      exact hweig ℓ hℓ hℓN hℓS

private theorem coreRow_of_ssDatum (p : ℕ) (hp : p.Prime) (N' : ℕ) [NeZero N']
    (S₀ : Set ℕ) (hS₀p : p ∈ S₀) (F : Type) [Field F] [CharP F p]
    (hdat : Nonempty (SSDatum p N' S₀ F)) : CoreRow p N' S₀ F := by
  obtain ⟨dat⟩ := hdat
  intro w₀ φ lam hw2 hφ hnot heig
  letI := dat.addCommGroup w₀; letI := dat.module w₀
  have hv0 : dat.res w₀ hw2 ⟨φ, hφ⟩ ≠ 0 := fun h0 => hnot (dat.res_ker w₀ hw2 φ hφ h0)
  have hveig : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ →
      dat.T w₀ ℓ (dat.res w₀ hw2 ⟨φ, hφ⟩) = lam ℓ • dat.res w₀ hw2 ⟨φ, hφ⟩ := by
    intro ℓ hℓ hℓN hℓS
    have hsub : (⟨ModPForms.heckePS w₀ ℓ φ, dat.hecke_stable w₀ hw2 ℓ hℓ hℓN hℓS φ hφ⟩ :
        ↥(modPMod N' w₀ F)) = lam ℓ • (⟨φ, hφ⟩ : ↥(modPMod N' w₀ F)) := by
      apply Subtype.ext
      rw [SetLike.val_smul]
      exact heig.2 ℓ hℓ hℓN hℓS
    have := dat.res_equivariant w₀ hw2 ℓ hℓ hℓN hℓS φ hφ
    rw [hsub, map_smul] at this
    exact this.symm
  have hw1 : (1 : ℤ) ≤ w₀ := by linarith
  have h0 : (0 : ℤ) ≤ w₀ := by linarith
  have hbound : w₀ ≤ (p : ℤ) + 1 + ((w₀.toNat : ℤ)) * ((p : ℤ) + 1) := by
    have hcast : ((w₀.toNat : ℤ)) = w₀ := Int.toNat_of_nonneg h0
    rw [hcast]
    have h1 : w₀ ≤ w₀ * ((p : ℤ) + 1) := le_mul_of_one_le_right h0 (by linarith)
    linarith
  obtain ⟨k', m, hk1, hkp, w, hw0, hweig⟩ :=
    ss_walk p hp N' S₀ hS₀p F dat w₀.toNat w₀ hw1 hbound
      (dat.res w₀ hw2 ⟨φ, hφ⟩) hv0 lam hveig
  obtain ⟨k'', h2'', hp1'', j, ψ, nu, hψ, heignu, hnu⟩ :=
    dat.pullback k' hk1 hkp w (fun ℓ => (ℓ : F) ^ ((p - 2) * m) * lam ℓ) hw0 hweig
  refine ⟨k'', h2'', hp1'', j + (p - 2) * m, ψ, nu, hψ, heignu, fun ℓ hℓ hℓN hℓS => ?_⟩
  rw [hnu ℓ hℓ hℓN hℓS, pow_add]
  ring

private theorem heckePS_congr_weight (p : ℕ) (hp : p.Prime) (F : Type) [Field F] [CharP F p]
    {k k' : ℤ} (hkk' : ((p : ℤ) - 1) ∣ k - k') {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (φ : PowerSeries F) :
    heckePS k ℓ φ = heckePS k' ℓ φ := by
  have hx0 : (ℓ : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F p]
    exact fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h).symm
  have hu : ((ℓ : F)) ^ ((p : ℤ) - 1) = 1 := by
    haveI := Fact.mk hp
    have hy : ((ℓ : ZMod p)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h).symm
    have hz : ((ℓ : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hy
    have hmap : ((ℓ : F)) = (ZMod.castHom (dvd_refl p) F) ((ℓ : ZMod p)) := by
      rw [map_natCast]
    rw [show ((p : ℤ) - 1) = ((p - 1 : ℕ) : ℤ) by rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one],
      zpow_natCast, hmap, ← map_pow, hz, map_one]
  obtain ⟨t, ht⟩ := hkk'
  have hfac : ((ℓ : F)) ^ (k - 1) = ((ℓ : F)) ^ (k' - 1) := by
    have h1 : k - 1 = (k' - 1) + ((p : ℤ) - 1) * t := by rw [← ht]; ring
    rw [h1, zpow_add₀ hx0, zpow_mul, hu, one_zpow, mul_one]
  ext n
  simp only [ModPForms.heckePS, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [hfac]
  · rfl

private theorem isModPEigen_congr_weight (p : ℕ) (hp : p.Prime) (N' : ℕ) (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (F : Type) [Field F] [CharP F p] {k k' : ℤ} (hkk' : ((p : ℤ) - 1) ∣ k - k')
    (φ : PowerSeries F) (lam : ℕ → F) (h : IsModPEigen N' S₀ k φ lam) :
    IsModPEigen N' S₀ k' φ lam := by
  unfold ModPForms.IsModPEigen at h ⊢
  obtain ⟨hne, heq⟩ := h
  refine ⟨hne, fun ℓ hℓ hℓN hℓS => ?_⟩
  have hℓp : ℓ ≠ p := fun he => hℓS (he ▸ hS₀p)
  rw [← heckePS_congr_weight p hp F hkk' hℓ hℓp φ]
  exact heq ℓ hℓ hℓN hℓS

private theorem trichotomy_descent (p : ℕ) (N' : ℕ) (F : Type) [Field F] (n : ℕ) :
    ∀ (k : ℤ), 2 ≤ k → k ≤ (p : ℤ) + 1 + (n : ℤ) * ((p : ℤ) - 1) →
    ∀ (φ : PowerSeries F), φ ∈ modPMod N' k F →
    (∃ k' : ℤ, 2 ≤ k' ∧ k' ≤ (p : ℤ) + 1 ∧ ((p : ℤ) - 1) ∣ k - k' ∧ φ ∈ modPMod N' k' F) ∨
      (∃ w₀ : ℤ, (p : ℤ) + 2 ≤ w₀ ∧ ((p : ℤ) - 1) ∣ k - w₀ ∧ φ ∈ modPMod N' w₀ F ∧
        φ ∉ modPMod N' (w₀ - ((p : ℤ) - 1)) F) := by
  induction n with
  | zero =>
    intro k hk2 hbound φ hφ
    refine Or.inl ⟨k, hk2, ?_, by simp, hφ⟩
    push_cast at hbound
    linarith
  | succ n ih =>
    intro k hk2 hbound φ hφ
    by_cases hwin : k ≤ (p : ℤ) + 1
    · exact Or.inl ⟨k, hk2, hwin, by simp, hφ⟩
    · rw [not_le] at hwin
      by_cases hmem : φ ∈ modPMod N' (k - ((p : ℤ) - 1)) F
      · have h2' : 2 ≤ k - ((p : ℤ) - 1) := by linarith
        have hb' : k - ((p : ℤ) - 1) ≤ (p : ℤ) + 1 + (n : ℤ) * ((p : ℤ) - 1) := by
          push_cast at hbound
          linarith
        rcases ih (k - ((p : ℤ) - 1)) h2' hb' φ hmem with
          ⟨k', h1, h2, h3, h4⟩ | ⟨w₀, h1, h2, h3, h4⟩
        · refine Or.inl ⟨k', h1, h2, ?_, h4⟩
          have he : k - k' = ((p : ℤ) - 1) + (k - ((p : ℤ) - 1) - k') := by ring
          rw [he]
          exact dvd_add (dvd_refl _) h3
        · refine Or.inr ⟨w₀, h1, ?_, h3, h4⟩
          have he : k - w₀ = ((p : ℤ) - 1) + (k - ((p : ℤ) - 1) - w₀) := by ring
          rw [he]
          exact dvd_add (dvd_refl _) h2
      · exact Or.inr ⟨k, by linarith, by simp, hφ, hmem⟩

private theorem filtration_trichotomy (p : ℕ) (hp : p.Prime) (hp5 : 3 ≤ p) (N' : ℕ) [NeZero N']
    (F : Type) [Field F] [CharP F p] (k : ℤ) (hk : 2 ≤ k) (φ : PowerSeries F)
    (hφ : φ ∈ modPMod N' k F) :
    (∃ k' : ℤ, 2 ≤ k' ∧ k' ≤ (p : ℤ) + 1 ∧ ((p : ℤ) - 1) ∣ k - k' ∧ φ ∈ modPMod N' k' F) ∨
      (∃ w₀ : ℤ, (p : ℤ) + 2 ≤ w₀ ∧ ((p : ℤ) - 1) ∣ k - w₀ ∧ φ ∈ modPMod N' w₀ F ∧
        φ ∉ modPMod N' (w₀ - ((p : ℤ) - 1)) F) := by
  have _ := hp
  have hp5' : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
  have h0 : (0 : ℤ) ≤ k - 2 := by linarith
  refine trichotomy_descent p N' F (k - 2).toNat k hk ?_ φ hφ
  have hcast : (((k - 2).toNat : ℤ)) = k - 2 := Int.toNat_of_nonneg h0
  rw [hcast]
  have h1 : k - 2 ≤ (k - 2) * ((p : ℤ) - 1) := le_mul_of_one_le_right h0 (by linarith)
  linarith

private theorem window_of_coreRow (p : ℕ) (hp : p.Prime) (hp5 : 3 ≤ p) (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀) (F : Type) [Field F] [CharP F p]
    (hcore : CoreRow p N' S₀ F)
    (k : ℤ) (hk : 2 ≤ k) (φ : PowerSeries F) (lam : ℕ → F)
    (hφ : φ ∈ modPMod N' k F) (heig : IsModPEigen N' S₀ k φ lam) :
    ∃ k' : ℤ, 2 ≤ k' ∧ k' ≤ (p : ℤ) + 1 ∧ ∃ (j : ℕ) (ψ : PowerSeries F) (mu : ℕ → F),
      ψ ∈ modPMod N' k' F ∧ IsModPEigen N' S₀ k' ψ mu ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → mu ℓ = (ℓ : F) ^ j * lam ℓ := by
  have _ := hpN'
  have _ := hS₀fin
  rcases filtration_trichotomy p hp hp5 N' F k hk φ hφ with
    ⟨k', h2, hp1, hdvd, hmem⟩ | ⟨w₀, hw2, hdvd, hmem, hnot⟩
  · refine ⟨k', h2, hp1, 0, φ, lam, hmem,
      isModPEigen_congr_weight p hp N' S₀ hS₀p F hdvd φ lam heig, ?_⟩
    intro ℓ _ _ _
    rw [pow_zero, one_mul]
  · exact hcore w₀ φ lam hw2 hmem hnot
      (isModPEigen_congr_weight p hp N' S₀ hS₀p F hdvd φ lam heig)

end SupersingularWindow

open ModPForms SupersingularWindow in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N' : ℕ) [NeZero N'] (hpN' : ¬ p ∣ N')
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (hS₀p : p ∈ S₀)
    (k : ℤ) (hk : 2 ≤ k) (φ : PowerSeries (AlgebraicClosure (ZMod p))) (lam : ℕ → AlgebraicClosure (ZMod p))
    (hφ : φ ∈ modPMod N' k (AlgebraicClosure (ZMod p))) (heig : IsModPEigen N' S₀ k φ lam) :
    ∃ k' : ℤ, 2 ≤ k' ∧ k' ≤ (p : ℤ) + 1 ∧ ∃ (j : ℕ) (ψ : PowerSeries (AlgebraicClosure (ZMod p))) (mu : ℕ → AlgebraicClosure (ZMod p)),
      ψ ∈ modPMod N' k' (AlgebraicClosure (ZMod p)) ∧ IsModPEigen N' S₀ k' ψ mu ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N' → ℓ ∉ S₀ → mu ℓ = (ℓ : AlgebraicClosure (ZMod p)) ^ j * lam ℓ := by
  haveI : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_ringHom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p
  exact window_of_coreRow p Fact.out (by omega) N' hpN' S₀ hS₀fin hS₀p _
    (coreRow_of_ssDatum p Fact.out N' S₀ hS₀p _
      (ModPForms.nonempty_ssDatum_algebraicClosure p hp5 N' hpN' S₀ hS₀p)) k hk φ lam hφ heig

end S_ModPForms_exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure
end P2MW
export P2MW.S_ModPForms_exists_weight_le_succ_mem_modPMod_isModPEigen_pow_mul_of_isModPEigen_algebraicClosure (solution)
