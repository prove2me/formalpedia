-- Prove2me | solution 1 for ModularCurve.natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/50867099-80aa-5813-b13f-dcfb9fbd82d2

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_sub_mem_inertiaInvariantPoints
import Theorems.Thm_ModularCurve_heckeGen_smul_galois_smul
import Theorems.Thm_ModularCurve_relindex_jZeroToricTorsion_pos_and_le_natCard_jZeroTorsion
import Theorems.Thm_ModularCurve_exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.Gamma0Pair.isElliptic ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "ModularCurve.LevelOnePhi.instAddCommGroup WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst"
p2m_attr_erase "instance" "instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.GaussReduction.isLocalHom_constToGauss instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.numberField_of_finiteDimensional ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.jqNModC_one ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.qExpandAlgHomC_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_laurentDescent_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.symPoly_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj ExtCitation.LocalLevel.coe_smul_OO"
p2m_attr_erase "simp" "AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

open ModularCurve
set_option autoImplicit false

namespace P2MG1c

open ModularCurve

section Group

variable {G : Type*} [AddCommGroup G]

theorem card_le_mul_card_inf (T K V : AddSubgroup G) (hKV : K ≤ V) (B : ℕ)
    (hfin : T.relIndex V ≠ 0) (hB : T.relIndex V ≤ B) :
    Nat.card K ≤ B * Nat.card ↥(T ⊓ K) := by
  have h1 : T.relIndex K ≤ B := (AddSubgroup.relIndex_le_of_le_right hKV hfin).trans hB
  have h2 : Nat.card ↥(T.addSubgroupOf K) * (T.addSubgroupOf K).index = Nat.card K :=
    AddSubgroup.card_mul_index _
  have h3 : Nat.card ↥(T.addSubgroupOf K) = Nat.card ↥(T ⊓ K) := by
    rw [← AddSubgroup.inf_addSubgroupOf_right]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe inf_le_right).toEquiv
  have h4 : (T.addSubgroupOf K).index = T.relIndex K := rfl
  rw [← h2, h3, h4, mul_comm]
  exact Nat.mul_le_mul_right _ h1

theorem card_le_mul_sq (f : G →+ G) (S T V : AddSubgroup G)
    (hS : ∀ x ∈ S, f x ∈ S) (hT : ∀ x ∈ S, f x ∈ T) (hTk : ∀ x ∈ T, f x = 0)
    (hKV : ∀ x ∈ S, f x = 0 → x ∈ V)
    (B : ℕ) (hfin : T.relIndex V ≠ 0) (hB : T.relIndex V ≤ B) :
    Nat.card S ≤ B * Nat.card ↥(T ⊓ S) ^ 2 := by
  classical
  rcases finite_or_infinite S with hSfin | hSinf
  · let fS : S →+ G := f.comp S.subtype
    let K : AddSubgroup G := S ⊓ f.ker
    have hker : fS.ker = K.addSubgroupOf S := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, K, AddSubgroup.mem_inf, fS,
        AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    have hKS : K ≤ S := inf_le_left
    have hcardK : Nat.card fS.ker = Nat.card K := by
      rw [hker]; exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hKS).toEquiv
    have hrange : fS.range ≤ T ⊓ S := by
      rintro _ ⟨x, rfl⟩
      exact ⟨hT x x.2, hS x x.2⟩
    haveI : Finite ↥(T ⊓ S) := Finite.of_injective (AddSubgroup.inclusion (inf_le_right : T ⊓ S ≤ S))
      (AddSubgroup.inclusion_injective _)
    have hcardS : Nat.card S = Nat.card K * Nat.card fS.range := by
      rw [← hcardK, ← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
    have hr : Nat.card fS.range ≤ Nat.card ↥(T ⊓ S) := AddSubgroup.card_le_of_le hrange
    have hKV' : K ≤ V := fun x hx => hKV x hx.1 hx.2
    have hTK : T ⊓ K = T ⊓ S := by
      ext x
      simp only [AddSubgroup.mem_inf, K, AddMonoidHom.mem_ker]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, hTk x h1⟩⟩
    have hK : Nat.card K ≤ B * Nat.card ↥(T ⊓ S) := by
      have := card_le_mul_card_inf T K V hKV' B hfin hB
      rwa [hTK] at this
    calc Nat.card S = Nat.card K * Nat.card fS.range := hcardS
      _ ≤ (B * Nat.card ↥(T ⊓ S)) * Nat.card ↥(T ⊓ S) := Nat.mul_le_mul hK hr
      _ = B * Nat.card ↥(T ⊓ S) ^ 2 := by ring
  · rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

theorem card_le_sq_mul_sq (f : G →+ G) (S T V : AddSubgroup G)
    (hS : ∀ x ∈ S, f x ∈ S) (hV : ∀ x ∈ S, f x ∈ V) (hTk : ∀ x ∈ T, f x = 0)
    (hKV : ∀ x ∈ S, f x = 0 → x ∈ V)
    (B : ℕ) (hfin : T.relIndex V ≠ 0) (hB : T.relIndex V ≤ B) :
    Nat.card S ≤ B ^ 2 * Nat.card ↥(T ⊓ S) ^ 2 := by
  classical
  rcases finite_or_infinite S with hSfin | hSinf
  · let fS : S →+ G := f.comp S.subtype
    let K : AddSubgroup G := S ⊓ f.ker
    have hker : fS.ker = K.addSubgroupOf S := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, K, AddSubgroup.mem_inf, fS,
        AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    have hKS : K ≤ S := inf_le_left
    have hcardK : Nat.card fS.ker = Nat.card K := by
      rw [hker]; exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hKS).toEquiv

    let R : AddSubgroup G := V ⊓ S
    have hrange : fS.range ≤ R := by
      rintro _ ⟨x, rfl⟩
      exact ⟨hV x x.2, hS x x.2⟩
    haveI : Finite ↥R := Finite.of_injective (AddSubgroup.inclusion (inf_le_right : R ≤ S))
      (AddSubgroup.inclusion_injective _)
    haveI : Finite ↥(T ⊓ S) := Finite.of_injective (AddSubgroup.inclusion (inf_le_right : T ⊓ S ≤ S))
      (AddSubgroup.inclusion_injective _)
    have hcardS : Nat.card S = Nat.card K * Nat.card fS.range := by
      rw [← hcardK, ← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
    have hr : Nat.card fS.range ≤ Nat.card ↥R := AddSubgroup.card_le_of_le hrange

    have hRV : R ≤ V := inf_le_left
    have hR1 : Nat.card ↥R ≤ B * Nat.card ↥(T ⊓ R) := card_le_mul_card_inf T R V hRV B hfin hB
    have hTR : T ⊓ R ≤ T ⊓ S := inf_le_inf_left T inf_le_right
    have hR2 : Nat.card ↥(T ⊓ R) ≤ Nat.card ↥(T ⊓ S) := AddSubgroup.card_le_of_le hTR
    have hR : Nat.card fS.range ≤ B * Nat.card ↥(T ⊓ S) :=
      hr.trans (hR1.trans (Nat.mul_le_mul_left _ hR2))

    have hKV' : K ≤ V := fun x hx => hKV x hx.1 hx.2
    have hTK : T ⊓ K = T ⊓ S := by
      ext x
      simp only [AddSubgroup.mem_inf, K, AddMonoidHom.mem_ker]
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2, hTk x h1⟩⟩
    have hK : Nat.card K ≤ B * Nat.card ↥(T ⊓ S) := by
      have := card_le_mul_card_inf T K V hKV' B hfin hB
      rwa [hTK] at this
    calc Nat.card S = Nat.card K * Nat.card fS.range := hcardS
      _ ≤ (B * Nat.card ↥(T ⊓ S)) * (B * Nat.card ↥(T ⊓ S)) := Nat.mul_le_mul hK hR
      _ = B ^ 2 * Nat.card ↥(T ⊓ S) ^ 2 := by ring
  · rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

end Group

section Hecke

variable (p : ℕ) [Fact p.Prime]

scoped instance neZero_of_fact_prime : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem galois_smul_hecke_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (t : HeckeAlg) (x : JZero p) :
    (letI := heckeModuleBar p; σ • (t • x) = t • (σ • x)) := by
  letI := heckeModuleBar p
  induction t using MvPolynomial.induction_on generalizing x with
  | C a =>
    rw [heckeModuleBar_C_smul, heckeModuleBar_C_smul]
    exact map_zsmul (DistribSMul.toAddMonoidHom (JZero p) σ) a x
  | add f g hf hg => rw [add_smul, add_smul, smul_add, hf, hg]
  | mul_X f ℓ hf =>
    rw [mul_smul, mul_smul, hf]
    congr 1
    exact (heckeGen_smul_galois_smul p σ ℓ x).symm

theorem smul_sub_mem_torsionBySet (s : Set HeckeAlg) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : JZero p)
    (hx : letI := heckeModuleBar p; x ∈ (Submodule.torsionBySet HeckeAlg (JZero p) s).toAddSubgroup) :
    letI := heckeModuleBar p
    σ • x - x ∈ (Submodule.torsionBySet HeckeAlg (JZero p) s).toAddSubgroup := by
  letI := heckeModuleBar p
  have hx' : x ∈ Submodule.torsionBySet HeckeAlg (JZero p) s := hx
  have hσx : σ • x ∈ Submodule.torsionBySet HeckeAlg (JZero p) s := by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have ha : (a : HeckeAlg) • x = 0 := (Submodule.mem_torsionBySet_iff _ _).mp hx' a
    rw [← galois_smul_hecke_smul, ha]
    exact (DistribSMul.toAddMonoidHom (JZero p) σ).map_zero
  exact AddSubgroup.sub_mem _ hσx hx

theorem torsionBySet_pow_le_jZeroTorsion (q : ℕ) (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) (m : ℕ) :
    letI := heckeModuleBar p
    (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup ≤ jZeroTorsion p (q ^ m) := by
  letI := heckeModuleBar p
  intro x hx
  have hx' : x ∈ Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg) := hx
  have hq : ((q : HeckeAlg) ^ m) ∈ (↑(I ^ m) : Set HeckeAlg) := Ideal.pow_mem_pow hqI m
  have h0 : ((q : HeckeAlg) ^ m) • x = 0 := (Submodule.mem_torsionBySet_iff _ _).mp hx' ⟨_, hq⟩
  have h1 : ((q : HeckeAlg) ^ m) • x = ((q ^ m : ℕ) : ℤ) • x := by
    rw [show ((q : HeckeAlg) ^ m) = MvPolynomial.C ((q ^ m : ℕ) : ℤ) by simp,
      heckeModuleBar_C_smul]
  change x ∈ Submodule.torsionBy ℤ (JZero p) ((q ^ m : ℕ) : ℤ)
  rw [Submodule.mem_torsionBy_iff, ← h1, h0]

theorem smul_eq_of_mem_jZeroToricTorsion (A : ValuationSubring (AlgebraicClosure ℚ)) (n : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (x : JZero p)
    (hx : x ∈ jZeroToricTorsion p A n) : σ • x = x := by
  obtain ⟨-, y, hy, rfl⟩ := mem_jZeroToricTorsion.mp hx
  rw [show σ • (eisensteinNumerator p • y) = eisensteinNumerator p • (σ • y) from
    map_nsmul (DistribSMul.toAddMonoidHom (JZero p) σ) (eisensteinNumerator p) y,
    (mem_inertiaInvariantPoints.mp hy) σ hσ]

theorem jZeroToricTorsion_le_inertiaInvariantTorsion (A : ValuationSubring (AlgebraicClosure ℚ)) (n : ℕ) :
    jZeroToricTorsion p A n ≤ inertiaInvariantTorsion p A n := fun x hx =>
  ⟨(mem_jZeroToricTorsion.mp hx).1, fun σ hσ => smul_eq_of_mem_jZeroToricTorsion p A n σ hσ x hx⟩

end Hecke

theorem natCard_le_of_inputs (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) (m : ℕ)
    (hU : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), σ ∈ A.inertiaSubgroupIn ℚ →
      ∀ x : JZero p, x ∈ jZeroTorsion p (q ^ m) → σ • x - x ∈ inertiaInvariantPoints p A)
    (σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ₀ : σ₀ ∈ A.inertiaSubgroupIn ℚ)
    (hgen : ∀ x : JZero p, x ∈ jZeroTorsion p (q ^ m) → σ₀ • x = x →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x)
    (B : ℕ) (hidx : (jZeroToricTorsion p A (q ^ m)).relIndex (jZeroTorsion p (q ^ m) ⊓ inertiaInvariantPoints p A) ≠ 0)
    (hB : (jZeroToricTorsion p A (q ^ m)).relIndex (jZeroTorsion p (q ^ m) ⊓ inertiaInvariantPoints p A) ≤ B) :
    letI := heckeModuleBar p
    Nat.card ↥(Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup ≤
      B ^ 2 * Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup) ^ 2 := by
  letI := heckeModuleBar p
  let f : JZero p →+ JZero p := DistribSMul.toAddMonoidHom (JZero p) σ₀ - AddMonoidHom.id _
  have hf : ∀ x, f x = σ₀ • x - x := fun x => rfl
  refine card_le_sq_mul_sq f (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup (jZeroToricTorsion p A (q ^ m))
    (jZeroTorsion p (q ^ m) ⊓ inertiaInvariantPoints p A) ?_ ?_ ?_ ?_ B hidx hB
  · intro x hx; rw [hf]; exact smul_sub_mem_torsionBySet p _ σ₀ x hx
  · intro x hx; rw [hf]
    have hxq := torsionBySet_pow_le_jZeroTorsion p q I hqI m hx
    refine ⟨?_, hU σ₀ hσ₀ x hxq⟩

    have hxq' : ((q ^ m : ℕ) : ℤ) • x = 0 := (Submodule.mem_torsionBy_iff _ _).mp hxq
    change σ₀ • x - x ∈ Submodule.torsionBy ℤ (JZero p) ((q ^ m : ℕ) : ℤ)
    rw [Submodule.mem_torsionBy_iff]
    change ((q ^ m : ℕ) : ℤ) • (σ₀ • x - x) = 0
    rw [zsmul_sub, show ((q ^ m : ℕ) : ℤ) • (σ₀ • x) = σ₀ • (((q ^ m : ℕ) : ℤ) • x) from
      (map_zsmul (DistribSMul.toAddMonoidHom (JZero p) σ₀) _ x).symm, hxq', sub_zero]
    exact map_zero (DistribSMul.toAddMonoidHom (JZero p) σ₀)
  · intro x hx; rw [hf, smul_eq_of_mem_jZeroToricTorsion p A _ σ₀ hσ₀ x hx, sub_self]
  · intro x hx h0
    rw [hf, sub_eq_zero] at h0
    have hxq := torsionBySet_pow_le_jZeroTorsion p q I hqI m hx
    exact ⟨hxq, mem_inertiaInvariantPoints.mpr (hgen x hxq h0)⟩

end P2MG1c
p2m_reactivate "P2MW.S_ModularCurve_natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul.P2MG1c"

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) :
    letI := heckeModuleBar p
    ∃ C : ℕ, ∀ m : ℕ,
      Nat.card ↥(Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup ≤
        Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup) ^ 2 * q ^ C := by
  letI := heckeModuleBar p
  obtain ⟨σ₀, hσ₀, hgen⟩ :=
    ModularCurve.exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp p q hqp A hA
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out

  let B : ℕ := Nat.card ↥(jZeroTorsion p (eisensteinNumerator p))
  refine ⟨B ^ 2, fun m => ?_⟩
  have hm0 : q ^ m ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hpm : ¬ p ∣ q ^ m := fun h =>
    hqp (((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h))).symm
  obtain ⟨hpos, hBle⟩ := ModularCurve.relindex_jZeroToricTorsion_pos_and_le_natCard_jZeroTorsion p q hqp A hA m
  have hidx : (jZeroToricTorsion p A (q ^ m)).relIndex (jZeroTorsion p (q ^ m) ⊓ inertiaInvariantPoints p A) ≠ 0 :=
    hpos.ne'
  have hle := P2MG1c.natCard_le_of_inputs p q A I hqI m
    (fun σ hσ x hx => ModularCurve.arithmeticGalois_smul_sub_mem_inertiaInvariantPoints p A hA (q ^ m) hm0 hpm σ hσ x hx)
    σ₀ hσ₀ (fun x hx h0 => hgen m x hx h0) B hidx hBle
  have hB : B ^ 2 ≤ q ^ (B ^ 2) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hq.two_le _)
  calc Nat.card ↥(Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup
      ≤ B ^ 2 * Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup) ^ 2 := hle
    _ ≤ q ^ (B ^ 2) * Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup) ^ 2 :=
        Nat.mul_le_mul_right _ hB
    _ = Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ (Submodule.torsionBySet HeckeAlg (JZero p) (↑(I ^ m) : Set HeckeAlg)).toAddSubgroup) ^ 2 * q ^ (B ^ 2) := by ring

end S_ModularCurve_natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul
end P2MW
export P2MW.S_ModularCurve_natCard_torsionBySet_pow_le_sq_natCard_jZeroToricTorsion_inf_mul (solution)
