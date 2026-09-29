-- Prove2me | solution 1 for ModularCurve.exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5d666d9c-f47f-5a13-900d-76989005aa44

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_ModularCurve_JZeroToricTorsion
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_sub_mem_inertiaInvariantPoints
import Theorems.Thm_ExtCitation_exists_inertia_pCharacter_generator
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul
import Theorems.Thm_ModularCurve_JZero_isOpen_stabilizer
import Theorems.Thm_ValuationSubring_exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.Gamma0Pair.isElliptic ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "ModularCurve.LevelOnePhi.instAddCommGroup WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst"
p2m_attr_erase "instance" "instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.GaussReduction.isLocalHom_constToGauss instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.numberField_of_finiteDimensional ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO"
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
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.symPoly_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ExtCitation.LocalLevel.coe_smul_OO"

open ModularCurve

set_option autoImplicit false

namespace P2MIIIT

open scoped Pointwise

section functional

noncomputable def zmodModuleOfTorsion (q : ℕ) (V : Type*) [AddCommGroup V] (hV : ∀ v : V, q • v = 0) :
    Module (ZMod q) V :=
  AddCommGroup.zmodModule hV

theorem exists_addMonoidHom_zmod_apply_ne_zero (q : ℕ) [Fact q.Prime] (V : Type*) [AddCommGroup V]
    (hV : ∀ v : V, q • v = 0) (v : V) (hv : v ≠ 0) : ∃ f : V →+ ZMod q, f v ≠ 0 := by
  letI := zmodModuleOfTorsion q V hV
  have : Module.Free (ZMod q) V := Module.Free.of_divisionRing _ _
  have h := mt (Module.forall_dual_apply_eq_zero_iff (ZMod q) v).1 hv
  push_neg at h
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.toAddMonoidHom, hφ⟩

theorem exists_addMonoidHom_zmod_ne_zero (q : ℕ) [hq : Fact q.Prime] (k : ℕ)
    (M : Type*) [AddCommGroup M] (hM : ∀ m : M, q ^ k • m = 0) (m0 : M) (hm0 : m0 ≠ 0) :
    ∃ f : M →+ ZMod q, f ≠ 0 := by
  classical

  let S : Submodule ℤ M := (q : ℤ) • ⊤
  have hS : ∀ m : M, (q : ℤ) • m ∈ S := fun m => Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

  have hQ : ∃ v : M ⧸ S, v ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hdiv : ∀ m : M, ∃ m' : M, (q : ℤ) • m' = m := fun m => by
      have : (Submodule.Quotient.mk m : M ⧸ S) = 0 := hall _
      rw [Submodule.Quotient.mk_eq_zero] at this
      obtain ⟨m', -, hm'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
      exact ⟨m', hm'⟩
    have hpow : ∀ j : ℕ, ∀ m : M, ∃ m' : M, ((q : ℤ) ^ j) • m' = m := by
      intro j
      induction j with
      | zero => intro m; exact ⟨m, by simp⟩
      | succ j ih =>
        intro m
        obtain ⟨m1, hm1⟩ := ih m
        obtain ⟨m2, hm2⟩ := hdiv m1
        exact ⟨m2, by rw [pow_succ, mul_smul, hm2, hm1]⟩
    obtain ⟨m', hm'⟩ := hpow k m0
    apply hm0
    rw [← hm', ← Nat.cast_pow, natCast_zsmul]
    exact hM m'
  obtain ⟨v, hv⟩ := hQ

  have hqQ : ∀ w : M ⧸ S, q • w = 0 := by
    intro w
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective S w
    have e : (q • Submodule.Quotient.mk m : M ⧸ S) = Submodule.mkQ S (q • m) :=
      (map_nsmul (Submodule.mkQ S) q m).symm
    rw [e, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← natCast_zsmul]
    exact hS m
  obtain ⟨f, hf⟩ := exists_addMonoidHom_zmod_apply_ne_zero q (M ⧸ S) hqQ v hv
  refine ⟨f.comp (Submodule.mkQ S).toAddMonoidHom, ?_⟩
  intro hzero
  apply hf
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective S v
  exact DFunLike.congr_fun hzero m

end functional

section main

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {J : Type*} [AddCommGroup J] [DistribMulAction (L ≃ₐ[K] L) J]

def coc (x : J) (σ : L ≃ₐ[K] L) : J := σ • x - x

theorem coc_one (x : J) : coc x (1 : L ≃ₐ[K] L) = 0 := by simp [coc]

theorem coc_eq_zero_iff (x : J) (σ : L ≃ₐ[K] L) : coc x σ = 0 ↔ σ • x = x := sub_eq_zero

theorem coc_mul_of_fix (x : J) (σ u : L ≃ₐ[K] L) (hu : u • x = x) : coc x (σ * u) = coc x σ := by
  simp [coc, mul_smul, hu]

theorem coc_mul_of_inv (x : J) (σ τ : L ≃ₐ[K] L) (h : σ • (τ • x - x) = τ • x - x) :
    coc x (σ * τ) = coc x τ + coc x σ := by
  unfold coc
  rw [mul_smul]
  calc σ • τ • x - x = σ • (τ • x - x) + (σ • x - x) := by rw [smul_sub]; abel
    _ = _ := by rw [h]

theorem conj_mem_fixingSubgroup [Normal K L] (F : IntermediateField K L) [Normal K F] (γ u : L ≃ₐ[K] L)
    (hu : u ∈ F.fixingSubgroup) : γ * u * γ⁻¹ ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hu ⊢
  intro f hf
  have hf' : γ⁻¹ f ∈ F := by
    have h := ((IntermediateField.normal_iff_forall_map_le' (K := F)).1 inferInstance) γ⁻¹
    exact h ⟨f, hf, rfl⟩
  show γ (u (γ⁻¹ f)) = f
  rw [hu _ hf']
  exact γ.apply_symm_apply f

variable {G' : Type*} [Group G'] (r : G' →* (L ≃ₐ[K] L))

theorem core [IsGalois K L] (q : ℕ) [Fact q.Prime] (k : ℕ)
    (I IP : Subgroup (L ≃ₐ[K] L)) (g : L ≃ₐ[K] L)
    (hconj1 : ∀ τ ∈ IP, g * τ * g⁻¹ ∈ I) (hconj2 : ∀ σ ∈ I, g⁻¹ * σ * g ∈ IP)
    (t : G') (ht : t ∈ IP.comap r)
    (hgen : ∀ (F : IntermediateField K L) [FiniteDimensional K F] [IsGalois K F]
      (χ : ↥(IP.comap r) →* Multiplicative (ZMod q)),
      (∀ i : ↥(IP.comap r), r (i : G') ∈ F.fixingSubgroup → χ i = 1) → χ ⟨t, ht⟩ = 1 → χ = 1)
    (hdense : ∀ σ ∈ IP, ∀ (F : IntermediateField K L) [FiniteDimensional K F],
      ∃ τ : G', r τ ∈ IP ∧ σ⁻¹ * r τ ∈ F.fixingSubgroup)
    (x : J) (hopen : IsOpen (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)))
    (hinv : ∀ σ ∈ I, ∀ τ ∈ I, σ • (τ • x - x) = τ • x - x)
    (htor : ∀ σ ∈ I, q ^ k • (σ • x - x) = 0)
    (hx0 : (g * r t * g⁻¹) • x = x) :
    ∀ σ ∈ I, σ • x = x := by
  classical

  obtain ⟨E, hEfin, hE⟩ := (krullTopology_mem_nhds_one_iff K L _).1
    (hopen.mem_nhds (MulAction.stabilizer (L ≃ₐ[K] L) x).one_mem)
  haveI := hEfin
  let F : IntermediateField K L := IntermediateField.normalClosure K E L
  haveI : IsGalois K F := IsGalois.normalClosure K E L
  have hFE : F.fixingSubgroup ≤ E.fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure E)
  have hFstab : ∀ u ∈ F.fixingSubgroup, u • x = x := fun u hu =>
    MulAction.mem_stabilizer_iff.1 (hE (hFE hu))

  let H : AddSubgroup J := AddSubgroup.closure ((coc x) '' (I : Set (L ≃ₐ[K] L)))
  have memH : ∀ σ, σ ∈ I → coc x σ ∈ H := fun σ hσ => AddSubgroup.subset_closure ⟨σ, hσ, rfl⟩
  by_contra hnot
  push_neg at hnot
  obtain ⟨σ1, hσ1, hne⟩ := hnot
  have hH : ∀ m : H, q ^ k • m = 0 := by
    rintro ⟨m, hm⟩
    apply Subtype.ext
    show q ^ k • m = 0
    refine AddSubgroup.closure_induction (p := fun m _ => q ^ k • m = 0) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨σ, hσ, rfl⟩; exact htor σ hσ
    · exact smul_zero _
    · intro a b _ _ ha hb; rw [smul_add, ha, hb, add_zero]
    · intro a _ ha; rw [smul_neg, ha, neg_zero]
  have hm1 : (⟨coc x σ1, memH σ1 hσ1⟩ : H) ≠ 0 := by
    intro h
    apply hne
    exact (coc_eq_zero_iff x σ1).1 (congrArg Subtype.val h)
  obtain ⟨lam, hlam⟩ := exists_addMonoidHom_zmod_ne_zero q k H hH _ hm1

  let ψ : ∀ σ : L ≃ₐ[K] L, σ ∈ I → ZMod q := fun σ hσ => lam ⟨coc x σ, memH σ hσ⟩
  have ψ_congr : ∀ σ σ' (hσ : σ ∈ I) (hσ' : σ' ∈ I), coc x σ = coc x σ' → ψ σ hσ = ψ σ' hσ' := by
    intro σ σ' hσ hσ' h
    show lam _ = lam _
    congr 1
    exact Subtype.ext h
  have ψ_zero : ∀ σ (hσ : σ ∈ I), σ • x = x → ψ σ hσ = 0 := by
    intro σ hσ h
    show lam _ = 0
    have : (⟨coc x σ, memH σ hσ⟩ : H) = 0 := Subtype.ext ((coc_eq_zero_iff x σ).2 h)
    rw [this, map_zero]
  have ψ_mul : ∀ σ τ (hσ : σ ∈ I) (hτ : τ ∈ I),
      ψ (σ * τ) (I.mul_mem hσ hτ) = ψ τ hτ + ψ σ hσ := by
    intro σ τ hσ hτ
    show lam _ = lam _ + lam _
    rw [← map_add]
    congr 1
    exact Subtype.ext (coc_mul_of_inv x σ τ (hinv σ hσ τ hτ))

  have hmemI : ∀ i : ↥(IP.comap r), g * r (i : G') * g⁻¹ ∈ I := fun i => hconj1 _ i.2

  let χ : ↥(IP.comap r) →* Multiplicative (ZMod q) :=
    { toFun := fun i => Multiplicative.ofAdd (ψ _ (hmemI i))
      map_one' := by
        have h1 : (g * r ((1 : ↥(IP.comap r)) : G') * g⁻¹) • x = x := by
          rw [OneMemClass.coe_one, map_one, mul_one, mul_inv_cancel, one_smul]
        simp only [ψ_zero _ (hmemI 1) h1, ofAdd_zero]
      map_mul' := by
        intro i j
        rw [← ofAdd_add]
        congr 1
        have e : g * r ((i * j : ↥(IP.comap r)) : G') * g⁻¹
            = (g * r (i : G') * g⁻¹) * (g * r (j : G') * g⁻¹) := by
          rw [Subgroup.coe_mul, map_mul]; group
        rw [ψ_congr _ _ (hmemI (i * j)) (I.mul_mem (hmemI i) (hmemI j)) (by rw [e]),
          ψ_mul _ _ (hmemI i) (hmemI j), add_comm] }
  have hχ_apply : ∀ i : ↥(IP.comap r), χ i = Multiplicative.ofAdd (ψ _ (hmemI i)) := fun i => rfl

  have hlevel : ∀ i : ↥(IP.comap r), r (i : G') ∈ F.fixingSubgroup → χ i = 1 := by
    intro i hi
    rw [hχ_apply, ψ_zero _ (hmemI i) (hFstab _ (conj_mem_fixingSubgroup F g _ hi)), ofAdd_zero]

  have hχt : χ ⟨t, ht⟩ = 1 := by
    rw [hχ_apply, ψ_zero _ (hmemI ⟨t, ht⟩) hx0, ofAdd_zero]
  have hχ : χ = 1 := hgen F χ hlevel hχt

  have hvan : ∀ σ (hσ : σ ∈ I), ψ σ hσ = 0 := by
    intro σ hσ
    obtain ⟨τ, hτP, hτF⟩ := hdense (g⁻¹ * σ * g) (hconj2 σ hσ) F
    have hu : σ⁻¹ * (g * r τ * g⁻¹) ∈ F.fixingSubgroup := by
      have := conj_mem_fixingSubgroup F g _ hτF
      have e : g * ((g⁻¹ * σ * g)⁻¹ * r τ) * g⁻¹ = σ⁻¹ * (g * r τ * g⁻¹) := by group
      rwa [e] at this
    have hfix : (σ⁻¹ * (g * r τ * g⁻¹)) • x = x := hFstab _ hu
    have heq : coc x (g * r τ * g⁻¹) = coc x σ := by
      have e : g * r τ * g⁻¹ = σ * (σ⁻¹ * (g * r τ * g⁻¹)) := by group
      rw [e, coc_mul_of_fix x σ _ hfix]
    have h1 : χ ⟨τ, hτP⟩ = 1 := by rw [hχ]; rfl
    rw [hχ_apply, ofAdd_eq_one] at h1
    rwa [ψ_congr _ σ (hmemI ⟨τ, hτP⟩) hσ heq] at h1

  apply hlam
  ext ⟨m, hm⟩
  show lam ⟨m, hm⟩ = 0
  refine AddSubgroup.closure_induction (p := fun m hm => lam ⟨m, hm⟩ = 0) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨σ, hσ, rfl⟩; exact hvan σ hσ
  · exact map_zero lam
  · intro a b ha hb iha ihb
    have := map_add lam ⟨a, ha⟩ ⟨b, hb⟩
    rw [iha, ihb, add_zero] at this
    exact this
  · intro a ha ih
    have := map_neg lam ⟨a, ha⟩
    rw [ih, neg_zero] at this
    exact this

end main

end P2MIIIT

namespace P2MIIIT

open ModularCurve ExtCitation
open scoped Pointwise

theorem smul_eq_of_mem_jZeroToricTorsion (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (n : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (x : JZero p)
    (hx : x ∈ jZeroToricTorsion p A n) : σ • x = x := by
  obtain ⟨-, y, hy, rfl⟩ := mem_jZeroToricTorsion.mp hx
  rw [show σ • (eisensteinNumerator p • y) = eisensteinNumerator p • (σ • y) from
    map_nsmul (DistribSMul.toAddMonoidHom (JZero p) σ) (eisensteinNumerator p) y,
    (mem_inertiaInvariantPoints.mp hy) σ hσ]

theorem not_dvd_pow_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) (k : ℕ) : ¬ p ∣ q ^ k := by
  intro h
  have h1 : p ∣ q := hp.dvd_of_dvd_pow h
  rcases (Nat.dvd_prime hq).1 h1 with h2 | h2
  · exact hp.one_lt.ne' h2
  · exact hqp h2.symm

theorem assembly (p : ℕ) [hp : Fact p.Prime] (q : ℕ) [hq : Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ σ₀ ∈ A.inertiaSubgroupIn ℚ, ∀ (k : ℕ),
      ∀ x ∈ jZeroTorsion p (q ^ k), σ₀ • x = x →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x := by
  classical
  let qq : Nat.Primes := ⟨p, hp.out⟩

  have hP : (padicPlace p).LiesOverPrime p := ExtCitation.natCast_mem_nonunits_primeLocalPlace qq
  obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime hp.out (padicPlace p) A hP hA
  obtain ⟨φ, hφ⟩ := ExtCitation.exists_isFrobeniusAt_apply_primeLocalToGlobal qq
  have hqp' : (qq : ℕ) ≠ q := fun h => hqp h.symm
  obtain ⟨t, ht, hφt, hgen⟩ := ExtCitation.exists_inertia_pCharacter_generator q qq hqp' φ hφ

  have hconj1 : ∀ τ ∈ (padicPlace p).inertiaSubgroupIn ℚ, g * τ * g⁻¹ ∈ A.inertiaSubgroupIn ℚ := by
    intro τ hτ
    have h' : τ ∈ (g⁻¹ • A).inertiaSubgroupIn ℚ := by rwa [← hg, inv_smul_smul]
    have := ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul A g⁻¹ h'
    rwa [inv_inv] at this
  have hconj2 : ∀ σ ∈ A.inertiaSubgroupIn ℚ, g⁻¹ * σ * g ∈ (padicPlace p).inertiaSubgroupIn ℚ := by
    intro σ hσ
    rw [← hg] at hσ
    exact ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul (padicPlace p) g hσ
  have ht' : t ∈ ((padicPlace p).inertiaSubgroupIn ℚ).comap (localGaloisToGlobal p) := ht
  refine ⟨g * localGaloisToGlobal p t * g⁻¹, hconj1 _ ht', ?_⟩
  intro k x hx hx0 σ hσ
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := inferInstance
  refine P2MIIIT.core (K := ℚ) (L := AlgebraicClosure ℚ) (localGaloisToGlobal p) q k
    (A.inertiaSubgroupIn ℚ) ((padicPlace p).inertiaSubgroupIn ℚ) g hconj1 hconj2 t ht'
    ?_ ?_ x (ModularCurve.JZero.isOpen_stabilizer p x) ?_ ?_ hx0 σ hσ
  ·
    intro F hF1 hF2 χ hlev h1
    exact (@hgen F hF1 hF2 χ hlev).1 h1
  ·
    intro τ hτ F _
    exact ValuationSubring.exists_localGaloisToGlobal_mem_inertiaSubgroupIn_inv_mul_mem_fixingSubgroup p τ hτ F
  ·
    intro σ' hσ' τ hτ
    exact (mem_inertiaInvariantPoints.mp
      (ModularCurve.arithmeticGalois_smul_sub_mem_inertiaInvariantPoints p A hA (q ^ k) (pow_ne_zero k hq.out.ne_zero)
        (not_dvd_pow_of_ne hp.out hq.out hqp k) τ hτ x hx)) σ' hσ'
  ·
    intro σ' hσ'
    have hxq : ((q ^ k : ℕ) : ℤ) • x = 0 := (Submodule.mem_torsionBy_iff _ _).1 hx
    have h1 : ((q ^ k : ℕ) : ℤ) • (σ' • x - x) = 0 := by
      rw [zsmul_sub, show ((q ^ k : ℕ) : ℤ) • (σ' • x) = σ' • (((q ^ k : ℕ) : ℤ) • x) from
        (map_zsmul (DistribSMul.toAddMonoidHom (JZero p) σ') _ x).symm, hxq, sub_zero]
      exact map_zero (DistribSMul.toAddMonoidHom (JZero p) σ')
    rwa [natCast_zsmul] at h1

end P2MIIIT

open ModularCurve
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ σ₀ ∈ A.inertiaSubgroupIn ℚ, ∀ (k : ℕ),
      ∀ x ∈ jZeroTorsion p (q ^ k), σ₀ • x = x →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x :=
  P2MIIIT.assembly p q hqp A hA

end S_ModularCurve_exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp
end P2MW
export P2MW.S_ModularCurve_exists_mem_inertiaSubgroupIn_forall_jZeroTorsion_pow_smul_eq_imp (solution)
