-- Prove2me | solution 1 for ModularCurve.JZeroNeronPrimaryTorsionFlag.natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/661d7295-25fe-5c1b-b051-1957a8d4443e

import Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv
import Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_algHom_succ_eq_mul_natCard_algHom_hopfKer
import Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_ringEquiv_apply_algHom_eq_convPow_of_range_eq_hopfKer_of_kind_eq_mult
import Theorems.Thm_AlgebraicGeometry_exists_hom_restriction_muP_fppfCohomologyMap_ker_natCard_eq_pow_of_sectionsEquiv_of_ne_two
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_jZeroTorsionFinite
import Theorems.Thm_HopfAlgebra_exists_constant_and_rootsOfUnity_models_of_rank
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing"
p2m_attr_erase "instance" "ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.LevelP.instAlgebraTorusQRingTorusRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingTorusQRingTorusRing ModularCurve.LevelP.instAwayTorusQRingTorusDenomTorusRing ModularCurve.LevelP.instCommRingTorusRing ModularCurve.LevelP.instAlgebraUnivBasisRingTorusRing ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions EtaleCohomologyLES.instAdditiveSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.instFullSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf EtaleCohomologyLES.constSchemeOpAdditive EtaleCohomologyLES.instFaithfulSheafSchemeFppfTopologyAbEtaleTopologyFppfSheafToEtaleSheaf"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.instAdditiveSheafFppfSmallFppfTopologyAbFppfCohomologyFunctor EtaleCohomologyLES.idIsContinuousEtaleFppf EtaleCohomologyLES.constantSheafEtaleAdditive EtaleCohomologyLES.constantSheafFppfAdditive EtaleCohomologyLES.etaleTopologySubcanonical EtaleCohomologyLES.etaleSheavesIsGrothendieckAbelian"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"
p2m_attr_erase "simp" "HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero KatzModularForm.baseChange_zero ModularCurve.KatzGamma0Form.baseChange_sub ModularCurve.KatzGamma0Form.baseChange_zero ModularCurve.KatzGamma0Form.baseChange_toKatzLevelPForm KatzModularForm.baseChange_sub ModularCurve.KatzLevelPForm.baseChange_sub ModularCurve.KatzGamma0Form.baseChange_smul ModularCurve.KatzGamma0Form.baseChange_add ModularCurve.KatzLevelPForm.baseChange_swap KatzModularForm.baseChange_add ModularCurve.KatzLevelPForm.baseChange_neg ModularCurve.KatzLevelPForm.baseChange_smul ModularCurve.KatzGamma0Form.baseChange_neg ModularCurve.KatzLevelPForm.baseChange_add KatzModularForm.baseChange_smul ModularCurve.KatzLevelPForm.baseChange_zero KatzModularForm.baseChange_neg"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP ModularCurve.LevelP.sClassify_tmul ModularCurve.LevelP.sLift_tmul WeierstrassCurve.Generic.poly_map_classify"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.quotientBySndLine_swap ModularCurve.LevelP.smulX_one ModularCurve.LevelP.quotientByLine_a₃ ModularCurve.LevelP.quotientByLine_a₂ ModularCurve.LevelP.quotientByLine_a₁ ModularCurve.LevelPData.quotientByFstLine_swap ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def TateCurve.tateTorsionPoint_zero_zero ModularCurve.LevelP.TorusQRing.lift_yQ ModularCurve.LevelP.TorusQRing.lift_yP ModularCurve.LevelP.TorusQRing.lift_xQ ModularCurve.LevelP.TorusRing.lift_ofUniv ModularCurve.LevelP.TorusQRing.lift_xP ModularCurve.LevelP.TorusQRing.lift_ofUniv ModularCurve.LevelP.TorusRing.lift_algebraMap ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply"
p2m_attr_erase "simp" "CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff EtaleCohomologyLES.sheafInclusionOfLe_obj_obj FppfCohomologyLES.homPostcompAddEquiv_apply EtaleCohomologyLES.fppfSheafToEtaleSheaf_obj_obj AlgebraicGeometry.Scheme.fppfCohomologyZeroNatIso_inv_app_apply FppfCohomologyLES.homPostcompAddEquiv_symm_apply AlgebraicGeometry.Scheme.fppfCohomologyZeroNatIso_hom_app_apply EtaleCohomologyLES.sheafInclusionOfLe_map_hom EtaleCohomologyLES.fppfSheafToEtaleSheaf_map_hom"

set_option autoImplicit false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
open ModularCurve.JZeroNeronPrimaryTorsionFlag

noncomputable section

namespace LayerQuotBialg

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA S m)

section SiteObjects

variable (R : Type) [CommRing R] [Module.Flat ℤ R] [Algebra.FinitePresentation ℤ R]

def affineMap : Spec (CommRingCat.of R) ⟶ specInt :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ R))

omit [Algebra.FinitePresentation ℤ R] in
theorem affineMap_flat : Flat (affineMap R) := by
  rw [affineMap, HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
    RingHom.flat_algebraMap_iff]
  infer_instance

omit [Module.Flat ℤ R] in
theorem affineMap_lfp : LocallyOfFinitePresentation (affineMap R) := by
  rw [affineMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation),
    CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
  infer_instance

def affineFppf : specInt.Fppf :=
  haveI := affineMap_flat R
  haveI := affineMap_lfp R
  Scheme.Fppf.mk (affineMap R)

def affineΓ : Γ((affineFppf R).left, ⊤) ≃+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv

end SiteObjects

section PhiMonoid

variable (i : Fin (flag.n + 1)) (U : specInt.Fppf)

def Phi (g : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))) :
    WithConv (S.H m →ₐ[ℤ] Γ(U.left, ⊤)) :=
  WithConv.toConv ((WithConv.ofConv g).comp (flag.π i))

theorem sections_compat (s : (flag.F i).1.obj (Opposite.op U)) :
    Additive.toMul (S.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) s))
      = Phi p q A hA S m flag i U (Additive.toMul (flag.F_sectionsEquiv i U s)) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  exact flag.F_sectionsCompat i U s h

theorem Phi_mul (g₁ g₂ : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))) :
    Phi p q A hA S m flag i U (g₁ * g₂)
      = Phi p q A hA S m flag i U g₁ * Phi p q A hA S m flag i U g₂ := by
  obtain ⟨s₁, hs₁⟩ := (flag.F_sectionsEquiv i U).surjective (Additive.ofMul g₁)
  obtain ⟨s₂, hs₂⟩ := (flag.F_sectionsEquiv i U).surjective (Additive.ofMul g₂)
  have h12 : flag.F_sectionsEquiv i U (s₁ + s₂) = Additive.ofMul (g₁ * g₂) := by
    rw [map_add, hs₁, hs₂]; rfl
  have e1 := sections_compat p q A hA S m flag i U s₁
  have e2 := sections_compat p q A hA S m flag i U s₂
  have e12 := sections_compat p q A hA S m flag i U (s₁ + s₂)
  rw [h12] at e12
  rw [hs₁] at e1
  rw [hs₂] at e2
  have hadd : S.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) (s₁ + s₂))
      = S.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) s₁)
        + S.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) s₂) := by
    rw [← map_add, ← map_add]
  have : Additive.toMul (S.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) (s₁ + s₂)))
      = Additive.toMul (S.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) s₁))
        * Additive.toMul (S.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) s₂)) := by
    rw [hadd]; rfl
  rw [e12, e1, e2] at this
  simpa using this

theorem Phi_one :
    Phi p q A hA S m flag i U (1 : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))) = 1 := by
  have h0 : flag.F_sectionsEquiv i U 0 = Additive.ofMul (1 : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))) := by
    rw [map_zero]; rfl
  have e0 := sections_compat p q A hA S m flag i U 0
  rw [h0] at e0
  have hz : S.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) 0) = 0 := by
    rw [map_zero, map_zero]
  have : Additive.toMul (S.sectionsEquiv m U (((flag.ι i).1.app (Opposite.op U)) 0))
      = (1 : WithConv (S.H m →ₐ[ℤ] Γ(U.left, ⊤))) := by
    rw [hz]; rfl
  rw [e0] at this
  simpa using this

end PhiMonoid

end LayerQuotBialg

namespace LayerQuotBialg
namespace Engine

open scoped TensorProduct

variable {R : Type} [CommRing R]

theorem toConv_includeLeft_mul_includeRight {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (X Y : H →ₐ[R] G) :
    (WithConv.toConv ((Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G).comp X)
        * WithConv.toConv ((Algebra.TensorProduct.includeRight : G →ₐ[R] G ⊗[R] G).comp Y)
      : WithConv (H →ₐ[R] G ⊗[R] G))
      = WithConv.toConv ((Algebra.TensorProduct.map X Y).comp (Bialgebra.comulAlgHom R H)) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro h
  rw [AlgHom.convMul_apply]
  have hlift : Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G).comp X)
      ((Algebra.TensorProduct.includeRight : G →ₐ[R] G ⊗[R] G).comp Y)
      (fun _ _ => Commute.all _ _)
      = Algebra.TensorProduct.map X Y := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext; intro a; simp
    · apply AlgHom.ext; intro b; simp
  rw [hlift]
  rfl

theorem comul_square_of_conv {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (π : H →ₐ[R] G)
    (hmul : ∀ g₁ g₂ : WithConv (G →ₐ[R] G ⊗[R] G),
      WithConv.toConv ((WithConv.ofConv (g₁ * g₂)).comp π)
        = WithConv.toConv ((WithConv.ofConv g₁).comp π)
          * WithConv.toConv ((WithConv.ofConv g₂).comp π)) :
    (Bialgebra.comulAlgHom R G).comp π
      = (Algebra.TensorProduct.map π π).comp (Bialgebra.comulAlgHom R H) := by
  have h := hmul (WithConv.toConv Algebra.TensorProduct.includeLeft)
    (WithConv.toConv Algebra.TensorProduct.includeRight)
  have hC2 := toConv_includeLeft_mul_includeRight (R := R) π π

  have hR : WithConv.toConv ((WithConv.ofConv (WithConv.toConv
        (Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] G))).comp π)
        * WithConv.toConv ((WithConv.ofConv (WithConv.toConv
        (Algebra.TensorProduct.includeRight : G →ₐ[R] G ⊗[R] G))).comp π)
      = WithConv.toConv ((Algebra.TensorProduct.map π π).comp
          (Bialgebra.comulAlgHom R H)) := hC2
  rw [hR] at h

  have hC0 := toConv_includeLeft_mul_includeRight (R := R)
    (AlgHom.id R G) (AlgHom.id R G)
  rw [AlgHom.comp_id, AlgHom.comp_id] at hC0
  rw [hC0] at h
  have h' : WithConv.toConv (((Algebra.TensorProduct.map (AlgHom.id R G)
        (AlgHom.id R G)).comp (Bialgebra.comulAlgHom R G)).comp π)
      = WithConv.toConv ((Algebra.TensorProduct.map π π).comp
          (Bialgebra.comulAlgHom R H)) := h
  rw [Algebra.TensorProduct.map_id, AlgHom.id_comp] at h'
  exact congrArg WithConv.ofConv h'

theorem counit_square_of_conv {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (π : H →ₐ[R] G)
    (hone : WithConv.toConv ((WithConv.ofConv
        (1 : WithConv (G →ₐ[R] R))).comp π) = (1 : WithConv (H →ₐ[R] R))) :
    (Bialgebra.counitAlgHom R G).comp π = Bialgebra.counitAlgHom R H := by
  have hid : Algebra.ofId R R = AlgHom.id R R := by
    apply AlgHom.ext; intro x
    show algebraMap R R x = x
    rw [Algebra.algebraMap_self, RingHom.id_apply]
  have h := congrArg WithConv.ofConv hone
  have h2 : ((Algebra.ofId R R).comp (Bialgebra.counitAlgHom R G)).comp π
      = (Algebra.ofId R R).comp (Bialgebra.counitAlgHom R H) := h
  rw [hid, AlgHom.id_comp, AlgHom.id_comp] at h2
  exact h2

theorem mapLin {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (X Y : H →ₐ[R] G) :
    (Algebra.TensorProduct.map X Y).toLinearMap
      = TensorProduct.map X.toLinearMap Y.toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  rfl

theorem comul_lin_square_of_conv {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (π : H →ₐ[R] G)
    (hmul : ∀ g₁ g₂ : WithConv (G →ₐ[R] G ⊗[R] G),
      WithConv.toConv ((WithConv.ofConv (g₁ * g₂)).comp π)
        = WithConv.toConv ((WithConv.ofConv g₁).comp π)
          * WithConv.toConv ((WithConv.ofConv g₂).comp π)) :
    TensorProduct.map π.toLinearMap π.toLinearMap ∘ₗ Coalgebra.comul
      = Coalgebra.comul ∘ₗ π.toLinearMap := by
  have h := congrArg AlgHom.toLinearMap (comul_square_of_conv (R := R) π hmul)
  rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap,
    Bialgebra.toLinearMap_comulAlgHom, mapLin (R := R) π π] at h
  exact h.symm

theorem counit_lin_square_of_conv {H G : Type} [CommRing H] [CommRing G]
    [HopfAlgebra R H] [HopfAlgebra R G] (π : H →ₐ[R] G)
    (hone : WithConv.toConv ((WithConv.ofConv
        (1 : WithConv (G →ₐ[R] R))).comp π) = (1 : WithConv (H →ₐ[R] R))) :
    Coalgebra.counit ∘ₗ π.toLinearMap = (Coalgebra.counit : H →ₗ[R] R) := by
  have h := congrArg AlgHom.toLinearMap (counit_square_of_conv (R := R) π hone)
  rw [AlgHom.comp_toLinearMap, Bialgebra.toLinearMap_counitAlgHom,
    Bialgebra.toLinearMap_counitAlgHom] at h
  exact h

theorem flat_tensor_self {A : Type} [CommRing A] [Bialgebra R A]
    [Module.Flat R A] : Module.Flat R (A ⊗[R] A) :=
  inferInstance

end LayerQuotBialg.Engine

namespace LayerQuotBialg

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
open scoped TensorProduct

scoped instance ft_tensor {R X Y : Type} [CommRing R] [CommRing X] [CommRing Y]
    [Algebra R X] [Algebra R Y] [Algebra.FiniteType R X] [Algebra.FiniteType R Y] :
    Algebra.FiniteType R (X ⊗[R] Y) :=
  Algebra.FiniteType.trans ‹Algebra.FiniteType R X›
    (Algebra.FiniteType.baseChange X (A := Y))

scoped instance fp_tensor {R X Y : Type} [CommRing R] [CommRing X] [CommRing Y]
    [Algebra R X] [Algebra R Y] [IsNoetherianRing R]
    [Algebra.FiniteType R X] [Algebra.FiniteType R Y] :
    Algebra.FinitePresentation R (X ⊗[R] Y) :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA S m)

section ZSide

variable (i : Fin (flag.n + 1))

theorem conv_hyp_π (T : Type) [CommRing T] [instT : Algebra ℤ T]
    (hF : Module.Flat ℤ T) (hFP : Algebra.FinitePresentation ℤ T)
    (g₁ g₂ : WithConv (flag.G i →ₐ[ℤ] T)) :
    WithConv.toConv ((WithConv.ofConv (g₁ * g₂)).comp (flag.π i))
      = WithConv.toConv ((WithConv.ofConv g₁).comp (flag.π i))
        * WithConv.toConv ((WithConv.ofConv g₂).comp (flag.π i)) := by
  classical
  obtain rfl : instT = Ring.toIntAlgebra T := Subsingleton.elim _ _
  haveI := hF
  haveI := hFP
  set U : specInt.Fppf := affineFppf T with hU
  set e := affineΓ T with he
  set eA : Γ(U.left, ⊤) →ₐ[ℤ] T := e.toRingHom.toIntAlgHom with heA
  set eI : T →ₐ[ℤ] Γ(U.left, ⊤) := e.symm.toRingHom.toIntAlgHom with heI
  have heAI : ∀ x, eA (eI x) = x := fun x => e.apply_symm_apply x
  set G₁ : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤)) :=
    WithConv.toConv (eI.comp (WithConv.ofConv g₁)) with hG₁
  set G₂ : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤)) :=
    WithConv.toConv (eI.comp (WithConv.ofConv g₂)) with hG₂
  have hAIg₁ : eA.comp (WithConv.ofConv G₁) = WithConv.ofConv g₁ := by
    apply AlgHom.ext; intro x
    show eA (eI (WithConv.ofConv g₁ x)) = _
    rw [heAI]
  have hAIg₂ : eA.comp (WithConv.ofConv G₂) = WithConv.ofConv g₂ := by
    apply AlgHom.ext; intro x
    show eA (eI (WithConv.ofConv g₂ x)) = _
    rw [heAI]
  have hprod : eA.comp (WithConv.ofConv (G₁ * G₂)) = WithConv.ofConv (g₁ * g₂) := by
    rw [AlgHom.comp_convMul_distrib, hAIg₁, hAIg₂]
  have hPhi := Phi_mul p q A hA S m flag i U G₁ G₂
  have hkey : eA.comp ((WithConv.ofConv (G₁ * G₂)).comp (flag.π i))
      = WithConv.ofConv (WithConv.toConv ((WithConv.ofConv g₁).comp (flag.π i))
          * WithConv.toConv ((WithConv.ofConv g₂).comp (flag.π i))) := by
    have hl : eA.comp ((WithConv.ofConv (G₁ * G₂)).comp (flag.π i))
        = eA.comp (WithConv.ofConv (Phi p q A hA S m flag i U (G₁ * G₂))) := rfl
    rw [hl, hPhi]
    rw [AlgHom.comp_convMul_distrib]
    have hr₁ : eA.comp (WithConv.ofConv (Phi p q A hA S m flag i U G₁))
        = (WithConv.ofConv g₁).comp (flag.π i) := by
      show eA.comp ((WithConv.ofConv G₁).comp (flag.π i)) = _
      rw [← AlgHom.comp_assoc, hAIg₁]
    have hr₂ : eA.comp (WithConv.ofConv (Phi p q A hA S m flag i U G₂))
        = (WithConv.ofConv g₂).comp (flag.π i) := by
      show eA.comp ((WithConv.ofConv G₂).comp (flag.π i)) = _
      rw [← AlgHom.comp_assoc, hAIg₂]
    rw [hr₁, hr₂]
  have hfin : (WithConv.ofConv (g₁ * g₂)).comp (flag.π i)
      = eA.comp ((WithConv.ofConv (G₁ * G₂)).comp (flag.π i)) := by
    rw [← AlgHom.comp_assoc, hprod]
  rw [show WithConv.toConv ((WithConv.ofConv (g₁ * g₂)).comp (flag.π i))
      = WithConv.toConv (eA.comp ((WithConv.ofConv (G₁ * G₂)).comp (flag.π i))) from
    congrArg WithConv.toConv hfin, hkey]

theorem conv_one_π (T : Type) [CommRing T] [instT : Algebra ℤ T]
    (hF : Module.Flat ℤ T) (hFP : Algebra.FinitePresentation ℤ T) :
    WithConv.toConv ((WithConv.ofConv
        (1 : WithConv (flag.G i →ₐ[ℤ] T))).comp (flag.π i))
      = (1 : WithConv (S.H m →ₐ[ℤ] T)) := by
  classical
  obtain rfl : instT = Ring.toIntAlgebra T := Subsingleton.elim _ _
  haveI := hF
  haveI := hFP
  set U : specInt.Fppf := affineFppf T with hU
  set e := affineΓ T with he
  set eA : Γ(U.left, ⊤) →ₐ[ℤ] T := e.toRingHom.toIntAlgHom with heA
  have hone := Phi_one p q A hA S m flag i U
  have hofId : eA.comp (Algebra.ofId ℤ Γ(U.left, ⊤)) = Algebra.ofId ℤ T := by
    apply AlgHom.ext; intro n
    exact eA.commutes n
  have huG : eA.comp (WithConv.ofConv
      (1 : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))))
      = WithConv.ofConv (1 : WithConv (flag.G i →ₐ[ℤ] T)) := by
    show eA.comp ((Algebra.ofId ℤ Γ(U.left, ⊤)).comp
        (Bialgebra.counitAlgHom ℤ (flag.G i)))
      = (Algebra.ofId ℤ T).comp (Bialgebra.counitAlgHom ℤ (flag.G i))
    rw [← AlgHom.comp_assoc, hofId]
  have huH : eA.comp (WithConv.ofConv
      (1 : WithConv (S.H m →ₐ[ℤ] Γ(U.left, ⊤))))
      = WithConv.ofConv (1 : WithConv (S.H m →ₐ[ℤ] T)) := by
    show eA.comp ((Algebra.ofId ℤ Γ(U.left, ⊤)).comp
        (Bialgebra.counitAlgHom ℤ (S.H m)))
      = (Algebra.ofId ℤ T).comp (Bialgebra.counitAlgHom ℤ (S.H m))
    rw [← AlgHom.comp_assoc, hofId]
  have hchain : (WithConv.ofConv (1 : WithConv (flag.G i →ₐ[ℤ] T))).comp (flag.π i)
      = WithConv.ofConv (1 : WithConv (S.H m →ₐ[ℤ] T)) := by
    rw [← huG, ← huH]
    show (eA.comp (WithConv.ofConv
        (1 : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))))).comp (flag.π i) = _
    rw [AlgHom.comp_assoc]
    show eA.comp (WithConv.ofConv (Phi p q A hA S m flag i U
        (1 : WithConv (flag.G i →ₐ[ℤ] Γ(U.left, ⊤))))) = _
    rw [hone]
  exact congrArg WithConv.toConv hchain

theorem comp_π_injective {T : Type} [CommRing T] [Algebra ℤ T] (j : Fin (flag.n + 1))
    {f g : flag.G j →ₐ[ℤ] T} (h : f.comp (flag.π j) = g.comp (flag.π j)) : f = g := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := flag.π_surj j x
  exact AlgHom.congr_fun h y

end ZSide

section QuotSide

variable (i : Fin flag.n)

theorem conv_hyp_quot (T : Type) [CommRing T] [Algebra ℤ T]
    (hF : Module.Flat ℤ T) (hFP : Algebra.FinitePresentation ℤ T)
    (g₁ g₂ : WithConv (flag.G i.castSucc →ₐ[ℤ] T)) :
    WithConv.toConv ((WithConv.ofConv (g₁ * g₂)).comp (flag.quot i))
      = WithConv.toConv ((WithConv.ofConv g₁).comp (flag.quot i))
        * WithConv.toConv ((WithConv.ofConv g₂).comp (flag.quot i)) := by
  have hquotπ : ∀ (w : flag.G i.castSucc →ₐ[ℤ] T),
      (w.comp (flag.quot i)).comp (flag.π i.succ) = w.comp (flag.π i.castSucc) := by
    intro w
    rw [AlgHom.comp_assoc, flag.quot_π]

  have h₁ : (WithConv.ofConv (WithConv.toConv ((WithConv.ofConv g₁).comp
        (flag.quot i)))).comp (flag.π i.succ)
      = (WithConv.ofConv g₁).comp (flag.π i.castSucc) := hquotπ _
  have h₂ : (WithConv.ofConv (WithConv.toConv ((WithConv.ofConv g₂).comp
        (flag.quot i)))).comp (flag.π i.succ)
      = (WithConv.ofConv g₂).comp (flag.π i.castSucc) := hquotπ _

  have hchain : (WithConv.ofConv ((WithConv.toConv ((WithConv.ofConv g₁).comp
        (flag.quot i))) * (WithConv.toConv ((WithConv.ofConv g₂).comp
        (flag.quot i))))).comp (flag.π i.succ)
      = ((WithConv.ofConv (g₁ * g₂)).comp (flag.quot i)).comp (flag.π i.succ) := by
    refine (congrArg WithConv.ofConv (conv_hyp_π p q A hA S m flag i.succ T hF hFP
        (WithConv.toConv ((WithConv.ofConv g₁).comp (flag.quot i)))
        (WithConv.toConv ((WithConv.ofConv g₂).comp (flag.quot i))))).trans ?_
    refine (congrArg WithConv.ofConv (congrArg₂ (· * ·)
        (congrArg WithConv.toConv h₁) (congrArg WithConv.toConv h₂))).trans ?_
    refine ((congrArg WithConv.ofConv (conv_hyp_π p q A hA S m flag i.castSucc T hF hFP
        g₁ g₂)).symm).trans ?_
    exact (hquotπ _).symm
  exact congrArg WithConv.toConv ((comp_π_injective p q A hA S m flag i.succ
    hchain).symm)

theorem conv_one_quot (T : Type) [CommRing T] [Algebra ℤ T]
    (hF : Module.Flat ℤ T) (hFP : Algebra.FinitePresentation ℤ T) :
    WithConv.toConv ((WithConv.ofConv
        (1 : WithConv (flag.G i.castSucc →ₐ[ℤ] T))).comp (flag.quot i))
      = (1 : WithConv (flag.G i.succ →ₐ[ℤ] T)) := by
  have hchain : ((WithConv.ofConv (1 : WithConv (flag.G i.castSucc →ₐ[ℤ] T))).comp
      (flag.quot i)).comp (flag.π i.succ)
      = (WithConv.ofConv (1 : WithConv (flag.G i.succ →ₐ[ℤ] T))).comp
          (flag.π i.succ) := by
    refine ((AlgHom.comp_assoc _ _ _).trans ?_)
    refine (congrArg (fun w => (WithConv.ofConv
        (1 : WithConv (flag.G i.castSucc →ₐ[ℤ] T))).comp w) (flag.quot_π i)).trans ?_
    refine (congrArg WithConv.ofConv (conv_one_π p q A hA S m flag i.castSucc T hF hFP)).trans ?_
    exact (congrArg WithConv.ofConv (conv_one_π p q A hA S m flag i.succ T hF hFP)).symm
  exact congrArg WithConv.toConv (comp_π_injective p q A hA S m flag i.succ hchain)

end QuotSide

section Packaging

variable (i : Fin (flag.n + 1)) (j : Fin flag.n)

theorem flat_of_flat' {M : Type} [AddCommMonoid M] {m₁ m₂ : Module ℤ M}
    (h : @Module.Flat ℤ M _ _ m₁) : @Module.Flat ℤ M _ _ m₂ := by
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact h

theorem fp_of_fp' {M : Type} [CommRing M] {a₁ a₂ : Algebra ℤ M}
    (h : @Algebra.FinitePresentation ℤ M _ _ a₁) :
    @Algebra.FinitePresentation ℤ M _ _ a₂ := by
  obtain rfl : a₁ = a₂ := Subsingleton.elim _ _
  exact h

noncomputable def quotBialg : flag.G j.succ →ₐc[ℤ] flag.G j.castSucc :=
  { toLinearMap := (flag.quot j).toLinearMap
    counit_comp := Engine.counit_lin_square_of_conv (R := ℤ) (flag.quot j)
      (conv_one_quot p q A hA S m flag j ℤ (flat_of_flat' inferInstance)
        (fp_of_fp' inferInstance))
    map_comp_comul := Engine.comul_lin_square_of_conv (R := ℤ) (flag.quot j)
      (fun g₁ g₂ => by
        haveI : @Module.Flat ℤ (flag.G j.castSucc) _ _ Algebra.toModule :=
          flat_of_flat' (flag.instFlat_G j.castSucc)
        apply conv_hyp_quot p q A hA S m flag j
        · exact flat_of_flat'
            (Engine.flat_tensor_self (R := ℤ) (A := flag.G j.castSucc))
        · exact fp_of_fp' inferInstance)
    map_one' := map_one (flag.quot j)
    map_mul' := map_mul (flag.quot j) }

theorem quotBialg_toAlgHom :
    (quotBialg p q A hA S m flag j : flag.G j.succ →ₐ[ℤ] flag.G j.castSucc)
      = flag.quot j := by
  apply AlgHom.ext
  intro x
  rfl

end Packaging

end LayerQuotBialg
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

namespace MultLayerFixedPoints

theorem exists_ringEquiv_pow (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    ∃ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (n₀ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ n₀) ∧ 2 ≤ n₀ ∧ n₀ < q := by
  classical
  have hqp : q.Prime := Fact.out
  have hq1 : 1 < q := hqp.one_lt
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  haveI : NeZero (q : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hqp.ne_zero⟩

  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ q := by
    have hdeg : (Polynomial.cyclotomic q (AlgebraicClosure ℚ)).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.mpr hqp.pos).ne'
    obtain ⟨ζ, hz⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hz⟩
  have hζ1 : ζ ≠ 1 := hζ.ne_one hq1

  have hnotfix : ¬ ∀ f : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, f ζ = ζ := by
    intro hfix
    obtain ⟨r, hr⟩ :=
      (@InfiniteGalois.mem_range_algebraMap_iff_fixed ℚ (AlgebraicClosure ℚ) _ _
        (AlgebraicClosure.instAlgebra ℚ) _ ζ).mpr hfix
    have hr' : (r : AlgebraicClosure ℚ) = ζ := (eq_ratCast _ r).symm.trans hr
    have hrq : ((r ^ q : ℚ) : AlgebraicClosure ℚ) = ((1 : ℚ) : AlgebraicClosure ℚ) := by
      rw [Rat.cast_pow, hr', hζ.pow_eq_one, Rat.cast_one]
    have hrq' : r ^ q = 1 := Rat.cast_injective hrq
    have hodd : Odd q := hqp.odd_of_ne_two hq2
    have hr1 : r = 1 := hodd.strictMono_pow.injective (by simpa using hrq')
    exact hζ1 (by rw [← hr', hr1, Rat.cast_one])
  obtain ⟨f, hf⟩ := not_forall.mp hnotfix

  have hfq : (f ζ) ^ q = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨n₀, hn₀, hfζ⟩ := hζ.eq_pow_of_pow_eq_one hfq
  refine ⟨(f : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ), n₀, ?_, ?_, hn₀⟩
  · intro ξ hξ
    obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    show f (ζ ^ k) = (ζ ^ k) ^ n₀
    rw [map_pow, ← hfζ, ← pow_mul, ← pow_mul, mul_comm]
  ·
    by_contra hlt
    have hcases : n₀ = 0 ∨ n₀ = 1 := by omega
    rcases hcases with h0 | h1
    · rw [h0, pow_zero] at hfζ
      exact hζ1 (f.injective (hfζ.symm.trans (map_one f).symm))
    · rw [h1, pow_one] at hfζ
      exact hf hfζ.symm

section Units

variable {R K T : Type} [CommRing R] [CommRing K] [HopfAlgebra R K] [CommRing T] [Algebra R T]

def antipodeAlgHom : K →ₐ[R] K :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

theorem antipodeAlgHom_apply (k : K) : antipodeAlgHom (R := R) k = HopfAlgebra.antipode R k :=
  rfl

theorem lift_comp_comp (ψ : K →ₐ[R] T) (X Y : K →ₐ[R] K) :
    Algebra.TensorProduct.lift (ψ.comp X) (ψ.comp Y) (fun _ _ => Commute.all _ _)
      = ψ.comp (Algebra.TensorProduct.lift X Y (fun _ _ => Commute.all _ _)) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext; intro a; simp
  · apply AlgHom.ext; intro b; simp

theorem toConv_mul_toConv_comp_antipode (ψ : K →ₐ[R] T) :
    WithConv.toConv ψ * WithConv.toConv (ψ.comp (antipodeAlgHom (R := R))) = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  have hlift := lift_comp_comp ψ (AlgHom.id R K) (antipodeAlgHom (R := R))
  rw [AlgHom.comp_id] at hlift
  have hlin : (Algebra.TensorProduct.lift (AlgHom.id R K) (antipodeAlgHom (R := R))
        (fun _ _ => Commute.all _ _)).toLinearMap
      = LinearMap.mul' R K ∘ₗ (HopfAlgebra.antipode R).lTensor K := by
    apply TensorProduct.ext'
    intro a b
    rfl
  have hx := LinearMap.congr_fun hlin (Coalgebra.comul c)
  rw [AlgHom.toLinearMap_apply, LinearMap.comp_apply,
    HopfAlgebra.mul_antipode_lTensor_comul_apply] at hx
  show Algebra.TensorProduct.lift (WithConv.ofConv (WithConv.toConv ψ))
      (WithConv.ofConv (WithConv.toConv (ψ.comp (antipodeAlgHom (R := R)))))
      (fun _ _ => Commute.all _ _) (Coalgebra.comul c) = _
  rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv, hlift, AlgHom.comp_apply, hx,
    AlgHom.commutes]

theorem toConv_comp_antipode_mul_toConv (ψ : K →ₐ[R] T) :
    WithConv.toConv (ψ.comp (antipodeAlgHom (R := R))) * WithConv.toConv ψ = 1 := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro c
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
  have hlift := lift_comp_comp ψ (antipodeAlgHom (R := R)) (AlgHom.id R K)
  rw [AlgHom.comp_id] at hlift
  have hlin : (Algebra.TensorProduct.lift (antipodeAlgHom (R := R)) (AlgHom.id R K)
        (fun _ _ => Commute.all _ _)).toLinearMap
      = LinearMap.mul' R K ∘ₗ (HopfAlgebra.antipode R).rTensor K := by
    apply TensorProduct.ext'
    intro a b
    rfl
  have hx := LinearMap.congr_fun hlin (Coalgebra.comul c)
  rw [AlgHom.toLinearMap_apply, LinearMap.comp_apply,
    HopfAlgebra.mul_antipode_rTensor_comul_apply] at hx
  show Algebra.TensorProduct.lift (WithConv.ofConv (WithConv.toConv (ψ.comp (antipodeAlgHom (R := R)))))
      (WithConv.ofConv (WithConv.toConv ψ))
      (fun _ _ => Commute.all _ _) (Coalgebra.comul c) = _
  rw [WithConv.ofConv_toConv, WithConv.ofConv_toConv, hlift, AlgHom.comp_apply, hx,
    AlgHom.commutes]

theorem isUnit_toConv (ψ : K →ₐ[R] T) : IsUnit (WithConv.toConv ψ) :=
  ⟨⟨WithConv.toConv ψ, WithConv.toConv (ψ.comp (antipodeAlgHom (R := R))),
    toConv_mul_toConv_comp_antipode ψ, toConv_comp_antipode_mul_toConv ψ⟩, rfl⟩

end Units
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

theorem eq_one_of_pow_eq_self {M : Type} [Monoid M] (q : ℕ) (hq : q.Prime)
    (hcard : Nat.card M = q) (hunit : ∀ x : M, IsUnit x) (g : M) (n : ℕ)
    (h2 : 2 ≤ n) (hn : n < q) (hg : g ^ n = g) : g = 1 := by
  have hcardU : Nat.card Mˣ = q := by
    rw [← hcard]
    exact Nat.card_congr (Equiv.ofBijective (Units.val : Mˣ → M)
      ⟨Units.val_injective, fun x => ⟨(hunit x).unit, (hunit x).unit_spec⟩⟩)
  set u : Mˣ := (hunit g).unit with hu
  have hug : (u : M) = g := (hunit g).unit_spec
  have hun : u ^ n = u := Units.val_injective (by rw [Units.val_pow_eq_pow_val, hug]; exact hg)
  have hun1 : u ^ (n - 1) = 1 := by
    have h : u ^ (n - 1) * u = 1 * u := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n), one_mul, hun]
    exact mul_right_cancel h
  have hdvd1 : orderOf u ∣ n - 1 := orderOf_dvd_of_pow_eq_one hun1
  have hdvdq : orderOf u ∣ q := hcardU ▸ orderOf_dvd_natCard u
  rcases (Nat.dvd_prime hq).mp hdvdq with h1 | hq'
  · have hu1 : u = 1 := orderOf_eq_one_iff.mp h1
    rw [← hug, hu1, Units.val_one]
  · exfalso
    rw [hq'] at hdvd1
    have := Nat.le_of_dvd (by omega) hdvd1
    omega

theorem natCard_algHom_int_eq_one {K : Type} [CommRing K] [HopfAlgebra ℤ K]
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgalM : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k) :
    Nat.card (K →ₐ[ℤ] ℤ) = 1 := by
  have hqp : q.Prime := Fact.out
  obtain ⟨σ, n₀, hcyc, h2, hn⟩ := exists_ringEquiv_pow q hq2

  have hcardM : Nat.card (WithConv (K →ₐ[ℤ] AlgebraicClosure ℚ)) = q :=
    (Nat.card_congr (WithConv.equiv (K →ₐ[ℤ] AlgebraicClosure ℚ))).trans hgenq
  have hunit : ∀ x : WithConv (K →ₐ[ℤ] AlgebraicClosure ℚ), IsUnit x := fun x => by
    rw [← WithConv.toConv_ofConv x]
    exact isUnit_toConv (R := ℤ) (WithConv.ofConv x)

  have hpt : ∀ φ : K →ₐ[ℤ] ℤ,
      (Algebra.ofId ℤ (AlgebraicClosure ℚ)).comp φ
        = (Algebra.ofId ℤ (AlgebraicClosure ℚ)).comp (Bialgebra.counitAlgHom ℤ K) := by
    intro φ
    set ψ : K →ₐ[ℤ] AlgebraicClosure ℚ := (Algebra.ofId ℤ (AlgebraicClosure ℚ)).comp φ with hψ
    have hfix : ∀ k : K, σ (ψ k) = ψ k := by
      intro k
      show σ (algebraMap ℤ (AlgebraicClosure ℚ) (φ k)) = algebraMap ℤ (AlgebraicClosure ℚ) (φ k)
      rw [eq_intCast, map_intCast]
    have hpow : WithConv.toConv ψ ^ n₀ = WithConv.toConv ψ := by
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro k
      rw [WithConv.ofConv_toConv, ← hfix k]
      exact (hgalM σ n₀ hcyc ψ k).symm
    have h1 : WithConv.toConv ψ = 1 :=
      eq_one_of_pow_eq_self q hqp hcardM hunit (WithConv.toConv ψ) n₀ h2 hn hpow
    have h1' := congrArg WithConv.ofConv h1
    rw [WithConv.ofConv_toConv] at h1'
    rw [h1']
    exact congrArg WithConv.ofConv (AlgHom.convOne_def (R := ℤ) (C := K)
      (A := AlgebraicClosure ℚ))

  have hinj : ∀ φ φ' : K →ₐ[ℤ] ℤ,
      (Algebra.ofId ℤ (AlgebraicClosure ℚ)).comp φ
        = (Algebra.ofId ℤ (AlgebraicClosure ℚ)).comp φ' → φ = φ' := by
    intro φ φ' h
    apply AlgHom.ext
    intro k
    have hk := AlgHom.congr_fun h k
    have hk' : ((φ k : ℤ) : AlgebraicClosure ℚ) = ((φ' k : ℤ) : AlgebraicClosure ℚ) := by
      simpa [Algebra.ofId_apply] using hk
    exact_mod_cast hk'
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨Bialgebra.counitAlgHom ℤ K⟩⟩
  exact hinj a b ((hpt a).trans (hpt b).symm)

end MultLayerFixedPoints
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

namespace LayerModelEngine

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  (S : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
  (flag : JZeroNeronPrimaryTorsionFlag p q A hA S m)

section QuotBialg
variable (i : Fin flag.n)

private def _root_.LayerModelEngine.quotBialg : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc :=
  LayerQuotBialg.quotBialg p q A hA S m flag i
p2m_export "LayerModelEngine" "quotBialg"
theorem quotBialg_eq :
    ((quotBialg p q A hA S m flag i : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
      : flag.G i.succ →ₐ[ℤ] flag.G i.castSucc) = flag.quot i :=
  LayerQuotBialg.quotBialg_toAlgHom p q A hA S m flag i
end QuotBialg
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

section G1
open scoped TensorProduct
variable {i : Fin flag.n}

theorem finite_baseChange_G (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (j' : Fin (flag.n + 1)) :
    Module.Finite (GaloisRep.ratLocalizedAt ℓ)
      (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) (flag.G j')) := by
  haveI := S.ff_finite m ℓ hℓ hℓp
  refine Module.Finite.of_surjective
    ((flag.π j').toAddMonoidHom.toIntLinearMap.baseChange (GaloisRep.ratLocalizedAt ℓ)) ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective _ (flag.π_surj j')

theorem hff_of_injective (K : Type) [CommRing K] [Algebra ℤ K]
    (j : K →ₐ[ℤ] flag.G i.succ) (hinj : Function.Injective j) :
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    Module.Finite (GaloisRep.ratLocalizedAt ℓ)
      (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K) := by
  intro ℓ hℓ hℓp
  haveI hprime : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hℓ)
  haveI := GaloisRep.isLocalization_ratLocalizedAt hℓ
  haveI : Module.Flat ℤ (GaloisRep.ratLocalizedAt ℓ) :=
    IsLocalization.flat (GaloisRep.ratLocalizedAt ℓ) (Ideal.span {(ℓ : ℤ)}).primeCompl
  haveI : IsNoetherianRing (GaloisRep.ratLocalizedAt ℓ) :=
    IsLocalization.isNoetherianRing (Ideal.span {(ℓ : ℤ)}).primeCompl _ inferInstance
  haveI := finite_baseChange_G p q A hA S m flag ℓ hℓ hℓp i.succ
  refine Module.Finite.of_injective
    (j.toAddMonoidHom.toIntLinearMap.baseChange (GaloisRep.ratLocalizedAt ℓ)) ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
end G1
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

section Fin

theorem finite_eisensteinPrimaryTorsionBar : Finite ↥(eisensteinPrimaryTorsionBar p q m) := by
  have hfin : Finite ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (modularFunctionFieldBar p) (q ^ m)) :=
    ModularCurve.jZeroTorsionFinite p (q ^ m) (pow_pos (Fact.out : q.Prime).pos m)
  have hle : eisensteinPrimaryTorsionBar p q m
      ≤ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (q ^ m) := by
    intro x hx
    have h0 : ((q : ℤ) ^ m) • x = 0 := hx.1
    rw [AlgebraicCurve.Pic0.mem_torsion]
    exact_mod_cast h0
  exact Finite.of_injective _ (AddSubgroup.inclusion_injective hle)

theorem finite_genericStep (j' : Fin (flag.n + 1)) : Finite ↥(flag.genericStep j') :=
  haveI := finite_eisensteinPrimaryTorsionBar p q m
  Finite.of_injective _ (AddSubgroup.inclusion_injective (flag.genericStep_le_tors j'))
end Fin
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

section G3
variable (j' : Fin (flag.n + 1))

def aPt (φ : flag.G j' →ₐ[ℤ] ↥A) : JZero p :=
  (S.pFibrePoints m (WithConv.toConv (φ.comp (flag.π j'))) : JZero p)

theorem aPt_mem_toric (φ : flag.G j' →ₐ[ℤ] ↥A) :
    aPt p q A hA S m flag j' φ ∈ jZeroToricTorsion p A (q ^ m) :=
  (S.pFibrePoints m (WithConv.toConv (φ.comp (flag.π j')))).2.1

theorem aPt_mem_genericStep (φ : flag.G j' →ₐ[ℤ] ↥A) :
    aPt p q A hA S m flag j' φ ∈ flag.genericStep j' := by
  rw [flag.genericStep_pin]
  refine ⟨(A.subtype.toIntAlgHom).comp φ, ?_⟩
  exact (S.pFibreGenericCompat m (WithConv.toConv (φ.comp (flag.π j')))
    (WithConv.toConv (((A.subtype.toIntAlgHom).comp φ).comp (flag.π j'))) (fun _ => rfl)).symm

def aPtInf (φ : flag.G j' →ₐ[ℤ] ↥A) :
    ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep j') :=
  ⟨aPt p q A hA S m flag j' φ, aPt_mem_toric p q A hA S m flag j' φ,
    aPt_mem_genericStep p q A hA S m flag j' φ⟩

theorem aPtInf_injective : Function.Injective (aPtInf p q A hA S m flag j') := by
  intro φ φ' h
  have h1 : aPt p q A hA S m flag j' φ = aPt p q A hA S m flag j' φ' :=
    congrArg (fun z : ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep j') => (z : JZero p)) h
  have h2 : S.pFibrePoints m (WithConv.toConv (φ.comp (flag.π j')))
      = S.pFibrePoints m (WithConv.toConv (φ'.comp (flag.π j'))) := Subtype.ext h1
  have h3 := WithConv.toConv_injective ((S.pFibrePoints m).injective h2)
  apply AlgHom.ext
  intro y
  obtain ⟨x, rfl⟩ := flag.π_surj j' y
  exact DFunLike.congr_fun h3 x

theorem aPtInf_surjective : Function.Surjective (aPtInf p q A hA S m flag j') := by
  rintro ⟨x, hxT, hxG⟩
  obtain ⟨g, hg⟩ := (flag.genericStep_pin j' x).mp hxG
  have hxE : x ∈ toricEisensteinPrimaryPart p q A hA m := ⟨hxT, flag.genericStep_le_tors j' hxG⟩
  have hc := S.pFibreGenericCompat m ((S.pFibrePoints m).symm ⟨x, hxE⟩)
    (WithConv.toConv ((A.subtype.toIntAlgHom).comp
      (WithConv.ofConv ((S.pFibrePoints m).symm ⟨x, hxE⟩)))) (fun _ => rfl)
  rw [Equiv.apply_symm_apply] at hc
  have hgen : S.genericPoints m (WithConv.toConv (((A.subtype.toIntAlgHom).comp
        (WithConv.ofConv ((S.pFibrePoints m).symm ⟨x, hxE⟩)))))
      = S.genericPoints m (WithConv.toConv (g.comp (flag.π j'))) :=
    Subtype.ext (hc.symm.trans hg.symm)
  have key : ((A.subtype.toIntAlgHom).comp (WithConv.ofConv ((S.pFibrePoints m).symm ⟨x, hxE⟩)))
      = g.comp (flag.π j') :=
    WithConv.toConv_injective ((S.genericPoints m).injective hgen)
  have hmem : ∀ y, g y ∈ A := by
    intro y
    obtain ⟨h, rfl⟩ := flag.π_surj j' y
    have e1 : g (flag.π j' h) = ((WithConv.ofConv ((S.pFibrePoints m).symm ⟨x, hxE⟩)) h : _) :=
      (DFunLike.congr_fun key h).symm
    rw [e1]
    exact (WithConv.ofConv ((S.pFibrePoints m).symm ⟨x, hxE⟩) h).2
  let φ : flag.G j' →ₐ[ℤ] ↥A :=
    { toFun := fun y => ⟨g y, hmem y⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun a b => Subtype.ext (map_mul g a b)
      map_zero' := Subtype.ext (map_zero g)
      map_add' := fun a b => Subtype.ext (map_add g a b)
      commutes' := fun n => Subtype.ext (by
        show g (algebraMap ℤ (flag.G j') n) = ((algebraMap ℤ ↥A n : ↥A) : AlgebraicClosure ℚ)
        rw [g.commutes]
        simp) }
  refine ⟨φ, Subtype.ext ?_⟩
  show (S.pFibrePoints m (WithConv.toConv (φ.comp (flag.π j'))) : JZero p) = x
  have hφ : φ.comp (flag.π j') = WithConv.ofConv ((S.pFibrePoints m).symm ⟨x, hxE⟩) := by
    apply AlgHom.ext
    intro h
    apply Subtype.ext
    show g ((flag.π j') h) = _
    exact (DFunLike.congr_fun key h).symm
  rw [hφ, WithConv.toConv_ofConv, Equiv.apply_symm_apply]

theorem natCard_algHom_valuationSubring :
    Nat.card (flag.G j' →ₐ[ℤ] ↥A)
      = Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep j') :=
  Nat.card_congr (Equiv.ofBijective _
    ⟨aPtInf_injective p q A hA S m flag j', aPtInf_surjective p q A hA S m flag j'⟩)

theorem finite_algHom_valuationSubring : Finite (flag.G j' →ₐ[ℤ] ↥A) :=
  haveI := finite_genericStep p q A hA S m flag j'
  haveI : Finite ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep j') :=
    Finite.of_injective _ (AddSubgroup.inclusion_injective inf_le_right)
  Finite.of_injective _ (aPtInf_injective p q A hA S m flag j')

theorem natCard_algHom_valuationSubring_ne_zero :
    Nat.card (flag.G j' →ₐ[ℤ] ↥A) ≠ 0 :=
  haveI := finite_algHom_valuationSubring p q A hA S m flag j'
  haveI : Nonempty (flag.G j' →ₐ[ℤ] ↥A) :=
    ⟨(Algebra.ofId ℤ ↥A).comp (Bialgebra.counitAlgHom ℤ (flag.G j'))⟩
  Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
end G3
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

section Bridge
variable {i : Fin flag.n} (qc : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
  (K : Type) [CommRing K] [Algebra ℤ K]
  (j : K →ₐ[ℤ] flag.G i.succ) (hinj : Function.Injective j)
  (hrange : j.range = HopfAlgebra.hopfKer qc)
include j hinj hrange in
theorem natCard_algHom_eq_of_range_eq (T : Type) [CommRing T] [Algebra ℤ T] :
    Nat.card (K →ₐ[ℤ] T) = Nat.card (↥(HopfAlgebra.hopfKer qc) →ₐ[ℤ] T) :=
  Nat.card_congr (((AlgEquiv.ofInjective j hinj).trans
    (Subalgebra.equivOfEq _ _ hrange)).arrowCongr AlgEquiv.refl)
end Bridge
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

section Genq
variable {i : Fin flag.n}

omit [Fact p.Prime] in
theorem exists_prime_ne : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p := by
  by_cases h : p = 2
  · exact ⟨3, Nat.prime_three, by omega⟩
  · exact ⟨2, Nat.prime_two, fun h2 => h h2.symm⟩

theorem natCard_points_Lff (i : Fin flag.n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
    Nat.card (flag.Lff i ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ) = q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨⟨Kc, _, _, -, -, -, hcardc, ⟨ec⟩⟩, ⟨Km, _, _, -, -, -, hcardm, ⟨em⟩⟩⟩ :=
    HopfAlgebra.exists_constant_and_rootsOfUnity_models_of_rank
      (GaloisRep.ratLocalizedAt ℓ) q (AlgebraicClosure ℚ)
  cases hk : flag.kind i with
  | const =>
      obtain ⟨e⟩ := flag.layerIsoConst i hk ℓ hℓ hℓp
      exact (Nat.card_congr (AlgEquiv.arrowCongr (e.trans ec.symm) AlgEquiv.refl)).trans hcardc
  | mult =>
      obtain ⟨e⟩ := flag.layerIsoMult i hk ℓ hℓ hℓp
      exact (Nat.card_congr (AlgEquiv.arrowCongr (e.trans em.symm) AlgEquiv.refl)).trans hcardm

theorem natCard_layerQuot (i : Fin flag.n) :
    Nat.card (↥(flag.genericStep i.succ) ⧸
      (flag.genericStep i.castSucc).addSubgroupOf (flag.genericStep i.succ)) = q := by
  obtain ⟨ℓ, hℓ, hℓp⟩ := exists_prime_ne p
  rw [← Nat.card_congr (flag.Lff_points i ℓ hℓ hℓp),
    Nat.card_congr (WithConv.equiv
      (flag.Lff i ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ))]
  exact natCard_points_Lff p q A hA S m flag i ℓ hℓ hℓp

theorem natCard_genericStep_succ_eq :
    Nat.card ↥(flag.genericStep i.succ) = q * Nat.card ↥(flag.genericStep i.castSucc) := by
  have hmono : flag.genericStep i.castSucc ≤ flag.genericStep i.succ :=
    flag.genericStep_mono (Fin.castSucc_lt_succ (i := i)).le
  rw [((flag.genericStep i.castSucc).addSubgroupOf
      (flag.genericStep i.succ)).card_eq_card_quotient_mul_card_addSubgroup,
    natCard_layerQuot p q A hA S m flag i,
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hmono).toEquiv]

theorem natCard_algHom_algebraicClosure_G :
    ∀ j' : Fin (flag.n + 1),
      Nat.card (flag.G j' →ₐ[ℤ] AlgebraicClosure ℚ) = Nat.card ↥(flag.genericStep j') := by
  intro j'
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => ⟨((S.genericPoints m (WithConv.toConv (g.comp (flag.π j')))) : JZero p),
      (flag.genericStep_pin j' _).mpr ⟨g, rfl⟩⟩) ⟨?_, ?_⟩)
  · intro g₁ g₂ h
    have h1 : ((S.genericPoints m (WithConv.toConv (g₁.comp (flag.π j')))) : JZero p)
        = ((S.genericPoints m (WithConv.toConv (g₂.comp (flag.π j')))) : JZero p) := by
      simpa using congrArg (fun z : ↥(flag.genericStep j') => (z : JZero p)) h
    have h2 := WithConv.toConv_injective ((S.genericPoints m).injective (Subtype.ext h1))
    ext z
    obtain ⟨y, rfl⟩ := flag.π_surj j' z
    exact DFunLike.congr_fun h2 y
  · rintro ⟨x, hx⟩
    obtain ⟨g, hg⟩ := (flag.genericStep_pin j' x).mp hx
    exact ⟨g, Subtype.ext hg⟩

theorem natCard_genericStep_ne_zero (j' : Fin (flag.n + 1)) :
    Nat.card ↥(flag.genericStep j') ≠ 0 := by
  haveI := finite_genericStep p q A hA S m flag j'
  exact Nat.card_ne_zero.mpr ⟨⟨⟨0, (flag.genericStep j').zero_mem⟩⟩, ‹_›⟩
end Genq
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

section H0

def gammaSpecIntAlgEquiv : Γ((fppfTerminal specInt).left, ⊤) ≃ₐ[ℤ] ℤ :=
  AlgEquiv.ofRingEquiv (f := (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv)
    (fun n => by simp)

variable (L : Sheaf (smallFppfTopology specInt) Ab.{1}) (K : Type) [CommRing K] [HopfAlgebra ℤ K]
  (e : ∀ U : specInt.Fppf,
    L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤))))

def fppfCohomologyZeroEquivAlgHomInt : fppfCohomology specInt L 0 ≃ (K →ₐ[ℤ] ℤ) :=
  (fppfCohomologySpecIntZeroAddEquiv L).toEquiv.trans
    ((e (fppfTerminal specInt)).toEquiv.trans
      (Additive.toMul.trans
        ((WithConv.equiv (K →ₐ[ℤ] Γ((fppfTerminal specInt).left, ⊤))).trans
          (AlgEquiv.arrowCongr AlgEquiv.refl gammaSpecIntAlgEquiv))))

include e in
theorem natCard_fppfCohomology_zero_eq_algHom_int :
    Nat.card (fppfCohomology specInt L 0) = Nat.card (K →ₐ[ℤ] ℤ) :=
  Nat.card_congr (fppfCohomologyZeroEquivAlgHomInt L K e)
end H0
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

end LayerModelEngine
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two.LayerQuotBialg"

open LayerModelEngine

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (S : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA S m) (i : Fin flag.n)
    (hk : flag.kind i = JZeroFlagLayerKind.mult)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact)
    (dt : ℕ)
    (ht : Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep i.succ)
        = q ^ dt * Nat.card ↥(jZeroToricTorsion p A (q ^ m) ⊓ flag.genericStep i.castSucc)) :
    Nat.card (fppfCohomology specInt L 0) = 1 ∧
    ∃ dk : ℕ, dk + dt ≤ 1 ∧
      ∃ (C : Sheaf (smallFppfTopology specInt) Ab.{1})
        (_ : C.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙
            (FppfKummerSES.muPAbelianSheafLifted.{0} q).obj)
        (f : L ⟶ C), Nat.card ↥(fppfCohomologyMap specInt f 1).ker = q ^ dk := by

  let qc := quotBialg p q A hA S m flag i
  have hqc := quotBialg_eq p q A hA S m flag i

  obtain ⟨K, crK, haK, ftK, flK, j, e, hinj, hrange, hHG, hflat, hnat⟩ :=
    ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv
      p q A hA S m flag i qc hqc L pr hzero hses
  letI := crK; letI := haK; letI := ftK; letI := flK

  have hff := hff_of_injective p q A hA S m flag K
    (j : K →ₐ[ℤ] flag.G i.succ) hinj

  have hgalM := ModularCurve.JZeroNeronPrimaryTorsionFlag.ringEquiv_apply_algHom_eq_convPow_of_range_eq_hopfKer_of_kind_eq_mult
    p q A hA S m flag i hk qc hqc K crK haK j hinj hrange hflat

  obtain ⟨hQ, hAA, hFq, _⟩ :=
    ModularCurve.JZeroNeronPrimaryTorsionFlag.natCard_algHom_succ_eq_mul_natCard_algHom_hopfKer
      p q A hA S m flag i qc hHG hflat

  have hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q := by
    have hbr := natCard_algHom_eq_of_range_eq p q A hA S m flag qc K
      (j : K →ₐ[ℤ] flag.G i.succ) hinj hrange (AlgebraicClosure ℚ)
    have hG := natCard_algHom_algebraicClosure_G p q A hA S m flag
    have hstep := natCard_genericStep_succ_eq p q A hA S m flag (i := i)
    have hne := natCard_genericStep_ne_zero p q A hA S m flag i.castSucc
    have hker : Nat.card (↥(HopfAlgebra.hopfKer qc) →ₐ[ℤ] AlgebraicClosure ℚ) = q := by
      have h1 : Nat.card ↥(flag.genericStep i.castSucc)
          * Nat.card (↥(HopfAlgebra.hopfKer qc) →ₐ[ℤ] AlgebraicClosure ℚ)
          = Nat.card ↥(flag.genericStep i.castSucc) * q := by
        rw [← hG i.castSucc, ← hQ, hG i.succ, hstep, ← hG i.castSucc]
        ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h1
    exact hbr.trans hker

  have hbrA := natCard_algHom_eq_of_range_eq p q A hA S m flag qc K
    (j : K →ₐ[ℤ] flag.G i.succ) hinj hrange ↥A
  have hg3s := natCard_algHom_valuationSubring p q A hA S m flag i.succ
  have hg3c := natCard_algHom_valuationSubring p q A hA S m flag i.castSucc
  have hne0 := natCard_algHom_valuationSubring_ne_zero p q A hA S m flag i.castSucc
  have hKA : Nat.card (K →ₐ[ℤ] ↥A) = q ^ dt := by
    have h1 : Nat.card (flag.G i.castSucc →ₐ[ℤ] ↥A) * Nat.card (K →ₐ[ℤ] ↥A)
        = Nat.card (flag.G i.castSucc →ₐ[ℤ] ↥A) * q ^ dt := by
      rw [hbrA, ← hAA, hg3s, hg3c, ht]
      ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne0) h1

  have h0 : Nat.card (fppfCohomology specInt L 0) = 1 :=
    (natCard_fppfCohomology_zero_eq_algHom_int L K e).trans
      (MultLayerFixedPoints.natCard_algHom_int_eq_one q hq2 hgenq hgalM)

  have hpkg := AlgebraicGeometry.exists_hom_restriction_muP_fppfCohomologyMap_ker_natCard_eq_pow_of_sectionsEquiv_of_ne_two
    p q hq2 K crK haK ftK flK hff hgenq hgalM L e hnat A hA dt hKA
  exact ⟨h0, hpkg⟩

end
end S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two
end P2MW
export P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_fppfCohomology_zero_cokernel_eq_one_and_exists_ker_natCard_eq_pow_of_kind_eq_mult_of_ne_two (solution)
