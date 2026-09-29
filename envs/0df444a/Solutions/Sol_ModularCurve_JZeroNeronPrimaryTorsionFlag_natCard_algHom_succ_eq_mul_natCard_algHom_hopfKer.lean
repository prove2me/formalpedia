-- Prove2me | solution 1 for ModularCurve.JZeroNeronPrimaryTorsionFlag.natCard_algHom_succ_eq_mul_natCard_algHom_hopfKer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c666afd7-fb6a-596b-87fc-1557a4c4c211

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_jZeroTorsionFinite
import Theorems.Thm_HopfAlgebra_algHom_comp_hopfKer_val_eq_iff
import Theorems.Thm_ModularCurve_eisensteinTorsionBar_self_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_algHom_succ_eq_mul_natCard_algHom_hopfKer
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd"
p2m_attr_erase "instance" "KatzModularForm.instNeg KatzModularForm.instSMul ModularCurve.instIsElliptic_tateBase ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing"
p2m_attr_erase "instance" "ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.LevelP.instAlgebraTorusQRingTorusRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingTorusQRingTorusRing ModularCurve.LevelP.instAwayTorusQRingTorusDenomTorusRing ModularCurve.LevelP.instCommRingTorusRing ModularCurve.LevelP.instAlgebraUnivBasisRingTorusRing ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero KatzModularForm.baseChange_zero ModularCurve.KatzGamma0Form.baseChange_sub ModularCurve.KatzGamma0Form.baseChange_zero ModularCurve.KatzGamma0Form.baseChange_toKatzLevelPForm KatzModularForm.baseChange_sub ModularCurve.KatzLevelPForm.baseChange_sub ModularCurve.KatzGamma0Form.baseChange_smul ModularCurve.KatzGamma0Form.baseChange_add ModularCurve.KatzLevelPForm.baseChange_swap KatzModularForm.baseChange_add ModularCurve.KatzLevelPForm.baseChange_neg ModularCurve.KatzLevelPForm.baseChange_smul ModularCurve.KatzGamma0Form.baseChange_neg ModularCurve.KatzLevelPForm.baseChange_add KatzModularForm.baseChange_smul ModularCurve.KatzLevelPForm.baseChange_zero KatzModularForm.baseChange_neg ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase"
p2m_attr_erase "simp" "ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP ModularCurve.LevelP.sClassify_tmul ModularCurve.LevelP.sLift_tmul WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.LevelPData.quotientBySndLine_swap ModularCurve.LevelP.smulX_one ModularCurve.LevelP.quotientByLine_a₃ ModularCurve.LevelP.quotientByLine_a₂ ModularCurve.LevelP.quotientByLine_a₁ ModularCurve.LevelPData.quotientByFstLine_swap ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def TateCurve.tateTorsionPoint_zero_zero ModularCurve.LevelP.TorusQRing.lift_yQ ModularCurve.LevelP.TorusQRing.lift_yP ModularCurve.LevelP.TorusQRing.lift_xQ ModularCurve.LevelP.TorusRing.lift_ofUniv ModularCurve.LevelP.TorusQRing.lift_xP ModularCurve.LevelP.TorusQRing.lift_ofUniv ModularCurve.LevelP.TorusRing.lift_algebraMap ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

namespace EisSelfBotV5
open ModularCurve

theorem eisensteinPrimaryTorsionBar_self_eq_bot (p : ℕ) [Fact p.Prime] (m : ℕ) :
    eisensteinPrimaryTorsionBar p p m = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨-, hx⟩
  have hk : ∀ k : ℕ, (eisensteinTorsionBar p p k : AddSubgroup (JZero p)) = ⊥ :=
    fun k => ModularCurve.eisensteinTorsionBar_self_eq_bot p k
  have : (⨆ k : ℕ, (eisensteinTorsionBar p p k : AddSubgroup (JZero p))) = ⊥ := by
    simp [hk]
  have hx' : x ∈ ⨆ k : ℕ, (eisensteinTorsionBar p p k : AddSubgroup (JZero p)) := hx
  rw [this] at hx'
  exact hx'
end EisSelfBotV5

noncomputable section

namespace CCountsN

open HopfAlgebra
open scoped TensorProduct

section Fibration

theorem natCard_eq_of_fibres {X Y Z : Type} (f : X → Y)
    (e : ∀ y : Y, {x : X // f x = y} ≃ Z) :
    Nat.card X = Nat.card Y * Nat.card Z := by
  have h : X ≃ Y × Z :=
    ((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e)).trans
      (Equiv.sigmaEquivProd Y Z)
  rw [Nat.card_congr h, Nat.card_prod]

end Fibration

section Kit

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Bialgebra R A]
    {B : Type} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B)
    {T : Type} [CommRing T] [Algebra R T]

def tr (ψ : A →ₐ[R] T) (χ : B →ₐ[R] T) : A →ₐ[R] T :=
  (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp (coaction π)

theorem tr_comp_val (ψ : A →ₐ[R] T) (χ : B →ₐ[R] T) :
    (tr π ψ χ).comp (hopfKer π).val = ψ.comp (hopfKer π).val := by
  apply AlgHom.ext
  rintro ⟨a, ha⟩
  show (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)) (coaction π a) = ψ a
  rw [coaction_eq_of_mem π ha, Algebra.TensorProduct.lift_tmul, map_one, mul_one]

def fibreEquiv
    (hiff : ∀ ψ ψ' : A →ₐ[R] T,
      ψ.comp (hopfKer π).val = ψ'.comp (hopfKer π).val
        ↔ ∃! χ : B →ₐ[R] T,
            (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp
              (HopfAlgebra.coaction π) = ψ')
    (ψ : A →ₐ[R] T) :
    {ψ' : A →ₐ[R] T // ψ'.comp (hopfKer π).val = ψ.comp (hopfKer π).val} ≃ (B →ₐ[R] T) where
  toFun ψ' := ((hiff ψ ψ'.1).mp ψ'.2.symm).exists.choose
  invFun χ := ⟨tr π ψ χ, tr_comp_val π ψ χ⟩
  left_inv ψ' := Subtype.ext ((hiff ψ ψ'.1).mp ψ'.2.symm).exists.choose_spec
  right_inv χ := by
    have h := (hiff ψ (tr π ψ χ)).mp (tr_comp_val π ψ χ).symm
    exact h.unique h.exists.choose_spec rfl

theorem natCard_algHom_eq_mul
    (hiff : ∀ ψ ψ' : A →ₐ[R] T,
      ψ.comp (hopfKer π).val = ψ'.comp (hopfKer π).val
        ↔ ∃! χ : B →ₐ[R] T,
            (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp
              (HopfAlgebra.coaction π) = ψ')
    (hsurj : Function.Surjective
      (fun ψ : A →ₐ[R] T => ψ.comp (hopfKer π).val)) :
    Nat.card (A →ₐ[R] T)
      = Nat.card (B →ₐ[R] T) * Nat.card (↥(hopfKer π) →ₐ[R] T) := by
  rw [mul_comm]
  refine natCard_eq_of_fibres (fun ψ : A →ₐ[R] T => ψ.comp (hopfKer π).val) (fun y => ?_)
  exact (Equiv.subtypeEquivRight (fun ψ' =>
      ⟨fun h => h.trans (hsurj y).choose_spec.symm,
       fun h => h.trans (hsurj y).choose_spec⟩)).trans
    (fibreEquiv π hiff (hsurj y).choose)

end Kit

section AlgClosedLeg

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Bialgebra R A]
    {B : Type} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B)

theorem exists_algHom_self_of_finiteType (k : Type) [Field k] [IsAlgClosed k]
    (C : Type) [CommRing C] [Nontrivial C] [Algebra k C] [Algebra.FiniteType k C] :
    Nonempty (C →ₐ[k] k) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k C›
  obtain ⟨M, hM⟩ := Ideal.exists_maximal C
  haveI : (Ideal.comap f.toRingHom M).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective f.toRingHom hf
  obtain ⟨x, hx⟩ :=
    MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k
      (I := Ideal.comap f.toRingHom M) ‹_›
  have hker : ∀ a ∈ RingHom.ker f, MvPolynomial.aeval x a = 0 := by
    intro a haa
    have h0 : f.toRingHom a = 0 := haa
    have h1 : a ∈ Ideal.comap f.toRingHom M := by
      rw [Ideal.mem_comap, h0]
      exact M.zero_mem
    rw [hx] at h1
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x a).mp h1
  refine ⟨((Ideal.Quotient.liftₐ (RingHom.ker f) (MvPolynomial.aeval x) hker).comp
    ((Ideal.quotientKerAlgEquivOfSurjective hf).symm : C →ₐ[k] _))⟩

variable {k : Type} [Field k] [IsAlgClosed k] [Algebra R k]

theorem res_surjective_of_isAlgClosed
    (hflat : Module.FaithfullyFlat ↥(hopfKer π) A)
    (hft : Algebra.FiniteType ↥(hopfKer π) A) :
    Function.Surjective (fun ψ : A →ₐ[R] k => ψ.comp (hopfKer π).val) := by
  intro x
  haveI := hflat
  letI : Algebra ↥(hopfKer π) k := x.toRingHom.toAlgebra
  haveI : IsScalarTower R ↥(hopfKer π) k :=
    IsScalarTower.of_algebraMap_eq fun r => (x.commutes r).symm

  haveI : Nontrivial (k ⊗[↥(hopfKer π)] A) :=
    Module.FaithfullyFlat.rTensor_nontrivial (R := ↥(hopfKer π)) (M := A) k
  haveI : Algebra.FiniteType k (k ⊗[↥(hopfKer π)] A) := by
    infer_instance
  obtain ⟨φ₀⟩ := exists_algHom_self_of_finiteType k (k ⊗[↥(hopfKer π)] A)

  refine ⟨(((φ₀.restrictScalars ↥(hopfKer π)).comp
    (Algebra.TensorProduct.includeRight :
      A →ₐ[↥(hopfKer π)] k ⊗[↥(hopfKer π)] A)).restrictScalars R), ?_⟩
  apply AlgHom.ext
  intro κ
  show φ₀ ((1 : k) ⊗ₜ[↥(hopfKer π)] ((hopfKer π).val κ)) = x κ
  have hval : (hopfKer π).val κ = κ • (1 : A) := by
    rw [Algebra.smul_def, mul_one]; rfl
  have h2 : (1 : k) ⊗ₜ[↥(hopfKer π)] ((hopfKer π).val κ)
      = (x κ) • ((1 : k) ⊗ₜ[↥(hopfKer π)] (1 : A)) := by
    rw [hval, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
    congr 1
  rw [h2, ← Algebra.TensorProduct.one_def, map_smul, map_one, smul_eq_mul, mul_one]

end AlgClosedLeg

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory

section Collapse

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m)

theorem exists_ne_algHom_pi (ℓ : ℕ) :
    ∃ φ₀ φ₁ : (Fin q → GaloisRep.ratLocalizedAt ℓ) →ₐ[GaloisRep.ratLocalizedAt ℓ]
        AlgebraicClosure ℚ, φ₀ ≠ φ₁ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have h01 : (0 : Fin q) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (Fact.out : q.Prime).one_lt] at hv
    exact zero_ne_one hv
  refine ⟨(Algebra.ofId _ _).comp (Pi.evalAlgHom _ _ 0),
    (Algebra.ofId _ _).comp (Pi.evalAlgHom _ _ 1), fun h => ?_⟩
  have := congrArg (fun f => f (Pi.single (0 : Fin q) (1 : GaloisRep.ratLocalizedAt ℓ))) h
  simp only [AlgHom.comp_apply, Pi.evalAlgHom_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm h01), map_one, map_zero] at this
  exact one_ne_zero this

theorem exists_ne_algHom_mu (ℓ : ℕ) :
    ∃ φ₀ φ₁ : (Polynomial (GaloisRep.ratLocalizedAt ℓ)
        ⧸ Ideal.span {(Polynomial.X : Polynomial (GaloisRep.ratLocalizedAt ℓ)) ^ q - 1})
          →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ, φ₀ ≠ φ₁ := by
  have hq : q.Prime := Fact.out

  have hsep : ((Polynomial.X : Polynomial (AlgebraicClosure ℚ)) ^ q - Polynomial.C 1).Separable := by
    refine Polynomial.separable_X_pow_sub_C (1 : AlgebraicClosure ℚ) ?_ one_ne_zero
    exact_mod_cast Nat.cast_ne_zero.mpr hq.ne_zero
  have hsplit : (((Polynomial.X : Polynomial (AlgebraicClosure ℚ)) ^ q - Polynomial.C 1).map
      (algebraMap (AlgebraicClosure ℚ) (AlgebraicClosure ℚ))).Splits :=
    IsAlgClosed.splits _
  have hcard : 1 < Fintype.card
      (((Polynomial.X : Polynomial (AlgebraicClosure ℚ)) ^ q - Polynomial.C 1).rootSet
        (AlgebraicClosure ℚ)) := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep hsplit]
    rw [Polynomial.natDegree_X_pow_sub_C]
    exact hq.one_lt
  obtain ⟨z₀, z₁, hz⟩ := Fintype.exists_pair_of_one_lt_card hcard
  have hroot : ∀ z : ((Polynomial.X : Polynomial (AlgebraicClosure ℚ)) ^ q
      - Polynomial.C 1).rootSet (AlgebraicClosure ℚ), (z : AlgebraicClosure ℚ) ^ q = 1 := by
    rintro ⟨z, hzz⟩
    have h0 := (Polynomial.mem_rootSet.mp hzz).2
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at h0
    exact h0

  have hker : ∀ z : AlgebraicClosure ℚ, z ^ q = 1 →
      ∀ a ∈ Ideal.span {(Polynomial.X : Polynomial (GaloisRep.ratLocalizedAt ℓ)) ^ q - 1},
        Polynomial.aeval z a = 0 := by
    intro z hzq a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_sub, map_pow, Polynomial.aeval_X, map_one, hzq, sub_self, zero_mul]
  refine ⟨Ideal.Quotient.liftₐ _ (Polynomial.aeval (z₀ : AlgebraicClosure ℚ))
      (hker z₀ (hroot z₀)),
    Ideal.Quotient.liftₐ _ (Polynomial.aeval (z₁ : AlgebraicClosure ℚ))
      (hker z₁ (hroot z₁)), fun h => ?_⟩
  have := congrArg (fun f => f (Ideal.Quotient.mk _
    (Polynomial.X : Polynomial (GaloisRep.ratLocalizedAt ℓ)))) h
  simp only [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom,
    Polynomial.aeval_X] at this
  exact hz (Subtype.ext this)

theorem nontrivial_withConv_lff (i : Fin flag.n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
    Nontrivial (WithConv (flag.Lff i ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ]
      AlgebraicClosure ℚ)) := by
  have key : ∃ ψ₀ ψ₁ : flag.Lff i ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ]
      AlgebraicClosure ℚ, ψ₀ ≠ ψ₁ := by
    cases hk : flag.kind i with
    | const =>
      obtain ⟨e⟩ := flag.layerIsoConst i hk ℓ hℓ hℓp
      obtain ⟨φ₀, φ₁, hφ⟩ := exists_ne_algHom_pi q ℓ
      refine ⟨φ₀.comp (e : _ →ₐ[GaloisRep.ratLocalizedAt ℓ] _),
        φ₁.comp (e : _ →ₐ[GaloisRep.ratLocalizedAt ℓ] _), fun h => hφ ?_⟩
      apply AlgHom.ext
      intro z
      have := congrArg (fun f => f (e.symm z)) h
      simpa [AlgEquiv.apply_symm_apply] using this
    | mult =>
      obtain ⟨e⟩ := flag.layerIsoMult i hk ℓ hℓ hℓp
      obtain ⟨φ₀, φ₁, hφ⟩ := exists_ne_algHom_mu q ℓ
      refine ⟨φ₀.comp (e : _ →ₐ[GaloisRep.ratLocalizedAt ℓ] _),
        φ₁.comp (e : _ →ₐ[GaloisRep.ratLocalizedAt ℓ] _), fun h => hφ ?_⟩
      apply AlgHom.ext
      intro z
      have := congrArg (fun f => f (e.symm z)) h
      simpa [AlgEquiv.apply_symm_apply] using this
  obtain ⟨ψ₀, ψ₁, hψ⟩ := key
  exact ⟨WithConv.toConv ψ₀, WithConv.toConv ψ₁, fun h => hψ (WithConv.toConv_injective h)⟩

theorem false_of_eisensteinPrimaryTorsionBar_eq_bot
    (heis : eisensteinPrimaryTorsionBar p q m = ⊥) (i : Fin flag.n) : False := by

  have h1 : flag.genericStep i.succ = ⊥ := le_bot_iff.mp (by
    rw [← heis]
    exact flag.genericStep_le_tors i.succ)

  obtain ⟨ℓ, hle, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  have hℓp : ℓ ≠ p := by omega

  haveI hsub : Subsingleton ↥(flag.genericStep i.succ) := by
    rw [h1]
    exact ⟨fun a b => Subtype.ext (by
      rw [AddSubgroup.mem_bot.mp a.2, AddSubgroup.mem_bot.mp b.2])⟩
  haveI : Subsingleton (↥(flag.genericStep i.succ)
      ⧸ (flag.genericStep i.castSucc).addSubgroupOf (flag.genericStep i.succ)) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with | H a =>
    induction b using QuotientAddGroup.induction_on with | H b =>
    exact congrArg _ (Subsingleton.elim a b)
  haveI := (flag.Lff_points i ℓ hℓ hℓp).subsingleton
  haveI := nontrivial_withConv_lff p q A hA C m flag i ℓ hℓ hℓp
  exact false_of_nontrivial_of_subsingleton
    (WithConv (flag.Lff i ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ))

end Collapse

open scoped TensorProduct

section PointsField

variable {k : Type*} [Field k] [IsAlgClosed k] {R : Type*} [CommRing R] [Algebra k R]
  [Algebra.FiniteType k R]

theorem exists_algHom_ker_eq (m : Ideal R) (hm : m.IsMaximal) :
    ∃ φ : R →ₐ[k] k, RingHom.ker φ.toRingHom = m := by
  haveI := hm
  letI := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) (Ideal.Quotient.mkₐ_surjective k m)
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := inferInstance
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R ⧸ m)
  let e : k ≃+* (R ⧸ m) := RingEquiv.ofBijective (algebraMap k (R ⧸ m)) hbij
  refine ⟨{ toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk m), commutes' := ?_ }, ?_⟩
  · intro c
    show e.symm (Ideal.Quotient.mk m (algebraMap k R c)) = c
    apply e.injective
    rw [RingEquiv.apply_symm_apply, Ideal.Quotient.mk_algebraMap]
    rfl
  · ext r
    show e.symm (Ideal.Quotient.mk m r) = 0 ↔ r ∈ m
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

theorem finite_maximalIdeal (hfin : Finite (R →ₐ[k] k)) :
    Finite {m : Ideal R // m.IsMaximal} := by
  classical
  refine Finite.of_injective
    (fun m : {m : Ideal R // m.IsMaximal} => (exists_algHom_ker_eq (k := k) m.1 m.2).choose) ?_
  intro m₁ m₂ h
  dsimp only at h
  apply Subtype.ext
  rw [← (exists_algHom_ker_eq (k := k) m₁.1 m₁.2).choose_spec,
    ← (exists_algHom_ker_eq (k := k) m₂.1 m₂.2).choose_spec, h]

variable [IsDomain R]

theorem isField_of_finite_algHom (hfin : Finite (R →ₐ[k] k)) : IsField R := by
  classical
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k) (B := R)
  haveI := finite_maximalIdeal (k := k) (R := R) hfin
  haveI : Fintype {m : Ideal R // m.IsMaximal} := Fintype.ofFinite _
  have hjac : (⊥ : Ideal R).jacobson = ⊥ :=
    IsJacobsonRing.out' ⊥ (Ideal.IsPrime.isRadical Ideal.isPrime_bot)
  by_contra hnf

  have hne : ∀ m : {m : Ideal R // m.IsMaximal}, (m : Ideal R) ≠ ⊥ := by
    intro m hm
    apply hnf
    have hmax : (⊥ : Ideal R).IsMaximal := hm ▸ m.2
    have hq : IsField (R ⧸ (⊥ : Ideal R)) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient ⊥).mp hmax
    exact MulEquiv.isField hq (RingEquiv.quotientBot R).symm.toMulEquiv

  have hx : ∀ m : {m : Ideal R // m.IsMaximal}, ∃ x : R, x ∈ (m : Ideal R) ∧ x ≠ 0 := by
    intro m
    by_contra h
    apply hne m
    refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
    by_contra hy0
    exact h ⟨y, hy, hy0⟩
  choose x hxm hx0 using hx
  have hz0 : (∏ m, x m) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ => hx0 m
  have hzm : ∀ m : {m : Ideal R // m.IsMaximal}, (∏ m, x m) ∈ (m : Ideal R) := by
    intro m
    rw [← Finset.mul_prod_erase Finset.univ x (Finset.mem_univ m)]
    exact Ideal.mul_mem_right _ _ (hxm m)
  have hzj : (∏ m, x m) ∈ (⊥ : Ideal R).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro J ⟨-, hJ⟩
    exact hzm ⟨J, hJ⟩
  rw [hjac, Ideal.mem_bot] at hzj
  exact hz0 hzj

theorem algebraMap_surjective_of_finite_algHom (hfin : Finite (R →ₐ[k] k)) :
    Function.Surjective (algebraMap k R) := by
  have hF := isField_of_finite_algHom (k := k) (R := R) hfin
  haveI hmax : (⊥ : Ideal R).IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient ⊥).mpr
      (MulEquiv.isField hF (RingEquiv.quotientBot R).toMulEquiv)
  letI := Ideal.Quotient.field (⊥ : Ideal R)
  haveI : Algebra.FiniteType k (R ⧸ (⊥ : Ideal R)) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k (⊥ : Ideal R))
      (Ideal.Quotient.mkₐ_surjective k ⊥)
  haveI : Module.Finite k (R ⧸ (⊥ : Ideal R)) :=
    finite_of_finite_type_of_isJacobsonRing k (R ⧸ (⊥ : Ideal R))
  haveI : Algebra.IsIntegral k (R ⧸ (⊥ : Ideal R)) := inferInstance
  have hinj : Function.Injective (Ideal.Quotient.mkₐ k (⊥ : Ideal R)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mp ha
  haveI : Algebra.IsIntegral k R :=
    ⟨fun r => (isIntegral_algHom_iff (Ideal.Quotient.mkₐ k (⊥ : Ideal R)) hinj).mp
      (Algebra.IsIntegral.isIntegral _)⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R)).2

end PointsField

section Descent

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
  {D : Type*} [CommRing D] [IsDomain D] [Algebra A D] [Algebra.FiniteType A D]

theorem exists_algHom_injective (hinj : Function.Injective (algebraMap A D))
    (hfin : Finite (D →ₐ[A] Ω)) :
    ∃ ι : D →ₐ[A] Ω, Function.Injective ι := by
  classical
  let L := FractionRing D
  haveI : IsScalarTower A D L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hg : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A D L]
    exact (IsFractionRing.injective D L).comp hinj
  let θ : Ω →+* L := IsFractionRing.lift hg
  letI : Algebra Ω L := θ.toAlgebra
  haveI : IsScalarTower A Ω L :=
    IsScalarTower.of_algebraMap_eq fun a => (IsFractionRing.lift_algebraMap hg a).symm

  let Φ : Ω ⊗[A] D →ₐ[Ω] L :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω L) (IsScalarTower.toAlgHom A D L)
      (fun _ _ => Commute.all _ _)
  let D' : Subalgebra Ω L := Φ.range
  haveI : Algebra.FiniteType Ω D' :=
    Algebra.FiniteType.of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  have hΦ : ∀ (c : Ω) (d : D), Φ (c ⊗ₜ[A] d) = θ c * algebraMap D L d := fun c d => by
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  have hmemD : ∀ d : D, algebraMap D L d ∈ D' := fun d =>
    ⟨(1 : Ω) ⊗ₜ[A] d, by show Φ ((1 : Ω) ⊗ₜ[A] d) = algebraMap D L d; rw [hΦ, map_one, one_mul]⟩

  let jD : D →ₐ[A] D' :=
    (Φ.rangeRestrict.restrictScalars A).comp Algebra.TensorProduct.includeRight
  have hjD : ∀ d : D, ((jD d : D') : L) = algebraMap D L d := fun d => by
    show Φ ((1 : Ω) ⊗ₜ[A] d) = algebraMap D L d
    rw [hΦ, map_one, one_mul]

  have hfin' : Finite (D' →ₐ[Ω] Ω) := by
    refine Finite.of_injective (fun χ : D' →ₐ[Ω] Ω => (χ.restrictScalars A).comp jD) ?_
    intro χ₁ χ₂ h
    dsimp only at h
    apply AlgHom.ext
    intro y
    obtain ⟨z, rfl⟩ := Φ.rangeRestrict_surjective y
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul c d =>
      have hcd : Φ.rangeRestrict (c ⊗ₜ[A] d) = algebraMap Ω D' c * jD d := by
        apply Subtype.ext
        show Φ (c ⊗ₜ[A] d) = θ c * ((jD d : D') : L)
        rw [hjD, hΦ]
      rw [hcd, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
      exact congrArg (fun t => algebraMap Ω Ω c * t) (DFunLike.congr_fun h d)
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  have hsurj := algebraMap_surjective_of_finite_algHom (k := Ω) (R := D') hfin'

  have hex : ∀ d : D, ∃ c : Ω, θ c = algebraMap D L d := fun d => by
    obtain ⟨c, hc⟩ := hsurj ⟨algebraMap D L d, hmemD d⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  choose ι hι using hex
  have hθ : Function.Injective θ := θ.injective
  refine ⟨{ toFun := ι, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
            commutes' := ?_ }, ?_⟩
  · apply hθ; rw [hι, map_one, map_one]
  · intro a b; apply hθ; rw [hι, map_mul, map_mul, hι, hι]
  · apply hθ; rw [hι, map_zero, map_zero]
  · intro a b; apply hθ; rw [hι, map_add, map_add, hι, hι]
  · intro a
    apply hθ
    rw [hι, ← IsScalarTower.algebraMap_apply A D L, IsScalarTower.algebraMap_apply A Ω L]
    rfl
  · intro d₁ d₂ h
    apply IsFractionRing.injective D L
    rw [← hι d₁, ← hι d₂]
    exact congrArg θ h

omit [IsAlgClosed Ω] [IsDomain D] [Algebra.FiniteType A D] in

theorem mem_of_map_maximalIdeal_ne_top (ι : D →ₐ[A] Ω) (hι : Function.Injective ι)
    (hD : (IsLocalRing.maximalIdeal A).map (algebraMap A D) ≠ ⊤) (d : D) : ι d ∈ A := by
  by_contra h
  have h0 : ι d ≠ 0 := fun h0 => h (h0 ▸ A.zero_mem)
  have hinv : (ι d)⁻¹ ∈ A := (A.mem_or_inv_mem _).resolve_left h
  have hamax : (⟨(ι d)⁻¹, hinv⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
    rintro ⟨u, hu⟩
    apply h
    have hd : ι d = (((u⁻¹ : Aˣ) : A) : Ω) := by
      have h1 : (ι d)⁻¹ * (((u⁻¹ : Aˣ) : A) : Ω) = 1 := by
        have h2 : ((u : A) : Ω) * (((u⁻¹ : Aˣ) : A) : Ω) = 1 := by
          rw [← show (((u : A) * ((u⁻¹ : Aˣ) : A) : A) : Ω) = ((u : A) : Ω) * (((u⁻¹ : Aˣ) : A) : Ω)
            from rfl, u.mul_inv]
          rfl
        rwa [hu] at h2
      calc ι d = ι d * ((ι d)⁻¹ * (((u⁻¹ : Aˣ) : A) : Ω)) := by rw [h1, mul_one]
        _ = (((u⁻¹ : Aˣ) : A) : Ω) := by rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]
    rw [hd]
    exact Subtype.mem _
  apply hD
  rw [Ideal.eq_top_iff_one]
  have hprod : d * algebraMap A D ⟨(ι d)⁻¹, hinv⟩ = 1 := by
    apply hι
    rw [map_mul, map_one, AlgHom.commutes]
    exact mul_inv_cancel₀ h0
  rw [← hprod]
  exact Ideal.mul_mem_left _ d (Ideal.mem_map_of_mem _ hamax)

end Descent

section Extension

variable {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)

def zAlgHom {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (f : S →+* T) :
    S →ₐ[ℤ] T :=
  { f with commutes' := fun n => by simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe, eq_intCast, map_intCast] }

@[scoped simp] theorem zAlgHom_apply {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T]
    (f : S →+* T) (s : S) : zAlgHom f s = f s := rfl

omit [IsAlgClosed Ω] in

theorem exists_prime_comap_eq_bot {F : Type*} [CommRing F] [Algebra A F]
    [Module.FaithfullyFlat A F] :
    ∃ P : Ideal F, P.IsPrime ∧ Function.Injective (algebraMap A (F ⧸ P)) ∧
      (IsLocalRing.maximalIdeal A).map (algebraMap A (F ⧸ P)) ≠ ⊤ := by

  have hmF : (IsLocalRing.maximalIdeal A).map (algebraMap A F) ≠ ⊤ := by
    intro htop
    apply Module.FaithfullyFlat.submodule_ne_top (R := A) (M := F)
      (IsLocalRing.maximalIdeal.isMaximal A)
    rw [Ideal.smul_top_eq_map, htop, Submodule.restrictScalars_top]
  obtain ⟨𝔫, h𝔫max, hle⟩ := Ideal.exists_le_maximal _ hmF
  haveI : 𝔫.IsPrime := h𝔫max.isPrime
  have hunder : 𝔫.comap (algebraMap A F) = IsLocalRing.maximalIdeal A :=
    ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_ne_top _ h𝔫max.ne_top)
      (Ideal.map_le_iff_le_comap.mp hle)).symm
  haveI : 𝔫.LiesOver (IsLocalRing.maximalIdeal A) := ⟨by rw [Ideal.under_def, hunder]⟩

  obtain ⟨P, hP𝔫, hPprime, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal A)) (q := IsLocalRing.maximalIdeal A)
      𝔫 bot_le
  haveI := hPprime
  refine ⟨P, hPprime, ?_, ?_⟩
  · intro a b hab
    rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq,
      ← map_sub] at hab
    have h2 : a - b ∈ P.comap (algebraMap A F) := hab
    rw [← Ideal.under_def, ← hPover.over, Ideal.mem_bot, sub_eq_zero] at h2
    exact h2
  · intro htop
    apply h𝔫max.ne_top
    have h1 : (IsLocalRing.maximalIdeal A).map (algebraMap A (F ⧸ P)) ≤ 𝔫.map (Ideal.Quotient.mk P) := by
      rw [show algebraMap A (F ⧸ P) = (Ideal.Quotient.mk P).comp (algebraMap A F) from rfl,
        ← Ideal.map_map]
      exact Ideal.map_mono hle
    rw [htop, top_le_iff] at h1
    have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk P)) h1
    rw [Ideal.comap_top, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hP𝔫] at h2
    exact h2

theorem exists_ringHom_retract {D : Type*} [CommRing D] [IsDomain D] [Algebra A D]
    [Algebra.FiniteType A D] (hinj : Function.Injective (algebraMap A D))
    (hmD : (IsLocalRing.maximalIdeal A).map (algebraMap A D) ≠ ⊤) (hfin : Finite (D →ₐ[A] Ω)) :
    ∃ f : D →+* A, ∀ a : A, f (algebraMap A D a) = a := by
  obtain ⟨ι, hι⟩ := exists_algHom_injective A hinj hfin
  have hmem := mem_of_map_maximalIdeal_ne_top A ι hι hmD
  refine ⟨{ toFun := fun d => ⟨ι d, hmem d⟩
            map_one' := Subtype.ext (map_one ι)
            map_mul' := fun a b => Subtype.ext (map_mul ι a b)
            map_zero' := Subtype.ext (map_zero ι)
            map_add' := fun a b => Subtype.ext (map_add ι a b) }, fun a => ?_⟩
  exact Subtype.ext (ι.commutes a)

variable {R : Type*} [CommRing R] [Algebra ℤ R] (K : Subalgebra ℤ R) [Algebra K A]
  {D : Type*} [CommRing D] [Algebra A D]

omit [IsAlgClosed Ω] in

theorem one_tmul_coe (κ : K) :
    (1 : A) ⊗ₜ[K] (κ : R) = algebraMap A (A ⊗[K] R) (algebraMap K A κ) := by
  have h1 : (κ : R) = κ • (1 : R) := by rw [Subalgebra.smul_def, smul_eq_mul, mul_one]
  rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

noncomputable def toD (π : A ⊗[K] R →ₐ[A] D) : R →ₐ[ℤ] D :=
  zAlgHom (S := R) (T := D)
    (π.toRingHom.comp (Algebra.TensorProduct.includeRight : R →ₐ[K] A ⊗[K] R).toRingHom)

omit [IsAlgClosed Ω] in
theorem toD_apply (π : A ⊗[K] R →ₐ[A] D) (r : R) : toD A K π r = π ((1 : A) ⊗ₜ[K] r) := rfl

omit [IsAlgClosed Ω] in
theorem toD_coe (π : A ⊗[K] R →ₐ[A] D) (κ : K) :
    toD A K π (κ : R) = algebraMap A D (algebraMap K A κ) := by
  rw [toD_apply, one_tmul_coe, AlgHom.commutes]

variable [Algebra ℤ Ω]

omit [IsAlgClosed Ω] in

theorem finite_algHom_of_surjective (π : A ⊗[K] R →ₐ[A] D) (hπ : Function.Surjective π)
    (x' : K →ₐ[ℤ] Ω) (hx' : ∀ κ, x' κ = (algebraMap K A κ : Ω))
    (hfin : Finite {ψ : R →ₐ[ℤ] Ω // ψ.comp K.val = x'}) : Finite (D →ₐ[A] Ω) := by
  refine Finite.of_injective (fun φ : D →ₐ[A] Ω =>
    (⟨(zAlgHom (S := D) (T := Ω) φ.toRingHom).comp (toD A K π), ?_⟩ :
      {ψ : R →ₐ[ℤ] Ω // ψ.comp K.val = x'})) ?_
  · apply AlgHom.ext
    intro κ
    show φ (toD A K π (κ : R)) = x' κ
    rw [toD_coe, AlgHom.commutes, hx']
    rfl
  · intro φ₁ φ₂ h
    have h' : ∀ r : R, φ₁ (π ((1 : A) ⊗ₜ[K] r)) = φ₂ (π ((1 : A) ⊗ₜ[K] r)) := fun r =>
      DFunLike.congr_fun (congrArg Subtype.val h) r
    apply AlgHom.ext
    intro y
    obtain ⟨z, rfl⟩ := hπ y
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a r =>
      have har : (a ⊗ₜ[K] r : A ⊗[K] R) = algebraMap A (A ⊗[K] R) a * ((1 : A) ⊗ₜ[K] r) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [har, map_mul, AlgHom.commutes, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, h' r]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]

omit [IsAlgClosed Ω] [Algebra K A] in

theorem finiteType_subalgebra [Algebra.FiniteType ℤ R] : Algebra.FiniteType K R :=
  Algebra.FiniteType.of_restrictScalars_finiteType ℤ K R

omit [Algebra K A] in

theorem exists_algHom_comp_val_eq [Module.FaithfullyFlat K R] [Algebra.FiniteType ℤ R]
    (x : K →ₐ[ℤ] A) (x' : K →ₐ[ℤ] Ω) (hx' : ∀ κ, x' κ = (x κ : Ω))
    (hfin : Finite {ψ : R →ₐ[ℤ] Ω // ψ.comp K.val = x'}) :
    ∃ ψ : R →ₐ[ℤ] A, ψ.comp K.val = x := by
  classical
  letI : Algebra K A := x.toRingHom.toAlgebra
  have hx : ∀ κ, algebraMap K A κ = x κ := fun _ => rfl
  haveI : Algebra.FiniteType K R := finiteType_subalgebra K
  obtain ⟨P, hPprime, hinjD, hmD⟩ := exists_prime_comap_eq_bot A (F := A ⊗[K] R)
  haveI := hPprime
  haveI : Algebra.FiniteType A ((A ⊗[K] R) ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A P) (Ideal.Quotient.mkₐ_surjective A P)
  have hfinD := finite_algHom_of_surjective A K (Ideal.Quotient.mkₐ A P)
    (Ideal.Quotient.mkₐ_surjective A P) x' (fun κ => by rw [hx', hx]) hfin
  obtain ⟨f, hf⟩ := exists_ringHom_retract A hinjD hmD hfinD
  refine ⟨(zAlgHom (S := (A ⊗[K] R) ⧸ P) (T := A) f).comp (toD A K (Ideal.Quotient.mkₐ A P)), ?_⟩
  apply AlgHom.ext
  intro κ
  show f (toD A K (Ideal.Quotient.mkₐ A P) (κ : R)) = x κ
  rw [toD_coe, hf, hx]

end Extension

section Flag

open ModularCurve ValuationSubring

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m)

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

theorem finite_genericStep (j : Fin (flag.n + 1)) : Finite ↥(flag.genericStep j) :=
  haveI := finite_eisensteinPrimaryTorsionBar p q m
  Finite.of_injective _ (AddSubgroup.inclusion_injective (flag.genericStep_le_tors j))

noncomputable def toStep (j : Fin (flag.n + 1)) (g : flag.G j →ₐ[ℤ] AlgebraicClosure ℚ) :
    ↥(flag.genericStep j) :=
  ⟨(C.genericPoints m (WithConv.toConv (g.comp (flag.π j))) : JZero p),
    (flag.genericStep_pin j _).mpr ⟨g, rfl⟩⟩

theorem toStep_injective (j : Fin (flag.n + 1)) :
    Function.Injective (toStep p q A hA C m flag j) := by
  intro g₁ g₂ h
  have h1 : (C.genericPoints m (WithConv.toConv (g₁.comp (flag.π j))) : JZero p)
      = (C.genericPoints m (WithConv.toConv (g₂.comp (flag.π j))) : JZero p) :=
    congrArg (fun z : ↥(flag.genericStep j) => (z : JZero p)) h
  have h2 : C.genericPoints m (WithConv.toConv (g₁.comp (flag.π j)))
      = C.genericPoints m (WithConv.toConv (g₂.comp (flag.π j))) := Subtype.ext h1
  have h3 := (C.genericPoints m).injective h2
  have h4 : g₁.comp (flag.π j) = g₂.comp (flag.π j) := WithConv.toConv_injective h3
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := flag.π_surj j x
  exact AlgHom.congr_fun h4 y

theorem toStep_surjective (j : Fin (flag.n + 1)) :
    Function.Surjective (toStep p q A hA C m flag j) := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg⟩ := (flag.genericStep_pin j x).mp hx
  exact ⟨g, Subtype.ext hg⟩

noncomputable def algHomEquivStep (j : Fin (flag.n + 1)) :
    (flag.G j →ₐ[ℤ] AlgebraicClosure ℚ) ≃ ↥(flag.genericStep j) :=
  Equiv.ofBijective (toStep p q A hA C m flag j)
    ⟨toStep_injective p q A hA C m flag j, toStep_surjective p q A hA C m flag j⟩

theorem natCard_algHom_eq_natCard_step (j : Fin (flag.n + 1)) :
    Nat.card (flag.G j →ₐ[ℤ] AlgebraicClosure ℚ) = Nat.card ↥(flag.genericStep j) :=
  Nat.card_congr (algHomEquivStep p q A hA C m flag j)

theorem finite_algHom_algebraicClosure (j : Fin (flag.n + 1)) :
    Finite (flag.G j →ₐ[ℤ] AlgebraicClosure ℚ) :=
  haveI := finite_genericStep p q A hA C m flag j
  Finite.of_equiv _ (algHomEquivStep p q A hA C m flag j).symm

theorem exists_algHom_comp_hopfKer_val_eq (i : Fin flag.n)
    (qc : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
    (hflat : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) (flag.G i.succ))
    (x : ↥(HopfAlgebra.hopfKer qc) →ₐ[ℤ] ↥A) :
    ∃ ψ : flag.G i.succ →ₐ[ℤ] ↥A, ψ.comp (HopfAlgebra.hopfKer qc).val = x := by
  haveI := hflat
  haveI := finite_algHom_algebraicClosure p q A hA C m flag i.succ
  exact exists_algHom_comp_val_eq A (HopfAlgebra.hopfKer qc) x
    ((zAlgHom (S := ↥A) (T := AlgebraicClosure ℚ) A.subtype).comp x) (fun _ => rfl)
    (Finite.of_injective _ Subtype.val_injective)

theorem comp_hopfKer_val_surjective (i : Fin flag.n)
    (qc : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
    (hflat : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) (flag.G i.succ)) :
    Function.Surjective (fun ψ : flag.G i.succ →ₐ[ℤ] ↥A => ψ.comp (HopfAlgebra.hopfKer qc).val) :=
  fun x => exists_algHom_comp_hopfKer_val_eq p q A hA C m flag i qc hflat x

end Flag

open ModularCurve ValuationSubring
open scoped TensorProduct

section ResidueFiniteness

variable (q : ℕ) [Fact q.Prime]

def toZModAlgHom {B : Type} [CommRing B] [Algebra ℤ B] [Algebra (ZMod q) B]
    (φ : B →ₐ[ℤ] AlgebraicClosure (ZMod q)) : B →ₐ[ZMod q] AlgebraicClosure (ZMod q) where
  toRingHom := φ.toRingHom
  commutes' := by
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    intro c
    show φ.toRingHom ((algebraMap (ZMod q) B) c)
      = (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) c
    have hc : ((c.val : ℕ) : ZMod q) = c := ZMod.natCast_rightInverse c
    calc φ.toRingHom ((algebraMap (ZMod q) B) c)
        = φ.toRingHom ((algebraMap (ZMod q) B) ((c.val : ℕ) : ZMod q)) := by rw [hc]
      _ = φ.toRingHom ((c.val : ℕ) : B) := by rw [map_natCast]
      _ = ((c.val : ℕ) : AlgebraicClosure (ZMod q)) := map_natCast φ.toRingHom _
      _ = (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) ((c.val : ℕ) : ZMod q) :=
          (map_natCast _ _).symm
      _ = (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))) c := by rw [hc]

variable (R : Type) [CommRing R]

abbrev ModQ : Type := R ⧸ Ideal.span {(q : R)}

omit [Fact q.Prime] in
theorem natCast_modQ_eq_zero : ((q : ℕ) : ModQ q R) = 0 := by
  have h : ((q : ℕ) : ModQ q R) = Ideal.Quotient.mk (Ideal.span {(q : R)}) (q : R) :=
    (map_natCast (Ideal.Quotient.mk (Ideal.span {(q : R)})) q).symm
  rw [h, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

noncomputable scoped instance : Algebra (ZMod q) (ModQ q R) :=
  ZMod.algebra' (R := ModQ q R) (m := ringChar (ModQ q R)) (n := q)
    (h := ringChar.dvd (natCast_modQ_eq_zero q R))

theorem finite_modQ [Algebra ℤ R]
    (hfin : Module.Finite ↥(GaloisRep.ratLocalizedAt q)
      (TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt q) R)) :
    Module.Finite (ZMod q) (ModQ q R) := by
  haveI := hfin

  letI algRq : Algebra ↥(GaloisRep.ratLocalizedAt q) (ModQ q R) :=
    ((algebraMap (ZMod q) (ModQ q R)).comp (GaloisRep.ratLocalizedAtResidue q)).toAlgebra
  haveI : IsScalarTower ℤ ↥(GaloisRep.ratLocalizedAt q) (ModQ q R) := ⟨fun z r a => by
    simp only [zsmul_eq_mul, Algebra.smul_def, map_mul, eq_intCast, map_intCast, mul_assoc]⟩

  have hsurj : Function.Surjective
      ((Ideal.Quotient.mk (Ideal.span {(q : R)})).toAddMonoidHom.toIntLinearMap.liftBaseChange
        ↥(GaloisRep.ratLocalizedAt q)) := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨1 ⊗ₜ x, by rw [LinearMap.liftBaseChange_tmul, one_smul]; rfl⟩
  haveI hfinRq : Module.Finite ↥(GaloisRep.ratLocalizedAt q) (ModQ q R) :=
    Module.Finite.of_surjective _ hsurj

  have key : ∀ (r : ↥(GaloisRep.ratLocalizedAt q)) (a : ModQ q R),
      r • a = (GaloisRep.ratLocalizedAtResidue q r) • a := by
    intro r a
    rw [Algebra.smul_def, Algebra.smul_def]
    congr 1
  obtain ⟨s, hs⟩ := hfinRq.fg_top
  refine ⟨⟨s, ?_⟩⟩

  let N : Submodule ↥(GaloisRep.ratLocalizedAt q) (ModQ q R) :=
    { carrier := (Submodule.span (ZMod q) (↑s : Set (ModQ q R)) : Set (ModQ q R))
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun r a ha => by
        show r • a ∈ Submodule.span (ZMod q) (↑s : Set (ModQ q R))
        rw [key r a]
        exact Submodule.smul_mem _ _ ha }
  have hN : (⊤ : Submodule ↥(GaloisRep.ratLocalizedAt q) (ModQ q R)) ≤ N := by
    rw [← hs]
    exact Submodule.span_le.mpr Submodule.subset_span
  exact le_antisymm le_top (fun a _ => hN Submodule.mem_top)

theorem finite_algHom_algebraicClosure_zmod [Algebra ℤ R]
    (hfin : Module.Finite ↥(GaloisRep.ratLocalizedAt q)
      (TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt q) R)) :
    Finite (R →ₐ[ℤ] AlgebraicClosure (ZMod q)) := by
  haveI := finite_modQ q R hfin
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q

  have hkill : ∀ φ : R →ₐ[ℤ] AlgebraicClosure (ZMod q),
      ∀ a ∈ Ideal.span {(q : R)}, φ a = 0 := by
    intro φ a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

  haveI : Finite ((ModQ q R) →ₐ[ZMod q] AlgebraicClosure (ZMod q)) := Finite.algHom _ _ _
  refine Finite.of_injective
    (fun φ : R →ₐ[ℤ] AlgebraicClosure (ZMod q) =>
      toZModAlgHom q (Ideal.Quotient.liftₐ (Ideal.span {(q : R)}) φ (hkill φ))) ?_
  intro φ₁ φ₂ h
  apply AlgHom.ext
  intro x
  have hx := congrArg (fun ψ : (ModQ q R) →ₐ[ZMod q] AlgebraicClosure (ZMod q) =>
    ψ (Ideal.Quotient.mk (Ideal.span {(q : R)}) x)) h
  simpa only [toZModAlgHom, AlgHom.coe_mk, Ideal.Quotient.liftₐ_apply,
    Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hx

end ResidueFiniteness

section FlagConjFour

variable (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m)

theorem finite_baseChange_G (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (j : Fin (flag.n + 1)) :
    Module.Finite ↥(GaloisRep.ratLocalizedAt ℓ)
      (TensorProduct ℤ ↥(GaloisRep.ratLocalizedAt ℓ) (flag.G j)) := by
  haveI := C.ff_finite m ℓ hℓ hℓp
  refine Module.Finite.of_surjective
    ((flag.π j).toAddMonoidHom.toIntLinearMap.baseChange ↥(GaloisRep.ratLocalizedAt ℓ)) ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective _ (flag.π_surj j)

theorem finite_algHom_step_algebraicClosure_zmod (hqp : q ≠ p) (j : Fin (flag.n + 1)) :
    Finite (flag.G j →ₐ[ℤ] AlgebraicClosure (ZMod q)) :=
  finite_algHom_algebraicClosure_zmod q (flag.G j)
    (finite_baseChange_G p q A hA C m flag q (Fact.out : q.Prime) hqp j)

end FlagConjFour

end CCountsN
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_algHom_succ_eq_mul_natCard_algHom_hopfKer.CCountsN"

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
open HopfAlgebra CCountsN

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (qc : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
    (hHG : HopfAlgebra.IsHopfGalois qc)
    (hflat : Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) (flag.G i.succ)) :
    Nat.card (flag.G i.succ →ₐ[ℤ] AlgebraicClosure ℚ)
        = Nat.card (flag.G i.castSucc →ₐ[ℤ] AlgebraicClosure ℚ)
          * Nat.card (↥(HopfAlgebra.hopfKer qc) →ₐ[ℤ] AlgebraicClosure ℚ) ∧
      Nat.card (flag.G i.succ →ₐ[ℤ] ↥A)
        = Nat.card (flag.G i.castSucc →ₐ[ℤ] ↥A)
          * Nat.card (↥(HopfAlgebra.hopfKer qc) →ₐ[ℤ] ↥A) ∧
      Nat.card (flag.G i.succ →ₐ[ℤ] AlgebraicClosure (ZMod q))
        = Nat.card (flag.G i.castSucc →ₐ[ℤ] AlgebraicClosure (ZMod q))
          * Nat.card (↥(HopfAlgebra.hopfKer qc) →ₐ[ℤ] AlgebraicClosure (ZMod q)) ∧
      Finite (flag.G i.castSucc →ₐ[ℤ] AlgebraicClosure (ZMod q)) := by
  by_cases hqp : q = p
  · subst hqp
    exact (CCountsN.false_of_eisensteinPrimaryTorsionBar_eq_bot q q A hA C m flag
      (EisSelfBotV5.eisensteinPrimaryTorsionBar_self_eq_bot q m) i).elim

  have hft : Algebra.FiniteType ↥(hopfKer qc) (flag.G i.succ) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := ℤ) (S := ↥(hopfKer qc))
      (A := flag.G i.succ)
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    exact natCard_algHom_eq_mul qc
      (fun ψ ψ' => HopfAlgebra.algHom_comp_hopfKer_val_eq_iff qc hHG ψ ψ')
      (res_surjective_of_isAlgClosed qc hflat hft)
  ·
    exact natCard_algHom_eq_mul qc
      (fun ψ ψ' => HopfAlgebra.algHom_comp_hopfKer_val_eq_iff qc hHG ψ ψ')
      (comp_hopfKer_val_surjective p q A hA C m flag i qc hflat)
  ·
    exact natCard_algHom_eq_mul qc
      (fun ψ ψ' => HopfAlgebra.algHom_comp_hopfKer_val_eq_iff qc hHG ψ ψ')
      (res_surjective_of_isAlgClosed qc hflat hft)
  ·
    exact finite_algHom_step_algebraicClosure_zmod p q A hA C m flag hqp i.castSucc

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_algHom_succ_eq_mul_natCard_algHom_hopfKer.CCountsN"

end S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_algHom_succ_eq_mul_natCard_algHom_hopfKer
end P2MW
export P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_natCard_algHom_succ_eq_mul_natCard_algHom_hopfKer (solution)
