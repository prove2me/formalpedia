-- Prove2me | solution 1 for ModularCurve.finite_setOf_heckeGen_sub_smul_eq_zero_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/634575a3-96d4-5365-92ab-5a75d0537978

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_ModularCurve_JZeroTorsionFinite
import Theorems.Thm_ModularCurve_freeAlgebra_lift_heckeOperatorBar_eq_zero_of_lift_cuspForm_eq_zero
import Theorems.Thm_CuspForm_norm_lt_of_heckeTLin_eq_smul
import Theorems.Thm_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast
import Theorems.Thm_ModularCurve_jZeroTorsionFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finite_setOf_heckeGen_sub_smul_eq_zero_of_not_dvd
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int"
p2m_attr_erase "instance" "ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

namespace HeckeIsogeny

open Polynomial

section LinearAlgebra

theorem aeval_int_eq_aeval_map {A : Type*} [Ring A] [Algebra ℂ A] [Algebra ℤ A] (x : A)
    (P : ℤ[X]) : aeval x P = aeval x (P.map (algebraMap ℤ ℂ)) := by
  rw [aeval_def, aeval_def, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem exists_intPoly_aeval_eq_zero_eval_ne_zero {n : ℕ} (b : Module.Basis (Fin n) ℂ V)
    (T : V →ₗ[ℂ] V) (hrat : ∀ i j, b.repr (T (b i)) j ∈ Set.range ((↑) : ℚ → ℂ))
    (a : ℤ) (ha : ∀ v : V, T v = (a : ℂ) • v → v = 0) :
    ∃ P : ℤ[X], aeval T (P.map (algebraMap ℤ ℂ)) = 0 ∧ P.eval a ≠ 0 := by
  classical
  haveI : Module.Finite ℂ V := Module.Finite.of_basis b
  haveI : Module.Free ℂ V := Module.Free.of_basis b

  choose q hq using hrat
  let A₀ : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => q j i
  have hA : A₀.map (algebraMap ℚ ℂ) = LinearMap.toMatrix b b T := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply]
    exact hq j i

  have hchar : T.charpoly = A₀.charpoly.map (algebraMap ℚ ℂ) := by
    rw [← LinearMap.charpoly_toMatrix T b, ← hA, Matrix.charpoly_map]

  have hroot : ¬ T.charpoly.IsRoot (a : ℂ) := by
    intro h
    rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly] at h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact hv.2 (ha v hv.apply_eq_smul)
  have hroot₀ : A₀.charpoly.eval (a : ℚ) ≠ 0 := by
    intro h0
    apply hroot
    have hcast : ((a : ℤ) : ℂ) = algebraMap ℚ ℂ (a : ℚ) := (map_intCast (algebraMap ℚ ℂ) a).symm
    rw [IsRoot.def, hchar, hcast, eval_map, eval₂_hom, h0, map_zero]

  obtain ⟨c, hc, hcP⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) A₀.charpoly
  set P : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) A₀.charpoly with hPdef
  have hc0 : (c : ℚ) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hc)
  have hcP' : P.map (algebraMap ℤ ℚ) = C (c : ℚ) * A₀.charpoly := by
    rw [hcP]
    ext k
    simp [Polynomial.coeff_smul, zsmul_eq_mul]
  refine ⟨P, ?_, ?_⟩
  · have h1 : algebraMap ℤ ℂ = (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) := RingHom.ext_int _ _
    rw [h1, ← Polynomial.map_map, hcP', Polynomial.map_mul, Polynomial.map_C, ← hchar, map_mul,
      LinearMap.aeval_self_charpoly, mul_zero]
  · intro h0
    have h1 : algebraMap ℤ ℚ (P.eval a) = (c : ℚ) * A₀.charpoly.eval (a : ℚ) := by
      rw [← eval₂_hom, ← eval_map, hcP', eval_mul, eval_C, eq_intCast]
    rw [h0, map_zero] at h1
    exact mul_ne_zero hc0 hroot₀ h1.symm

end LinearAlgebra

theorem eval_smul_eq_zero_of_aeval_eq_zero {M : Type*} [AddCommGroup M] (H : Module.End ℤ M)
    (P : ℤ[X]) (hP : aeval H P = 0) (a : ℤ) (x : M) (hx : H x = a • x) : P.eval a • x = 0 := by
  have hdiv : P = C (P.eval a) + (P /ₘ (X - C a)) * (X - C a) := by
    conv_lhs => rw [← modByMonic_add_div P (X - C a), modByMonic_X_sub_C_eq_C_eval]
    rw [mul_comm]
  have h := congrArg (fun F : Module.End ℤ M => F x) hP
  beta_reduce at h
  rw [hdiv, map_add, map_mul, aeval_C, map_sub, aeval_X, aeval_C, LinearMap.zero_apply,
    LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
    Module.algebraMap_end_apply, hx, sub_self, map_zero, add_zero] at h
  exact h

open ModularCurve in

theorem finite_setOf_zsmul_eq_zero (N : ℕ) [NeZero N] (m : ℤ) (hm : m ≠ 0) :
    {x : JZero N | m • x = 0}.Finite := by
  have hfin := ModularCurve.jZeroTorsionFinite N m.natAbs (Int.natAbs_pos.2 hm)
  unfold ModularCurve.JZeroTorsionFinite at hfin
  have hsub : {x : JZero N | m • x = 0} ⊆
      ((AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) m.natAbs :
        AddSubgroup (JZero N)) : Set (JZero N)) := by
    intro x hx
    rw [Set.mem_setOf_eq] at hx
    rw [SetLike.mem_coe, AlgebraicCurve.Pic0.mem_torsion]
    rcases Int.natAbs_eq m with h | h
    · rw [← h, hx]
    · have h' : (m.natAbs : ℤ) = -m := by omega
      rw [h', neg_smul, hx, neg_zero]
  exact (Set.toFinite _).subset hsub

theorem exists_intPoly_aeval_heckeTLin_eq_zero (N : ℕ) [NeZero N] (ℓ : Nat.Primes)
    (hℓN : ¬ (ℓ : ℕ) ∣ N) :
    ∃ P : ℤ[X], aeval (CuspForm.heckeTLin (N := N) 2 ℓ.2 hℓN) P = 0 ∧
      P.eval (((ℓ : ℕ) : ℤ) + 1) ≠ 0 := by
  obtain ⟨n, b, hT, -⟩ := CuspForm.exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast N
  have ha : ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      CuspForm.heckeTLin 2 ℓ.2 hℓN f = (((((ℓ : ℕ) : ℤ) + 1 : ℤ)) : ℂ) • f → f = 0 := by
    intro f hf
    by_contra hf0
    have hlt := CuspForm.norm_lt_of_heckeTLin_eq_smul hf0 ℓ.2 hℓN hf
    have hnorm : ‖(((((ℓ : ℕ) : ℤ) + 1 : ℤ)) : ℂ)‖ = (ℓ : ℕ) + 1 := by
      rw [show (((((ℓ : ℕ) : ℤ) + 1 : ℤ)) : ℂ) = (((ℓ : ℕ) + 1 : ℕ) : ℂ) by push_cast; ring,
        Complex.norm_natCast]
      push_cast
      ring
    rw [hnorm] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨P, hP, hPa⟩ :=
    exists_intPoly_aeval_eq_zero_eval_ne_zero b (CuspForm.heckeTLin 2 ℓ.2 hℓN)
      (fun i j => hT ℓ ℓ.2 hℓN i j) _ ha
  exact ⟨P, by rw [aeval_int_eq_aeval_map, hP], hPa⟩

open ModularCurve

theorem aeval_heckeOperatorBar_eq_zero (N : ℕ) [NeZero N] (ℓ : Nat.Primes) (hℓN : ¬ (ℓ : ℕ) ∣ N)
    (P : ℤ[X]) (hP : aeval (CuspForm.heckeTLin (N := N) 2 ℓ.2 hℓN) P = 0) :
    aeval (heckeOperatorBar N ℓ) P = 0 := by
  have h := ModularCurve.freeAlgebra_lift_heckeOperatorBar_eq_zero_of_lift_cuspForm_eq_zero N
    (aeval (FreeAlgebra.ι ℤ ℓ) P) (by
      rw [← aeval_algHom_apply, FreeAlgebra.lift_ι_apply]
      simp only [dif_neg hℓN]
      exact hP)
  rwa [← aeval_algHom_apply, FreeAlgebra.lift_ι_apply] at h

theorem finite_setOf_heckeGen_sub_smul_eq_zero (N : ℕ) [NeZero N] (ℓ : Nat.Primes)
    (hℓN : ¬ (ℓ : ℕ) ∣ N) :
    letI := heckeModuleBar N
    {x : JZero N | (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • x = 0}.Finite := by
  letI : Module HeckeAlg (JZero N) := heckeModuleBar N
  show {x : JZero N | (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • x = 0}.Finite
  have hC : ∀ (a : ℤ) (y : JZero N), (MvPolynomial.C a : HeckeAlg) • y = a • y :=
    fun a y => heckeModuleBar_C_smul a y
  by_cases hcomm : HeckeOperatorsCommuteBar N
  ·
    have hgen : ∀ y : JZero N, heckeGen ℓ • y = heckeOperatorBar N ℓ y :=
      fun y => heckeModuleBar_heckeGen_smul hcomm ℓ y
    obtain ⟨P, hP, hPa⟩ := exists_intPoly_aeval_heckeTLin_eq_zero N ℓ hℓN
    have hJ := aeval_heckeOperatorBar_eq_zero N ℓ hℓN P hP
    refine (finite_setOf_zsmul_eq_zero N _ hPa).subset ?_
    intro x hx
    rw [Set.mem_setOf_eq, sub_smul, hgen, hC, sub_eq_zero] at hx
    exact eval_smul_eq_zero_of_aeval_eq_zero (heckeOperatorBar N ℓ) P hJ _ x hx
  ·
    have hgen : ∀ y : JZero N, heckeGen ℓ • y = 0 :=
      fun y => heckeModuleBar_heckeGen_smul_of_not hcomm ℓ y
    have hne : -((((ℓ : ℕ) : ℤ) + 1)) ≠ 0 := by
      have : (0 : ℤ) < ((ℓ : ℕ) : ℤ) + 1 := by positivity
      omega
    refine (finite_setOf_zsmul_eq_zero N _ hne).subset ?_
    intro x hx
    rw [Set.mem_setOf_eq, sub_smul, hgen, hC, zero_sub] at hx
    rw [Set.mem_setOf_eq, neg_smul]
    exact hx

end HeckeIsogeny

open ModularCurve

theorem solution
    (N : ℕ) [NeZero N] (ℓ : Nat.Primes) (hℓN : ¬ (ℓ : ℕ) ∣ N) :
    letI := heckeModuleBar N
    {x : JZero N | (heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1)) • x = 0}.Finite :=
  HeckeIsogeny.finite_setOf_heckeGen_sub_smul_eq_zero N ℓ hℓN

end S_ModularCurve_finite_setOf_heckeGen_sub_smul_eq_zero_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_finite_setOf_heckeGen_sub_smul_eq_zero_of_not_dvd (solution)
