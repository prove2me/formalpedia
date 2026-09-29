-- Prove2me | solution 1 for ModularCurve.goodEigensystemOccursAt_of_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cc80c9c8-18d9-5a66-aa32-5878259c1d07

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_ModularCurve_exists_ringHom_heckeAlgebra_heckeOperatorBar
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul
import Theorems.Thm_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_goodEigensystemOccursAt_of_divisible
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open CongruenceSubgroup

section Core

variable {σ : Type*} {A : Type*} [CommRing A] [IsDomain A] {M : Type*} [AddCommGroup M]

private def h2KillIdeal (act : MvPolynomial σ ℤ →+* Module.End ℤ M) (D : AddSubgroup M) :
    Ideal (MvPolynomial σ ℤ) where
  carrier := {t | ∀ y ∈ D, act t y = 0}
  zero_mem' := by
    intro y _
    rw [map_zero, LinearMap.zero_apply]
  add_mem' := by
    intro s t hs ht y hy
    rw [map_add, LinearMap.add_apply, hs y hy, ht y hy, add_zero]
  smul_mem' := by
    intro s t ht y hy
    rw [smul_eq_mul, map_mul, Module.End.mul_apply, ht y hy, map_zero]

private theorem mem_h2KillIdeal {act : MvPolynomial σ ℤ →+* Module.End ℤ M} {D : AddSubgroup M}
    {t : MvPolynomial σ ℤ} : t ∈ h2KillIdeal act D ↔ ∀ y ∈ D, act t y = 0 :=
  Iff.rfl

private theorem h2_core (α : MvPolynomial σ ℤ →ₐ[ℤ] A)
    (hint : ∀ i : σ, IsIntegral ℤ (α (MvPolynomial.X i)))
    (act : MvPolynomial σ ℤ →+* Module.End ℤ M) (D : AddSubgroup M) (hD : D ≠ ⊥)
    (hdiv : ∀ y ∈ D, ∀ n : ℕ, 0 < n → ∃ z ∈ D, n • z = y)
    (hkill : ∀ t : MvPolynomial σ ℤ, α t = 0 → ∀ y ∈ D, act t y = 0)
    (t₀ : MvPolynomial σ ℤ) (ht₀ : ∀ y ∈ D, act t₀ y = 0) : α t₀ = 0 := by
  classical

  have hαint : ∀ t : MvPolynomial σ ℤ, IsIntegral ℤ (α t) := by
    intro t
    induction t using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      exact isIntegral_algebraMap
    | add p q hp hq =>
      rw [map_add]
      exact hp.add hq
    | mul_X p i hp =>
      rw [map_mul]
      exact hp.mul (hint i)

  have hsat : ∀ (k : ℕ) (t : MvPolynomial σ ℤ), 0 < k →
      (k : MvPolynomial σ ℤ) * t ∈ h2KillIdeal act D → t ∈ h2KillIdeal act D := by
    intro k t hk h
    rw [mem_h2KillIdeal] at h ⊢
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hdiv y hy k hk
    have h1 := h z hz
    rw [map_mul, map_natCast, Module.End.mul_apply, Module.End.natCast_apply] at h1
    rw [map_nsmul]
    exact h1

  have hker : ∀ t : MvPolynomial σ ℤ, α t = 0 → t ∈ h2KillIdeal act D :=
    fun t ht => mem_h2KillIdeal.mpr (hkill t ht)

  have key : ∀ k : ℕ, 0 < k → (k : MvPolynomial σ ℤ) ∈ h2KillIdeal act D → False := by
    intro k hk hkmem
    have h1 : (1 : MvPolynomial σ ℤ) ∈ h2KillIdeal act D := hsat k 1 hk (by rwa [mul_one])
    apply hD
    rw [eq_bot_iff]
    intro y hy
    have h2 := (mem_h2KillIdeal.mp h1) y hy
    rw [map_one, Module.End.one_apply] at h2
    rw [AddSubgroup.mem_bot]
    exact h2
  by_contra hne
  have ht₀mem : t₀ ∈ h2KillIdeal act D := mem_h2KillIdeal.mpr ht₀

  have hx_mem : α.rangeRestrict t₀ ∈ Ideal.map α.rangeRestrict (h2KillIdeal act D) :=
    Ideal.mem_map_of_mem _ ht₀mem
  have hx_ne : α.rangeRestrict t₀ ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg Subtype.val h
    exact h'
  have hx_int : IsIntegral ℤ (α.rangeRestrict t₀) := by
    rw [← isIntegral_algHom_iff α.range.val Subtype.val_injective]
    exact hαint t₀
  have hJ : (Ideal.map α.rangeRestrict (h2KillIdeal act D)).comap (algebraMap ℤ ↥α.range) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx_ne hx_mem hx_int
  obtain ⟨n, hnJ, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  rw [Ideal.mem_comap, eq_intCast] at hnJ
  obtain ⟨s, hs, hsn⟩ := (Ideal.mem_map_iff_of_surjective _ α.rangeRestrict_surjective).mp hnJ

  have hαs : α s = (n : A) := by
    have h1 := congrArg Subtype.val hsn
    have h2 : ((n : ↥α.range) : A) = (n : A) := map_intCast α.range.val n
    exact h1.trans h2
  have hsub : s - (n : MvPolynomial σ ℤ) ∈ h2KillIdeal act D := by
    apply hker
    rw [map_sub, map_intCast, hαs, sub_self]
  have hnmem : (n : MvPolynomial σ ℤ) ∈ h2KillIdeal act D := by
    have h3 := (h2KillIdeal act D).sub_mem hs hsub
    rwa [sub_sub_cancel] at h3

  obtain ⟨k, rfl | rfl⟩ : ∃ k : ℕ, n = k ∨ n = -k := ⟨n.natAbs, Int.natAbs_eq n⟩
  · exact key k (by omega) (by rwa [Int.cast_natCast] at hnmem)
  · refine key k (by omega) ?_
    rw [Int.cast_neg, Int.cast_natCast] at hnmem
    exact neg_mem_iff.mp hnmem

end Core

section Players

private abbrev h2Bad (N₀ p : ℕ) : Set ℕ := {n : ℕ | n ∣ N₀ * p}

private abbrev h2Good (N₀ p : ℕ) : Set Nat.Primes := {ℓ : Nat.Primes | ¬ (ℓ : ℕ) ∣ N₀ * p}

private theorem h2Good_not_dvd {N₀ p : ℕ} (i : h2Good N₀ p) : ¬ ((i.1 : ℕ) ∣ N₀) :=
  fun h => i.2 (h.mul_right p)

variable (N₀ p : ℕ) [NeZero N₀]

private def h2gen (i : h2Good N₀ p) : CuspForm.heckeAlgebra N₀ 2 (h2Bad N₀ p) :=
  CuspForm.heckeAlgebra.T (N := N₀) (k := 2) (S := h2Bad N₀ p) i.1.2 (h2Good_not_dvd i) i.2

private def h2γ : MvPolynomial (h2Good N₀ p) ℤ →ₐ[ℤ] CuspForm.heckeAlgebra N₀ 2 (h2Bad N₀ p) :=
  MvPolynomial.aeval (h2gen N₀ p)

private def h2α {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    MvPolynomial (h2Good N₀ p) ℤ →ₐ[ℤ] ℂ :=
  MvPolynomial.aeval fun i : h2Good N₀ p => (ModularFormClass.qCoeff f (i.1 : ℕ) : ℂ)

private def h2act (hcomm : ModularCurve.HeckeOperatorsCommuteBar N₀) :
    MvPolynomial (h2Good N₀ p) ℤ →+* Module.End ℤ (ModularCurve.JZero N₀) :=
  (ModularCurve.heckeEvalBar hcomm).comp
    (MvPolynomial.rename (Subtype.val : h2Good N₀ p → Nat.Primes)).toRingHom

variable {N₀ p}

private theorem h2γ_X (i : h2Good N₀ p) : h2γ N₀ p (MvPolynomial.X i) = h2gen N₀ p i :=
  MvPolynomial.aeval_X _ _

private theorem h2γ_C (r : ℤ) : h2γ N₀ p (MvPolynomial.C r) = algebraMap ℤ _ r :=
  MvPolynomial.aeval_C _ _

private theorem coe_h2γ_X (i : h2Good N₀ p) :
    ((h2γ N₀ p (MvPolynomial.X i) : CuspForm.heckeAlgebra N₀ 2 (h2Bad N₀ p)) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N₀) 2)) =
      CuspForm.heckeTLin 2 i.1.2 (h2Good_not_dvd i) := by
  rw [h2γ_X]
  rfl

omit [NeZero N₀] in
private theorem h2α_X {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (i : h2Good N₀ p) :
    h2α N₀ p f (MvPolynomial.X i) = ModularFormClass.qCoeff f (i.1 : ℕ) :=
  MvPolynomial.aeval_X _ _

private theorem h2act_X (hcomm : ModularCurve.HeckeOperatorsCommuteBar N₀) (i : h2Good N₀ p) :
    h2act N₀ p hcomm (MvPolynomial.X i) = ModularCurve.heckeOperatorBar N₀ i.1 := by
  show ModularCurve.heckeEvalBar hcomm
      (MvPolynomial.rename (Subtype.val : h2Good N₀ p → Nat.Primes) (MvPolynomial.X i)) = _
  rw [MvPolynomial.rename_X]
  exact ModularCurve.heckeEvalBar_heckeGen hcomm i.1

end Players

section WallD

private lemma h2_wallD
    (N₀ p : ℕ) [NeZero N₀] [NeZero p]
    (hin : ModularCurve.HeckeInputsAll N₀) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N₀)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (N₀ * p)) 2) (hf : f.IsNormalizedEigenform)
    (D : AddSubgroup (ModularCurve.JZero N₀)) (hD : D ≠ ⊥)
    (hdiv : ∀ y ∈ D, ∀ n : ℕ, 0 < n → ∃ z ∈ D, n • z = y)
    (hkill : ∀ t ∈ ModularCurve.eigenIdeal (fun ℓ : Nat.Primes => ModularFormClass.qCoeff f ℓ),
      t ∈ MvPolynomial.supported ℤ {ℓ : Nat.Primes | ¬ (ℓ : ℕ) ∣ N₀ * p} →
      ∀ y ∈ D, (letI := ModularCurve.heckeModuleBar N₀; t • y) = 0) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N₀) 2, g ≠ 0 ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN₀ : ¬ ℓ ∣ N₀), ¬ ℓ ∣ p →
        CuspForm.heckeTLin 2 hℓ hℓN₀ g = ModularFormClass.qCoeff f ℓ • g := by
  have _ := hin
  classical

  obtain ⟨Φ, hΦT, -⟩ := ModularCurve.exists_ringHom_heckeAlgebra_heckeOperatorBar N₀
  let ι : CuspForm.heckeAlgebra N₀ 2 (h2Bad N₀ p) →ₐ[ℤ] CuspForm.heckeAlgebra N₀ 2 (∅ : Set ℕ) :=
    Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (N := N₀) (k := 2) (Set.empty_subset _))

  have hact : ∀ t : MvPolynomial (h2Good N₀ p) ℤ, h2act N₀ p hcomm t = Φ (ι (h2γ N₀ p t)) := by
    have key : (h2act N₀ p hcomm).toIntAlgHom =
        (Φ.comp (ι.comp (h2γ N₀ p)).toRingHom).toIntAlgHom := by
      apply MvPolynomial.algHom_ext
      intro i
      show h2act N₀ p hcomm (MvPolynomial.X i) = Φ (ι (h2γ N₀ p (MvPolynomial.X i)))
      rw [h2act_X, h2γ_X]
      have e : ι (h2gen N₀ p i) = CuspForm.heckeAlgebra.T (N := N₀) (k := 2) (S := (∅ : Set ℕ))
          i.1.2 (h2Good_not_dvd i) (Set.notMem_empty _) := Subtype.ext rfl
      rw [e, hΦT i.1 (h2Good_not_dvd i) (Set.notMem_empty _)]
    intro t
    exact DFunLike.congr_fun key t

  have hkill' : ∀ t : MvPolynomial (h2Good N₀ p) ℤ, h2α N₀ p f t = 0 →
      ∀ y ∈ D, h2act N₀ p hcomm t y = 0 := by
    intro t ht y hy
    have hmem : MvPolynomial.rename (Subtype.val : h2Good N₀ p → Nat.Primes) t ∈
        ModularCurve.eigenIdeal (fun ℓ : Nat.Primes => ModularFormClass.qCoeff f ℓ) := by
      rw [ModularCurve.mem_eigenIdeal_iff, MvPolynomial.aeval_rename]
      exact ht
    have hsupp : MvPolynomial.rename (Subtype.val : h2Good N₀ p → Nat.Primes) t ∈
        MvPolynomial.supported ℤ {ℓ : Nat.Primes | ¬ (ℓ : ℕ) ∣ N₀ * p} := by
      rw [MvPolynomial.supported_eq_range_rename]
      exact ⟨t, rfl⟩
    have h := hkill _ hmem hsupp y hy
    rw [ModularCurve.heckeModuleBar_smul_def hcomm] at h
    exact h

  have hint : ∀ i : h2Good N₀ p, IsIntegral ℤ (h2α N₀ p f (MvPolynomial.X i)) := by
    intro i
    obtain ⟨a, ha⟩ := (CuspForm.IsNormalizedEigenform.primeCoeffsIntegral_of_neZero hf) i.1
    rw [h2α_X, ← ha]
    exact a.2

  have hcore : ∀ t : MvPolynomial (h2Good N₀ p) ℤ,
      (∀ y ∈ D, h2act N₀ p hcomm t y = 0) → h2α N₀ p f t = 0 :=
    fun t ht => h2_core (h2α N₀ p f) hint (h2act N₀ p hcomm) D hD hdiv hkill' t ht

  have hle : RingHom.ker (h2γ N₀ p).toRingHom ≤ RingHom.ker (h2α N₀ p f).toRingHom := by
    intro t ht
    rw [RingHom.mem_ker] at ht ⊢
    refine hcore t fun y _ => ?_
    rw [hact t, show h2γ N₀ p t = 0 from ht, map_zero, map_zero, LinearMap.zero_apply]

  have hsurj : Function.Surjective (h2γ N₀ p).toRingHom := by
    rintro ⟨u, hu⟩
    suffices h : ∃ t : MvPolynomial (h2Good N₀ p) ℤ,
        ((h2γ N₀ p t : CuspForm.heckeAlgebra N₀ 2 (h2Bad N₀ p)) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N₀) 2)) = u by
      obtain ⟨t, ht⟩ := h
      exact ⟨t, Subtype.ext ht⟩
    refine Algebra.adjoin_induction (p := fun x _ => ∃ t : MvPolynomial (h2Good N₀ p) ℤ,
        ((h2γ N₀ p t : CuspForm.heckeAlgebra N₀ 2 (h2Bad N₀ p)) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N₀) 2)) = x) ?_ ?_ ?_ ?_ hu
    · rintro x (⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, -, hqS, rfl⟩)
      · exact ⟨MvPolynomial.X ⟨⟨ℓ, hℓ⟩, hℓS⟩, coe_h2γ_X _⟩
      · exact absurd (hqN.trans (dvd_mul_right N₀ p)) hqS
    · intro r
      refine ⟨MvPolynomial.C r, ?_⟩
      rw [h2γ_C]
      rfl
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a + b, by rw [map_add, Subalgebra.coe_add, ha, hb]⟩
    · rintro x y - - ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a * b, by rw [map_mul, Subalgebra.coe_mul, ha, hb]⟩

  let χ : CuspForm.heckeAlgebra N₀ 2 (h2Bad N₀ p) →+* ℂ :=
    ((h2γ N₀ p).toRingHom.liftOfSurjective hsurj) ⟨(h2α N₀ p f).toRingHom, hle⟩
  have hχ : ∀ t : MvPolynomial (h2Good N₀ p) ℤ, χ (h2γ N₀ p t) = h2α N₀ p f t := fun t =>
    RingHom.liftOfSurjective_comp_apply (h2γ N₀ p).toRingHom hsurj
      ⟨(h2α N₀ p f).toRingHom, hle⟩ t

  obtain ⟨g, hg0, hgeig⟩ := CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul
    (CuspForm.hasIntegralStructure_two N₀) (by norm_num) χ
  refine ⟨g, hg0, fun ℓ hℓ hℓN₀ hℓp => ?_⟩
  have hℓNp : ¬ ℓ ∣ N₀ * p := fun h => ((Nat.Prime.dvd_mul hℓ).mp h).elim hℓN₀ hℓp
  have h1 := hgeig (h2γ N₀ p (MvPolynomial.X ⟨⟨ℓ, hℓ⟩, hℓNp⟩))
  rw [coe_h2γ_X, hχ, h2α_X] at h1
  exact h1

end WallD

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [NeZero p]
    (hin : ModularCurve.HeckeInputsAll N₀) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N₀)
    (f : CuspForm (CongruenceSubgroup.Gamma0 (N₀ * p)) 2) (hf : f.IsNormalizedEigenform)
    (D : AddSubgroup (ModularCurve.JZero N₀)) (hD : D ≠ ⊥)
    (hdiv : ∀ y ∈ D, ∀ n : ℕ, 0 < n → ∃ z ∈ D, n • z = y)
    (hkill : ∀ t ∈ ModularCurve.eigenIdeal (fun ℓ : Nat.Primes => ModularFormClass.qCoeff f ℓ),
      t ∈ MvPolynomial.supported ℤ {ℓ : Nat.Primes | ¬ (ℓ : ℕ) ∣ N₀ * p} →
      ∀ y ∈ D, (letI := ModularCurve.heckeModuleBar N₀; t • y) = 0) :
    f.GoodEigensystemOccursAt N₀ := by
  obtain ⟨g, hg0, hT⟩ := h2_wallD N₀ p hin hcomm f hf D hD hdiv hkill
  obtain ⟨h, hh, hq⟩ := CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul hg0
    (fun ℓ => ModularFormClass.qCoeff f ℓ) {q : ℕ | q ∣ p}
    (fun ℓ hℓ hℓN₀ hℓS => hT ℓ hℓ hℓN₀ hℓS)
  refine ⟨h, hh, fun ℓ hℓ hℓN => ?_⟩
  have hℓN₀ : ¬ ℓ ∣ N₀ := fun hd => hℓN (hd.mul_right p)
  have hℓS : ℓ ∉ {q : ℕ | q ∣ p} := fun hd => hℓN (hd.mul_left N₀)
  exact hq ℓ hℓ hℓN₀ hℓS

end

end S_ModularCurve_goodEigensystemOccursAt_of_divisible
end P2MW
export P2MW.S_ModularCurve_goodEigensystemOccursAt_of_divisible (solution)
