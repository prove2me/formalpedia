-- Prove2me | solution 1 for ModularCurve.eigenformSupportAt_jZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b4425ea3-0e52-5b53-bc23-44a38d7fc76e

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_EigenformIdeal
import Theorems.Thm_ModularCurve_JZero_exists_abelJacobiCard
import Theorems.Thm_ModularCurve_eigenIdeal_isMaximal
import Theorems.Thm_ModularCurve_annihilator_torsionBy_jZero_le_of_isPrime
import Theorems.Thm_ModularCurve_aeval_heckeAlgebra_eq_zero_of_forall_smul_jZero_eq_zero
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eigenformSupportAt_jZero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve

namespace EigenformSupportJZero

section Support

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

private theorem exists_succ_eq {α : Type*} [PartialOrder α] [Finite α] (f : ℕ → α)
    (hf : ∀ n, f (n + 1) ≤ f n) : ∃ n, f (n + 1) = f n := by
  obtain ⟨i, j, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hanti : Antitone f := antitone_nat_of_succ_le hf
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨i, le_antisymm (hf i) (heq ▸ hanti (Nat.succ_le_of_lt h))⟩
  · exact ⟨j, le_antisymm (hf j) (heq.symm ▸ hanti (Nat.succ_le_of_lt h))⟩

private def chain (𝔪 : Ideal R) (P : Submodule R M) : ℕ → Submodule R M
  | 0 => P
  | j + 1 => 𝔪 • chain 𝔪 P j

private theorem chain_zero (𝔪 : Ideal R) (P : Submodule R M) : chain 𝔪 P 0 = P := rfl

private theorem chain_succ (𝔪 : Ideal R) (P : Submodule R M) (j : ℕ) :
    chain 𝔪 P (j + 1) = 𝔪 • chain 𝔪 P j := rfl

private theorem chain_succ_le (𝔪 : Ideal R) (P : Submodule R M) (j : ℕ) :
    chain 𝔪 P (j + 1) ≤ chain 𝔪 P j := by
  rw [chain_succ]; exact Submodule.smul_le_right

private theorem chain_le (𝔪 : Ideal R) (P : Submodule R M) : ∀ j, chain 𝔪 P j ≤ P
  | 0 => le_rfl
  | j + 1 => (chain_succ_le 𝔪 P j).trans (chain_le 𝔪 P j)

private theorem chain_mono (𝔪 : Ideal R) {P Q : Submodule R M} (h : P ≤ Q) :
    ∀ j, chain 𝔪 P j ≤ chain 𝔪 Q j
  | 0 => h
  | j + 1 => by rw [chain_succ, chain_succ]; exact Submodule.smul_mono le_rfl (chain_mono 𝔪 h j)

variable [Finite M]

private scoped instance : Finite (Submodule R M) :=
  Finite.of_injective (fun N : Submodule R M => (N : Set M)) SetLike.coe_injective

private theorem exists_ne_zero_forall_smul_eq_zero (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal)
    (hann : Module.annihilator R M ≤ 𝔪) : ∃ x : M, x ≠ 0 ∧ ∀ a ∈ 𝔪, a • x = 0 := by
  classical

  obtain ⟨k, hk⟩ := exists_succ_eq (chain 𝔪 (⊤ : Submodule R M)) (chain_succ_le 𝔪 ⊤)
  set N : Submodule R M := chain 𝔪 ⊤ k with hN

  obtain ⟨r, hr1, hrN⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 N
    (IsNoetherian.noetherian N) (by rw [hN, ← chain_succ, hk])

  let g : ℕ → Submodule R M := fun a => LinearMap.range ((r ^ a) • (LinearMap.id : M →ₗ[R] M))
  have hg_mem : ∀ a (y : M), y ∈ g a ↔ ∃ x : M, r ^ a • x = y := fun a y => by
    simp only [g, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]
  have hg_le : ∀ a, g (a + 1) ≤ g a := by
    intro a y hy
    obtain ⟨x, rfl⟩ := (hg_mem (a + 1) y).1 hy
    exact (hg_mem a _).2 ⟨r • x, by rw [pow_succ, mul_smul]⟩
  obtain ⟨a, ha⟩ := exists_succ_eq g hg_le
  set P : Submodule R M := g a with hP

  have hrP : ∀ y ∈ P, r • y ∈ P := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hg_mem a y).1 hy
    rw [← ha]
    exact (hg_mem (a + 1) _).2 ⟨x, by rw [pow_succ', mul_smul]⟩
  let ψ : P → P := fun y => ⟨r • (y : M), hrP y y.2⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ g (a + 1) := by rw [ha]; exact hz
    obtain ⟨x, rfl⟩ := (hg_mem (a + 1) z).1 hz'
    exact ⟨⟨r ^ a • x, (hg_mem a _).2 ⟨x, rfl⟩⟩, Subtype.ext (by
      show r • (r ^ a • x) = r ^ (a + 1) • x
      rw [pow_succ', mul_smul])⟩
  have hψi : Function.Injective ψ := Finite.injective_iff_surjective.2 hψs
  have hinj : ∀ y ∈ P, r • y = 0 → y = 0 := by
    intro y hy h0
    have h := @hψi ⟨y, hy⟩ ⟨0, P.zero_mem⟩ (Subtype.ext (by show r • y = r • (0 : M); rw [h0, smul_zero]))
    exact congrArg Subtype.val h

  have hkP : chain 𝔪 P k = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyN : y ∈ N := chain_mono 𝔪 (le_top : P ≤ ⊤) k hy
    exact (Submodule.mem_bot R).2 (hinj y (chain_le 𝔪 P k hy) (hrN y hyN))

  have hP0 : chain 𝔪 P 0 ≠ ⊥ := by
    rw [chain_zero]
    intro hbot
    have hra : r ^ a ∈ 𝔪 := by
      refine hann (Module.mem_annihilator.2 fun m => ?_)
      have hm : r ^ a • m ∈ P := (hg_mem a _).2 ⟨m, rfl⟩
      rw [hbot] at hm
      exact (Submodule.mem_bot R).1 hm
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow r 1 a
    have h1 : r ^ a - 1 ∈ 𝔪 := by
      rw [one_pow] at hc
      rw [hc]
      exact 𝔪.mul_mem_right c hr1
    have : (1 : R) ∈ 𝔪 := by
      have h := 𝔪.sub_mem hra h1
      rwa [sub_sub_cancel] at h
    exact h𝔪.ne_top ((Ideal.eq_top_iff_one 𝔪).2 this)

  have hex : ∃ j, chain 𝔪 P j = ⊥ := ⟨k, hkP⟩
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 :=
    Nat.exists_eq_succ_of_ne_zero (fun h0 => hP0 (h0 ▸ Nat.find_spec hex))
  have hjbot : chain 𝔪 P (j + 1) = ⊥ := hj ▸ Nat.find_spec hex
  have hjne : chain 𝔪 P j ≠ ⊥ := Nat.find_min hex (by rw [hj]; exact Nat.lt_succ_self j)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hjne
  refine ⟨x, hx0, fun m hm => ?_⟩
  have hmx : m • x ∈ chain 𝔪 P (j + 1) := by
    rw [chain_succ]; exact Submodule.smul_mem_smul hm hx
  rw [hjbot] at hmx
  exact (Submodule.mem_bot R).1 hmx

end Support

private theorem finite_torsionBy_jZero (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime) :
    letI := heckeModuleBar N
    Finite (Submodule.torsionBy HeckeAlg (JZero N) (p : HeckeAlg)) := by
  letI := heckeModuleBar N
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := JZero.exists_abelJacobiCard N
  have hcard : Nat.card (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ 1))
      = p ^ (2 * g * 1) := hg p 1
  haveI : Finite (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  let ι : Submodule.torsionBy HeckeAlg (JZero N) (p : HeckeAlg) →
      Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ 1) :=
    fun x => ⟨(x : JZero N), by
      have hx : (p : HeckeAlg) • (x : JZero N) = 0 := (Submodule.mem_torsionBy_iff _ _).1 x.2
      rw [Pic0.mem_torsion, pow_one, natCast_zsmul, ← Nat.cast_smul_eq_nsmul HeckeAlg]
      exact hx⟩
  refine Finite.of_injective ι fun x y h => Subtype.ext ?_
  have h' := congrArg Subtype.val h
  exact h'

private theorem annihilator_jZero_le_eigenIdeal (N : ℕ) [NeZero N]
    (hHI : HeckeInputsAll N) (hHC : HeckeOperatorsCommuteBar N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : f.IsNormalizedEigenform)
    (k : Type) [Field k] (𝒪 : Subring ℂ) (h𝒪 : ∀ ℓ : Nat.Primes, ModularFormClass.qCoeff f ℓ ∈ 𝒪)
    (φ : 𝒪 →+* k) :
    letI := heckeModuleBar N
    Module.annihilator HeckeAlg (JZero N) ≤ eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩) := by
  letI := heckeModuleBar N
  intro t ht
  rw [mem_eigenIdeal_iff]

  set g : Nat.Primes → CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) := fun ℓ : Nat.Primes =>
    if h : (ℓ : ℕ) ∣ N
      then (CuspForm.heckeAlgebra.U (S := (∅ : Set ℕ)) ℓ.prop h (Set.notMem_empty _) :
        CuspForm.heckeAlgebra N 2 (∅ : Set ℕ))
      else CuspForm.heckeAlgebra.T (S := (∅ : Set ℕ)) ℓ.prop h (Set.notMem_empty _) with hg

  have h0 : MvPolynomial.aeval (R := ℤ) g t = 0 :=
    aeval_heckeAlgebra_eq_zero_of_forall_smul_jZero_eq_zero N hHI hHC t (Module.mem_annihilator.1 ht)

  obtain ⟨χ, -, hχT, hχU⟩ := hf.exists_ringHom_heckeAlgebra (∅ : Set ℕ)
  have hgen : ∀ ℓ : Nat.Primes, χ (g ℓ) = ModularFormClass.qCoeff f ℓ := by
    intro ℓ
    rw [hg]
    by_cases h : (ℓ : ℕ) ∣ N
    · simp only [dif_pos h]; exact hχU ℓ ℓ.prop h (Set.notMem_empty _)
    · simp only [dif_neg h]; exact hχT ℓ ℓ.prop h (Set.notMem_empty _)

  have hC : MvPolynomial.aeval (R := ℤ) (fun ℓ : Nat.Primes => (ModularFormClass.qCoeff f ℓ : ℂ)) t = 0 := by
    have h := congrArg χ h0
    rw [map_zero, MvPolynomial.map_aeval, RingHom.ext_int (χ.comp (algebraMap ℤ _)) (algebraMap ℤ ℂ),
      MvPolynomial.coe_eval₂Hom, ← MvPolynomial.aeval_def] at h
    simp_rw [hgen] at h
    exact h

  have h𝒪 : MvPolynomial.aeval (R := ℤ)
      (fun ℓ : Nat.Primes => (⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩ : 𝒪)) t = 0 := by
    apply 𝒪.subtype_injective
    rw [map_zero, MvPolynomial.map_aeval, RingHom.ext_int (𝒪.subtype.comp (algebraMap ℤ _)) (algebraMap ℤ ℂ),
      MvPolynomial.coe_eval₂Hom, ← MvPolynomial.aeval_def]
    simp only [Subring.coe_subtype]
    exact hC

  have h := congrArg φ h𝒪
  rw [map_zero, MvPolynomial.map_aeval, RingHom.ext_int (φ.comp (algebraMap ℤ _)) (algebraMap ℤ k),
    MvPolynomial.coe_eval₂Hom, ← MvPolynomial.aeval_def] at h
  exact h

end EigenformSupportJZero
p2m_reactivate "P2MW.S_ModularCurve_eigenformSupportAt_jZero.EigenformSupportJZero"

end
p2m_reactivate "P2MW.S_ModularCurve_eigenformSupportAt_jZero.EigenformSupportJZero"

set_option maxHeartbeats 1600000 in
open ModularCurve EigenformSupportJZero in
theorem solution (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime) (hHI : ModularCurve.HeckeInputsAll N)
    (hHC : ModularCurve.HeckeOperatorsCommuteBar N) :
    letI := ModularCurve.heckeModuleBar N; ModularCurve.EigenformSupportAt N p (ModularCurve.JZero N) := by
  letI := heckeModuleBar N
  show ∀ 𝔪 : Ideal HeckeAlg, IsEigenformIdeal N 𝔪 → ((p : HeckeAlg)) ∈ 𝔪 → MTorsionNeBot HeckeAlg (JZero N) 𝔪
  intro 𝔪 h𝔪 hp𝔪
  obtain ⟨f, hf, k, _, _, 𝒪, h𝒪, φ, rfl⟩ := h𝔪
  have hmax := eigenIdeal_isMaximal (fun ℓ => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩)
  have hann := annihilator_jZero_le_eigenIdeal N hHI hHC f hf k 𝒪 h𝒪 φ
  have hannp := annihilator_torsionBy_jZero_le_of_isPrime N p hp hHI hHC _ hmax.isPrime hann hp𝔪
  haveI := finite_torsionBy_jZero N p hp
  obtain ⟨x, hx0, hx𝔪⟩ := exists_ne_zero_forall_smul_eq_zero
    (M := Submodule.torsionBy HeckeAlg (JZero N) (p : HeckeAlg)) _ hmax hannp
  show Submodule.torsionBySet HeckeAlg (JZero N) _ ≠ ⊥
  rw [Submodule.ne_bot_iff]
  refine ⟨(x : JZero N), (Submodule.mem_torsionBySet_iff _ _).2 fun a => ?_,
    fun h => hx0 (Subtype.ext h)⟩
  have h := congrArg Subtype.val (hx𝔪 a a.2)
  simpa using h

#print axioms solution

end S_ModularCurve_eigenformSupportAt_jZero
end P2MW
export P2MW.S_ModularCurve_eigenformSupportAt_jZero (solution)
