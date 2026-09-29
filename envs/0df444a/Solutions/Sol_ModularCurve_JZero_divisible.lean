-- Prove2me | solution 1 for ModularCurve.JZero.divisible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/5c64e6e8-3631-52f0-a541-dc6a5a465670

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeOperatorTotal
import Definitions.Def_ModularCurve_PeriodLattice
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_divisible
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_JZero_divisible.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "JZero modularFunctionFieldFull coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff HeckeInputsAlong periodLattice exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice heckeInputsAlong_of_prime periodLatticeHeckeStable exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull transcendental_coeffEmb_jq finiteDimensional_adjoin_coeffEmb_jq_full"
namespace JZeroDivisible
p2m_open "ModularCurve"

local notation "Qb" => AlgebraicClosure ℚ

local notation "FQ" M:max => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)

local notation "FC" M:max => laurentBaseChange ℂ (modularFunctionFieldFull M)

def sigma : Qb →ₐ[ℚ] ℂ :=
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  IsAlgClosed.lift

def sigmaR : Qb →+* ℂ := (sigma : Qb →ₐ[ℚ] ℂ).toRingHom

theorem sigmaR_comp_algebraMap : sigmaR.comp (algebraMap ℚ Qb) = algebraMap ℚ ℂ :=
  sigma.comp_algebraMap

theorem coeffMap_sigma_algebraMap (a : Qb) :
    coeffMap sigmaR (algebraMap Qb (LaurentSeries Qb) a) =
      algebraMap ℂ (LaurentSeries ℂ) (sigmaR a) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_sigma_coeffEmb (z : LaurentSeries ℚ) :
    coeffMap sigmaR (coeffEmb Qb z) = coeffEmb ℂ z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr sigmaR_comp_algebraMap z

section Level

variable (M : ℕ) [NeZero M]

omit [NeZero M] in
theorem coeffMap_sigma_mem {x : LaurentSeries Qb} (hx : x ∈ FQ M) :
    coeffMap sigmaR x ∈ FC M := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_sigma_algebraMap]
        exact (laurentBaseChange ℂ _).algebraMap_mem _
      · rw [coeffMap_sigma_coeffEmb]
        exact coeffEmb_mem_laurentBaseChange ℂ hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

def phi : (FQ M) →+* (FC M) where
  toFun x := ⟨coeffMap sigmaR (x : LaurentSeries Qb), coeffMap_sigma_mem M x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem phi_algebraMap (a : Qb) :
    phi M (algebraMap Qb (FQ M) a) = algebraMap ℂ (FC M) (sigmaR a) :=
  Subtype.ext (coeffMap_sigma_algebraMap a)

@[reducible] def algQbC : Algebra Qb ℂ := sigmaR.toAlgebra

@[reducible] def algF : Algebra (FQ M) (FC M) := (phi M).toAlgebra

@[reducible] def algQbFC : Algebra Qb (FC M) := ((algebraMap ℂ (FC M)).comp sigmaR).toAlgebra

attribute [local instance] algQbC algF algQbFC

theorem isScalarTower_Qb_C_FC : IsScalarTower Qb ℂ (FC M) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isScalarTower_Qb_FQ_FC : IsScalarTower Qb (FQ M) (FC M) :=
  IsScalarTower.of_algebraMap_eq fun a => (phi_algebraMap M a).symm

attribute [local instance] isScalarTower_Qb_C_FC isScalarTower_Qb_FQ_FC

theorem hfgQ : ∃ x : FQ M, Transcendental Qb x ∧
    FiniteDimensional (IntermediateField.adjoin Qb ({x} : Set (FQ M))) (FQ M) :=
  ModularCurve.exists_transcendental_finiteDimensional_modularFunctionFieldBar M

theorem hfgC : ∃ x : FC M, Transcendental ℂ x ∧
    FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set (FC M))) (FC M) :=
  ⟨_, ModularCurve.transcendental_coeffEmb_jq ℂ M,
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full ℂ M⟩

theorem isCurveOverQ : IsCurveOver Qb (FQ M) := ModularCurve.isCurveOver_modularFunctionFieldBar M

theorem isCurveOverC : IsCurveOver ℂ (FC M) :=
  ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull ℂ M

attribute [local instance] isCurveOverQ isCurveOverC

theorem adjoin_range_algebraMap :
    IntermediateField.adjoin ℂ (Set.range (algebraMap (FQ M) (FC M))) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hle : (FC M) ≤ IntermediateField.lift (IntermediateField.adjoin ℂ (Set.range (phi M))) := by
    rw [IntermediateField.lift_adjoin]
    change IntermediateField.adjoin ℂ _ ≤ _
    refine IntermediateField.adjoin.mono ℂ _ _ ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨phi M ⟨coeffEmb Qb z, coeffEmb_mem_laurentBaseChange _ hz⟩, ⟨_, rfl⟩,
      coeffMap_sigma_coeffEmb z⟩
  exact (IntermediateField.mem_lift y).1 (hle y.2)

end Level

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum [IsAlgClosed K] [IsCurveOver K F] (D : Divisor K F) :
    Divisor.degree D = D.sum fun _ n => n := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply, IsCurveOver.deg_eq_one_of_isAlgClosed,
    Nat.cast_one]
  refine Finsupp.sum_congr fun v _ => ?_
  simp

theorem mk_eq_zero_iff (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = 0 ↔ (D : Divisor K F).IsPrincipal := by
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]

theorem exists_nsmul_eq_mk_of_dvd [HasPrincipalDivisors K F] (m : ℕ) (hm : m ≠ 0)
    (D : Divisor.degZero (K := K) (F := F))
    (h : ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, (m : ℤ) ∣ v.ord f - (D : Divisor K F) v) :
    ∃ y : Pic0 K F, m • y = Pic0.mk D := by
  obtain ⟨f, hf, hdvd⟩ := h
  obtain ⟨E, hE, hE0⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf

  set G : Divisor K F := (D : Divisor K F) - E with hG
  have hGdvd : ∀ v, (m : ℤ) ∣ G v := fun v => by
    rw [hG, Finsupp.sub_apply, hE, ← dvd_neg, neg_sub]
    exact hdvd v

  let Y : Divisor K F := G.mapRange (fun k => k / (m : ℤ)) (by simp)
  have hmY : (m : ℤ) • Y = G := by
    ext v
    rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact Int.mul_ediv_cancel' (hGdvd v)
  have hGdeg : Divisor.degree G = 0 := by
    rw [hG, map_sub, Divisor.mem_degZero.mp D.2, hE0, sub_zero]
  have hYdeg : Y ∈ Divisor.degZero (K := K) (F := F) := by
    rw [Divisor.mem_degZero]
    have h := congrArg Divisor.degree hmY
    rw [map_zsmul, hGdeg, smul_eq_mul, mul_eq_zero] at h
    exact h.resolve_left (by exact_mod_cast hm)
  have hEdeg : E ∈ Divisor.degZero (K := K) (F := F) := Divisor.mem_degZero.mpr hE0
  have hEP : Pic0.mk ⟨E, hEdeg⟩ = 0 := (mk_eq_zero_iff _).2 ⟨f, hf, hE⟩
  refine ⟨Pic0.mk ⟨Y, hYdeg⟩, ?_⟩
  have hsum : (m • (⟨Y, hYdeg⟩ : Divisor.degZero (K := K) (F := F))) + ⟨E, hEdeg⟩ = D :=
    Subtype.ext <| by
      rw [AddSubgroup.coe_add, AddSubgroupClass.coe_nsmul]
      change m • Y + E = (D : Divisor K F)
      rw [← natCast_zsmul, hmY, hG, sub_add_cancel]
  calc m • Pic0.mk ⟨Y, hYdeg⟩
      = Pic0.mk (m • ⟨Y, hYdeg⟩) := by rw [Pic0.mk, Pic0.mk, QuotientAddGroup.mk_nsmul]
    _ = Pic0.mk (m • ⟨Y, hYdeg⟩ + ⟨E, hEdeg⟩) := by rw [Pic0.mk_add, hEP, add_zero]
    _ = Pic0.mk D := by rw [hsum]

theorem exists_nsmul_eq_of_quotient {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Λ : Submodule ℤ V) (m : ℕ) (hm : m ≠ 0) (t : V ⧸ Λ) : ∃ s : V ⧸ Λ, m • s = t := by
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective Λ t
  refine ⟨Submodule.Quotient.mk ((m : ℂ)⁻¹ • φ), ?_⟩
  rw [← Submodule.mkQ_apply, ← Submodule.mkQ_apply, ← map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), one_smul]

end General

section Level2

variable (M : ℕ) [NeZero M]

attribute [local instance] algQbC algF algQbFC isScalarTower_Qb_C_FC isScalarTower_Qb_FQ_FC
  isCurveOverQ isCurveOverC

theorem exists_liftPlace (v : Place Qb (FQ M)) :
    ∃ P' : Place ℂ (FC M),
      P'.toValuationSubring.comap (phi M) = v.toValuationSubring ∧
      (∀ f, P'.ord (phi M f) = v.ord f) ∧
      ∀ Q' : Place ℂ (FC M),
        Q'.toValuationSubring.comap (phi M) = v.toValuationSubring → Q' = P' :=
  Place.exists_comap_algebraMap_eq_of_constantFieldExtension Qb (FQ M) ℂ (FC M)
    (hfgQ M) (hfgC M) (adjoin_range_algebraMap M) v

def liftPlace (v : Place Qb (FQ M)) : Place ℂ (FC M) := (exists_liftPlace M v).choose

theorem liftPlace_comap (v : Place Qb (FQ M)) :
    (liftPlace M v).toValuationSubring.comap (phi M) = v.toValuationSubring :=
  (exists_liftPlace M v).choose_spec.1

theorem liftPlace_unique {v : Place Qb (FQ M)} {Q' : Place ℂ (FC M)}
    (h : Q'.toValuationSubring.comap (phi M) = v.toValuationSubring) : Q' = liftPlace M v :=
  (exists_liftPlace M v).choose_spec.2.2 Q' h

theorem liftPlace_injective : Function.Injective (liftPlace M) := fun v w h =>
  Place.ext (by rw [← liftPlace_comap M v, ← liftPlace_comap M w, h])

theorem forall_ne_liftPlace_of_comap_ne {w' : Place ℂ (FC M)}
    (h : ∀ v : Place Qb (FQ M),
      w'.toValuationSubring.comap (algebraMap (FQ M) (FC M)) ≠ v.toValuationSubring) :
    ∀ v, w' ≠ liftPlace M v := fun v hv =>
  h v (by rw [hv]; exact liftPlace_comap M v)

def conorm : Divisor Qb (FQ M) →+ Divisor ℂ (FC M) :=
  Finsupp.mapDomain.addMonoidHom (liftPlace M)

theorem conorm_apply (D : Divisor Qb (FQ M)) : conorm M D = Finsupp.mapDomain (liftPlace M) D :=
  rfl

@[scoped simp] theorem conorm_apply_liftPlace (D : Divisor Qb (FQ M)) (v : Place Qb (FQ M)) :
    conorm M D (liftPlace M v) = D v := by
  rw [conorm_apply]
  exact Finsupp.mapDomain_apply (liftPlace_injective M) D v

theorem conorm_apply_of_forall_ne (D : Divisor Qb (FQ M)) {w' : Place ℂ (FC M)}
    (h : ∀ v, w' ≠ liftPlace M v) : conorm M D w' = 0 := by
  rw [conorm_apply]
  exact Finsupp.mapDomain_notin_range D w' (by rintro ⟨v, rfl⟩; exact h v rfl)

theorem degree_conorm (D : Divisor Qb (FQ M)) :
    Divisor.degree (conorm M D) = Divisor.degree D := by
  rw [degree_eq_sum, degree_eq_sum, conorm_apply]
  exact Finsupp.sum_mapDomain_index_inj (liftPlace_injective M)

theorem conorm_mem_degZero {D : Divisor Qb (FQ M)}
    (hD : D ∈ Divisor.degZero (K := Qb) (F := FQ M)) :
    conorm M D ∈ Divisor.degZero (K := ℂ) (F := FC M) := by
  rw [Divisor.mem_degZero] at hD ⊢
  rw [degree_conorm, hD]

theorem hinC : ∀ ℓ : Nat.Primes,
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.HeckeInputsAlong ℂ M ℓ := fun ℓ => by
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  exact ModularCurve.heckeInputsAlong_of_prime ℂ M ℓ

theorem exists_nsmul_eq_complex (m : ℕ) (hm : m ≠ 0) (z : Pic0 ℂ (FC M)) :
    ∃ y : Pic0 ℂ (FC M), m • y = z := by
  obtain ⟨v, -⟩ :=
    ModularCurve.exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice M (hinC M)
      (ModularCurve.periodLatticeHeckeStable M)
  obtain ⟨s, hs⟩ := exists_nsmul_eq_of_quotient (periodLattice M) m hm (v z)
  refine ⟨v.symm s, v.injective ?_⟩
  rw [map_nsmul, AddEquiv.apply_symm_apply, hs]

theorem exists_dvd_ord_sub (m : ℕ) (hm : m ≠ 0) (D : Divisor.degZero (K := Qb) (F := FQ M)) :
    ∃ f : FQ M, f ≠ 0 ∧ ∀ v : Place Qb (FQ M), (m : ℤ) ∣ v.ord f - (D : Divisor Qb (FQ M)) v := by

  set Dt : Divisor.degZero (K := ℂ) (F := FC M) := ⟨conorm M D, conorm_mem_degZero M D.2⟩
    with hDt
  obtain ⟨y', hy'⟩ := exists_nsmul_eq_complex M m hm (Pic0.mk Dt)
  obtain ⟨E', rfl⟩ := Pic0.mk_surjective y'
  have hP : ((Dt - m • E' : Divisor.degZero (K := ℂ) (F := FC M)) : Divisor ℂ (FC M)).IsPrincipal := by
    rw [← mk_eq_zero_iff, Pic0.mk, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nsmul, sub_eq_zero]
    exact hy'.symm
  obtain ⟨f', hf', hf'D⟩ := hP
  have hdiv' : ∃ f' : FC M, f' ≠ 0 ∧ ∀ v' : Place ℂ (FC M), (m : ℤ) ∣ v'.ord f' - conorm M D v' := by
    refine ⟨f', hf', fun v' => ⟨-((E' : Divisor ℂ (FC M)) v'), ?_⟩⟩
    have h := hf'D v'
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_nsmul, Finsupp.sub_apply,
      Finsupp.smul_apply, nsmul_eq_mul] at h

    change (conorm M D) v' - (m : ℤ) * (E' : Divisor ℂ (FC M)) v' = v'.ord f' at h
    linear_combination -h

  exact Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension Qb (FQ M) ℂ (FC M)
    (hfgQ M) (hfgC M) (adjoin_range_algebraMap M) m hm (D : Divisor Qb (FQ M)) (conorm M D)
    (fun v' v h => by rw [liftPlace_unique M h, conorm_apply_liftPlace])
    (fun v' h => conorm_apply_of_forall_ne M _ (forall_ne_liftPlace_of_comap_ne M h)) hdiv'

theorem jZero_divisible (m : ℕ) (hm : m ≠ 0) (x : JZero M) : ∃ y : JZero M, m • y = x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  exact exists_nsmul_eq_mk_of_dvd m hm D (exists_dvd_ord_sub M m hm D)

end Level2

end ModularCurve.JZeroDivisible
p2m_reactivate "P2MW.S_ModularCurve_JZero_divisible.ModularCurve P2MW.S_ModularCurve_JZero_divisible.ModularCurve.JZeroDivisible"
p2m_reactivate "P2MW.S_ModularCurve_JZero_divisible.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_divisible.ModularCurve P2MW.S_ModularCurve_JZero_divisible.ModularCurve.JZeroDivisible"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_JZero_divisible.ModularCurve"

theorem solution (N : ℕ) [NeZero N] :
    ∀ m : ℕ, m ≠ 0 → ∀ x : JZero N, ∃ y : JZero N, m • y = x :=
  fun m hm x => ModularCurve.JZeroDivisible.jZero_divisible N m hm x

end S_ModularCurve_JZero_divisible
end P2MW
export P2MW.S_ModularCurve_JZero_divisible (solution)
