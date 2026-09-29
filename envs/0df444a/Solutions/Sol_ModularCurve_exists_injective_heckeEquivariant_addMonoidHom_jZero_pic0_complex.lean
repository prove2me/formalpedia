-- Prove2me | solution 1 for ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/03b79bd8-a12c-5417-8bed-0969da9570e0

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_PeriodLattice
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
import Theorems.Thm_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_Submodule_natCard_torsionBy_quotient_eq_pow_finrank
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve ModularCurve~coeffMap_qExpand P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeInputsAlong heckeOperatorAlong heckeOperatorAlong_eq heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral JZero qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff HeckeInputsAll period periodLattice exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice periodLatticeHeckeStable exists_basis_periodLattice_linearIndependent_real_span_eq_top exists_transcendental_finiteDimensional_modularFunctionFieldBar isCurveOver_modularFunctionFieldBar isCurveOver_laurentBaseChange_modularFunctionFieldFull transcendental_coeffEmb_jq finiteDimensional_adjoin_coeffEmb_jq_full"
namespace K1BC
p2m_open "ModularCurve~coeffMap_qExpand"

local notation "Qb" => AlgebraicClosure ℚ

local notation "FQ" M:max => laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)

local notation "FC" M:max => laurentBaseChange ℂ (modularFunctionFieldFull M)

def sigma : Qb →ₐ[ℚ] ℂ :=
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  IsAlgClosed.lift

def sigmaR : Qb →+* ℂ := (sigma : Qb →ₐ[ℚ] ℂ).toRingHom

theorem sigmaR_apply (a : Qb) : sigmaR a = sigma a := rfl

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

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

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

@[scoped simp] theorem coe_phi (x : FQ M) : (phi M x : LaurentSeries ℂ) = coeffMap sigmaR x := rfl

theorem phi_algebraMap (a : Qb) :
    phi M (algebraMap Qb (FQ M) a) = algebraMap ℂ (FC M) (sigmaR a) :=
  Subtype.ext (coeffMap_sigma_algebraMap a)

theorem phi_injective : Function.Injective (phi M) := (phi M).injective

theorem phi_ne_zero {f : FQ M} (hf : f ≠ 0) : phi M f ≠ 0 :=
  (map_ne_zero_iff _ (phi_injective M)).2 hf

@[reducible] def algQbC : Algebra Qb ℂ := sigmaR.toAlgebra

@[reducible] def algF : Algebra (FQ M) (FC M) := (phi M).toAlgebra

@[reducible] def algQbFC : Algebra Qb (FC M) := ((algebraMap ℂ (FC M)).comp sigmaR).toAlgebra

attribute [local instance] algQbC algF algQbFC

theorem algebraMap_FQ_FC : algebraMap (FQ M) (FC M) = phi M := rfl

theorem algebraMap_Qb_C : algebraMap Qb ℂ = sigmaR := rfl

theorem algebraMap_Qb_FC (a : Qb) : algebraMap Qb (FC M) a = algebraMap ℂ (FC M) (sigmaR a) := rfl

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

theorem adjoin_range_phi : IntermediateField.adjoin ℂ (Set.range (phi M)) = ⊤ := by
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

theorem adjoin_range_algebraMap :
    IntermediateField.adjoin ℂ (Set.range (algebraMap (FQ M) (FC M))) = ⊤ :=
  adjoin_range_phi M

end Level

section PlaceHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem ord_eq_zero_of_mem_of_inv_mem {f : F} (hf : f ∈ v.toValuationSubring)
    (hfi : f⁻¹ ∈ v.toValuationSubring) : v.ord f = 0 := by
  have h1 := ord_nonneg_of_mem v hf
  have h2 := ord_nonneg_of_mem v hfi
  rw [Place.ord_inv] at h2
  omega

theorem exists_not_mem : ∃ g : F, g ∉ v.toValuationSubring := by
  by_contra h
  push Not at h
  exact v.ne_top' (SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => h x⟩)

theorem exists_ord_eq_one : ∃ f : F, v.ord f = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  exact ⟨π, v.ord_coe_irreducible hπ⟩

theorem degree_eq_sum [IsAlgClosed K] [IsCurveOver K F] (D : Divisor K F) :
    Divisor.degree D = D.sum fun _ n => n := by
  simp only [Divisor.degree, Finsupp.liftAddHom_apply, IsCurveOver.deg_eq_one_of_isAlgClosed,
    Nat.cast_one]
  refine Finsupp.sum_congr fun v _ => ?_
  simp

end PlaceHelpers

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

theorem mem_liftPlace_iff (v : Place Qb (FQ M)) (f : FQ M) :
    phi M f ∈ (liftPlace M v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [← liftPlace_comap M v]
  exact Iff.rfl

theorem ord_liftPlace (v : Place Qb (FQ M)) (f : FQ M) :
    (liftPlace M v).ord (phi M f) = v.ord f :=
  (exists_liftPlace M v).choose_spec.2.1 f

theorem liftPlace_unique {v : Place Qb (FQ M)} {Q' : Place ℂ (FC M)}
    (h : Q'.toValuationSubring.comap (phi M) = v.toValuationSubring) : Q' = liftPlace M v :=
  (exists_liftPlace M v).choose_spec.2.2 Q' h

theorem liftPlace_injective : Function.Injective (liftPlace M) := fun v w h =>
  Place.ext (by rw [← liftPlace_comap M v, ← liftPlace_comap M w, h])

theorem exists_eq_liftPlace {w' : Place ℂ (FC M)}
    (hwx : ∃ y : FQ M, phi M y ∉ w'.toValuationSubring) : ∃ v, w' = liftPlace M v := by
  obtain ⟨x, _, hfd⟩ := hfgQ M
  haveI := hfd
  obtain ⟨v, hv⟩ := Place.exists_toValuationSubring_eq_comap_ringHom (K := Qb) x (phi M)
    w'.toValuationSubring (fun a => by rw [phi_algebraMap]; exact w'.algebraMap_mem' _) hwx
  exact ⟨v, liftPlace_unique M hv.symm⟩

theorem ord_phi_of_forall_ne {w' : Place ℂ (FC M)} (hoff : ∀ v, w' ≠ liftPlace M v)
    (f : FQ M) : w'.ord (phi M f) = 0 := by
  have hall : ∀ y : FQ M, phi M y ∈ w'.toValuationSubring := by
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := exists_eq_liftPlace M h
    exact hoff v hv
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  exact ord_eq_zero_of_mem_of_inv_mem w' (hall f) (by rw [← map_inv₀]; exact hall f⁻¹)

theorem forall_ne_liftPlace_of_comap_ne {w' : Place ℂ (FC M)}
    (h : ∀ v : Place Qb (FQ M),
      w'.toValuationSubring.comap (algebraMap (FQ M) (FC M)) ≠ v.toValuationSubring) :
    ∀ v, w' ≠ liftPlace M v := fun v hv =>
  h v (by rw [hv]; exact liftPlace_comap M v)

theorem forall_comap_ne_of_ne_liftPlace {w' : Place ℂ (FC M)}
    (h : ∀ v, w' ≠ liftPlace M v) (v : Place Qb (FQ M)) :
    w'.toValuationSubring.comap (algebraMap (FQ M) (FC M)) ≠ v.toValuationSubring := fun hv =>
  h v (liftPlace_unique M hv)

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

@[scoped simp] theorem conorm_single (v : Place Qb (FQ M)) (n : ℤ) :
    conorm M (Finsupp.single v n) = Finsupp.single (liftPlace M v) n := by
  rw [conorm_apply, Finsupp.mapDomain_single]

theorem degree_conorm (D : Divisor Qb (FQ M)) :
    Divisor.degree (conorm M D) = Divisor.degree D := by
  rw [degree_eq_sum, degree_eq_sum, conorm_apply]
  exact Finsupp.sum_mapDomain_index_inj (liftPlace_injective M)

theorem isPrincipal_conorm {D : Divisor Qb (FQ M)} (hD : D.IsPrincipal) :
    (conorm M D).IsPrincipal := by
  obtain ⟨f, hf, hDf⟩ := hD
  refine ⟨phi M f, phi_ne_zero M hf, fun w' => ?_⟩
  by_cases h : ∃ v, w' = liftPlace M v
  · obtain ⟨v, rfl⟩ := h
    rw [conorm_apply_liftPlace, ord_liftPlace, hDf]
  · push Not at h
    rw [conorm_apply_of_forall_ne M D h, ord_phi_of_forall_ne M h]

theorem conorm_mem_degZero {D : Divisor Qb (FQ M)}
    (hD : D ∈ Divisor.degZero (K := Qb) (F := FQ M)) :
    conorm M D ∈ Divisor.degZero (K := ℂ) (F := FC M) := by
  rw [Divisor.mem_degZero] at hD ⊢
  rw [degree_conorm, hD]

def conormDegZero :
    Divisor.degZero (K := Qb) (F := FQ M) →+ Divisor.degZero (K := ℂ) (F := FC M) :=
  ((conorm M).domRestrict _).codRestrict _ fun D => conorm_mem_degZero M D.2

@[scoped simp] theorem coe_conormDegZero (D : Divisor.degZero (K := Qb) (F := FQ M)) :
    (conormDegZero M D : Divisor ℂ (FC M)) = conorm M D := rfl

def iota : Pic0 Qb (FQ M) →+ Pic0 ℂ (FC M) :=
  QuotientAddGroup.map _ _ (conormDegZero M) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact isPrincipal_conorm M hD)

theorem iota_mk (D : Divisor.degZero (K := Qb) (F := FQ M)) :
    iota M (Pic0.mk D) = Pic0.mk (conormDegZero M D) := rfl

theorem mk_eq_zero_iff {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    (D : Divisor.degZero (K := K') (F := F')) :
    Pic0.mk D = 0 ↔ (D : Divisor K' F').IsPrincipal := by
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]

theorem mk_eq_mk_of_add_eq {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    (A B C : Divisor.degZero (K := K') (F := F')) (hC : Pic0.mk C = 0) (h : A + C = B) :
    Pic0.mk A = Pic0.mk B := by
  rw [← h, Pic0.mk_add, hC, add_zero]

theorem iota_injective : Function.Injective (iota M) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [iota_mk, mk_eq_zero_iff, coe_conormDegZero] at hx
  rw [mk_eq_zero_iff]
  exact Divisor.isPrincipal_of_constantFieldExtension Qb (FQ M) ℂ (FC M) (hfgQ M) (hfgC M)
    (adjoin_range_algebraMap M) D (conorm M D)
    (fun v' v h => by rw [liftPlace_unique M h, conorm_apply_liftPlace])
    (fun v' h => conorm_apply_of_forall_ne M _ (forall_ne_liftPlace_of_comap_ne M h)) hx

theorem finite_torsionBy_quotient {K : Type*} [DivisionRing K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (L : Submodule ℤ V) [Module.Free ℤ L] [Module.Finite ℤ L] (n : ℕ) (hn : n ≠ 0) :
    Finite (Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ)) :=
  Nat.finite_of_card_ne_zero (by
    rw [Submodule.natCard_torsionBy_quotient_eq_pow_finrank (K := K) L n hn]
    exact pow_ne_zero _ hn)

theorem finite_torsion_of_injective {A : Type*} [AddCommGroup A] {K : Type*} [DivisionRing K]
    [CharZero K] {V : Type*} [AddCommGroup V] [Module K V]
    (L : Submodule ℤ V) [Module.Free ℤ L] [Module.Finite ℤ L]
    (f : A →+ V ⧸ L) (hf : Function.Injective f) (n : ℕ) (hn : n ≠ 0) :
    Finite {c : A // n • c = 0} := by
  haveI := finite_torsionBy_quotient (K := K) L n hn
  refine Finite.of_injective
    (fun c : {c : A // n • c = 0} =>
      (⟨f c.1, ?_⟩ : Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ))) ?_
  · rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← map_nsmul, c.2, map_zero]
  · intro c d h
    exact Subtype.ext (hf (congrArg Subtype.val h))

theorem finite_torsion_pic0C
    (hinC : ∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.HeckeInputsAlong ℂ M ℓ)
    (n : ℕ) (hn : n ≠ 0) :
    Finite {c : Pic0 ℂ (FC M) // n • c = 0} := by
  obtain ⟨v, -⟩ :=
    ModularCurve.exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice M hinC
      (ModularCurve.periodLatticeHeckeStable M)
  obtain ⟨m, b, -, -⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top M
  haveI : Module.Free ℤ (periodLattice M) := Module.Free.of_basis b
  haveI : Module.Finite ℤ (periodLattice M) := Module.Finite.of_basis b
  exact finite_torsion_of_injective (K := ℂ) (periodLattice M) v.toAddMonoidHom v.injective n hn

theorem mem_range_iota_of_isOfFinAddOrder
    (hinC : ∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.HeckeInputsAlong ℂ M ℓ)
    {z : Pic0 ℂ (FC M)} (hz : IsOfFinAddOrder z) :
    z ∈ (iota M).range := by
  obtain ⟨D', rfl⟩ := Pic0.mk_surjective z
  set n : ℕ := addOrderOf (Pic0.mk D') with hn_def
  have hn : n ≠ 0 := (hz.addOrderOf_pos).ne'

  have hnD : ((n • D' : Divisor.degZero (K := ℂ) (F := FC M)) : Divisor ℂ (FC M)).IsPrincipal := by
    rw [← mk_eq_zero_iff, Pic0.mk, QuotientAddGroup.mk_nsmul]
    exact addOrderOf_nsmul_eq_zero (Pic0.mk D')
  obtain ⟨g', hg', hg'D⟩ := hnD
  have hD'tors : ∃ g' : FC M, g' ≠ 0 ∧ ∀ v', (n : ℤ) * (D' : Divisor ℂ (FC M)) v' = v'.ord g' :=
    ⟨g', hg', fun v' => by
      have := hg'D v'
      rwa [AddSubgroupClass.coe_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at this⟩

  obtain ⟨D, h', hh', _, hover, hoff⟩ :=
    Divisor.exists_torsion_descent_of_constantFieldExtension_of_finite Qb (FQ M) ℂ (FC M) (hfgQ M)
      (hfgC M) (adjoin_range_algebraMap M) n hn (finite_torsion_pic0C M hinC n hn)
      (D' : Divisor ℂ (FC M)) hD'tors

  obtain ⟨E', hE', hE'0⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) h' hh'
  have hsplit : ∀ w', (D' : Divisor ℂ (FC M)) w' = conorm M D w' + E' w' := by
    intro w'
    by_cases h : ∃ v, w' = liftPlace M v
    · obtain ⟨v, rfl⟩ := h
      rw [conorm_apply_liftPlace, hE', hover v (liftPlace M v) (liftPlace_comap M v)]
    · push Not at h
      rw [conorm_apply_of_forall_ne M D h, hE', zero_add,
        hoff w' (forall_comap_ne_of_ne_liftPlace M h)]
  have hD0 : D ∈ Divisor.degZero (K := Qb) (F := FQ M) := by
    rw [Divisor.mem_degZero, ← degree_conorm M D]
    have hcon : conorm M D = (D' : Divisor ℂ (FC M)) - E' := by
      ext w'
      rw [Finsupp.sub_apply, hsplit]
      ring
    rw [hcon, map_sub, Divisor.mem_degZero.mp D'.2, hE'0, sub_zero]
  have hE'deg : E' ∈ Divisor.degZero (K := ℂ) (F := FC M) := Divisor.mem_degZero.mpr hE'0
  refine ⟨Pic0.mk ⟨D, hD0⟩, ?_⟩
  rw [iota_mk]
  have hE'P : Pic0.mk ⟨E', hE'deg⟩ = 0 := by
    rw [mk_eq_zero_iff]
    exact ⟨h', hh', hE'⟩
  have hsum : conormDegZero M ⟨D, hD0⟩ + ⟨E', hE'deg⟩ = D' :=
    Subtype.ext <| Finsupp.ext fun w' => by
      simp only [AddSubgroup.coe_add, Finsupp.add_apply, coe_conormDegZero, hsplit w']
  exact mk_eq_mk_of_add_eq _ _ _ hE'P hsum

end Level2

theorem inertiaDegAlong_eq_one {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h := Place.deg_restrict_mul_inertiaDeg (F := F) w
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed,
    one_mul] at h
  exact h

section Compat

attribute [local instance] algQbC algF algQbFC isScalarTower_Qb_C_FC isScalarTower_Qb_FQ_FC
  isCurveOverQ isCurveOverC

variable {M M' : ℕ} [NeZero M] [NeZero M']
  (ψQ : FQ M →ₐ[Qb] FQ M') (ψC : FC M →ₐ[ℂ] FC M')
  (hψQ : ψQ.toRingHom.IsIntegral) (hψC : ψC.toRingHom.IsIntegral)
  (hc : ∀ f, phi M' (ψQ f) = ψC (phi M f))

include hψQ hψC hc

theorem restrictAlong_liftPlace (W : Place Qb (FQ M')) :
    (liftPlace M' W).restrictAlong ψC hψC = liftPlace M (W.restrictAlong ψQ hψQ) := by
  refine liftPlace_unique M ?_
  ext f
  show ψC (phi M f) ∈ (liftPlace M' W).toValuationSubring ↔ ψQ f ∈ W.toValuationSubring
  rw [← hc, mem_liftPlace_iff]

theorem ramificationIndexAlong_liftPlace (W : Place Qb (FQ M')) :
    (liftPlace M' W).ramificationIndexAlong ψC = W.ramificationIndexAlong ψQ := by
  obtain ⟨f, hf⟩ := exists_ord_eq_one (W.restrictAlong ψQ hψQ)
  have hQ := Place.ord_restrictAlong ψQ hψQ W f
  have hC := Place.ord_restrictAlong ψC hψC (liftPlace M' W) (phi M f)
  rw [restrictAlong_liftPlace ψQ ψC hψQ hψC hc, ord_liftPlace, hf, mul_one, ← hc, ord_liftPlace,
    hQ, hf, mul_one] at hC
  exact_mod_cast hC.symm

omit hψQ hc in

theorem mem_restrictAlong_C_iff (W' : Place ℂ (FC M')) (x : FC M) :
    x ∈ (W'.restrictAlong ψC hψC).toValuationSubring ↔ ψC x ∈ W'.toValuationSubring :=
  Iff.rfl

theorem exists_eq_liftPlace_of_restrictAlong {v : Place Qb (FQ M)} {W' : Place ℂ (FC M')}
    (hW' : W'.restrictAlong ψC hψC = liftPlace M v) : ∃ W, W' = liftPlace M' W := by
  obtain ⟨g, hg⟩ := exists_not_mem v
  refine exists_eq_liftPlace M' ⟨ψQ g, fun hmem => hg ?_⟩
  rw [hc, ← mem_restrictAlong_C_iff ψC hψC W' (phi M g), hW'] at hmem
  exact (mem_liftPlace_iff M v g).1 hmem

theorem fiberAlong_liftPlace (v : Place Qb (FQ M)) :
    Place.fiberAlong ψC hψC (liftPlace M v) =
      (Place.fiberAlong ψQ hψQ v).map ⟨liftPlace M', liftPlace_injective M'⟩ := by
  ext W'
  rw [Place.mem_fiberAlong, Finset.mem_map]
  constructor
  · intro hW'
    obtain ⟨W, rfl⟩ := exists_eq_liftPlace_of_restrictAlong ψQ ψC hψQ hψC hc hW'
    refine ⟨W, ?_, rfl⟩
    rw [Place.mem_fiberAlong]
    apply liftPlace_injective M
    rw [← restrictAlong_liftPlace ψQ ψC hψQ hψC hc W]
    exact hW'
  · rintro ⟨W, hW, rfl⟩
    rw [Place.mem_fiberAlong] at hW
    rw [Function.Embedding.coeFn_mk, restrictAlong_liftPlace ψQ ψC hψQ hψC hc, hW]

end Compat

section HeckeLevel

attribute [local instance] algQbC algF algQbFC isScalarTower_Qb_C_FC isScalarTower_Qb_FQ_FC
  isCurveOverQ isCurveOverC

variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

theorem phi_heckeAlphaBar (f : FQ N) :
    phi (N * ℓ) (heckeAlphaBar Qb N ℓ f) = heckeAlphaBar ℂ N ℓ (phi N f) :=
  Subtype.ext (by simp only [coe_phi, coe_heckeAlphaBar])

theorem phi_heckeBetaBar (f : FQ N) :
    phi (N * ℓ) (heckeBetaBar Qb N ℓ f) = heckeBetaBar ℂ N ℓ (phi N f) :=
  Subtype.ext (by simp only [coe_phi, coe_heckeBetaBar, coeffMap_qExpand])

theorem conorm_heckeDiv (hαQ : HeckeAlphaBarIntegral Qb N ℓ) (hβQ : HeckeBetaBarIntegral Qb N ℓ)
    (hαC : HeckeAlphaBarIntegral ℂ N ℓ) (hβC : HeckeBetaBarIntegral ℂ N ℓ)
    (D : Divisor Qb (FQ N)) :
    conorm N (Divisor.correspondence (heckeBetaBar Qb N ℓ) (heckeAlphaBar Qb N ℓ) hβQ hαQ D) =
      Divisor.correspondence (heckeBetaBar ℂ N ℓ) (heckeAlphaBar ℂ N ℓ) hβC hαC (conorm N D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add D E hD hE => simp only [map_add, hD, hE]
  | single v n =>
    simp only [Divisor.correspondence_apply, conorm_single, Divisor.pullbackAlong_single, map_sum,
      Divisor.pushforwardAlong_single,
      fiberAlong_liftPlace _ _ hβQ hβC (phi_heckeBetaBar N ℓ),
      Finset.sum_map, Function.Embedding.coeFn_mk,
      ramificationIndexAlong_liftPlace _ _ hβQ hβC (phi_heckeBetaBar N ℓ),
      restrictAlong_liftPlace _ _ hαQ hαC (phi_heckeAlphaBar N ℓ),
      inertiaDegAlong_eq_one, Nat.cast_one, mul_one]

theorem iota_heckeOperatorAlong (hQ : HeckeInputsAlong Qb N ℓ) (hC : HeckeInputsAlong ℂ N ℓ)
    (x : Pic0 Qb (FQ N)) :
    iota N (heckeOperatorAlong Qb N ℓ x) = heckeOperatorAlong ℂ N ℓ (iota N x) := by
  obtain ⟨hαQ, hβQ, hPQ, hfinQ, hFIQ, hNQ⟩ := hQ
  obtain ⟨hαC, hβC, hPC, hfinC, hFIC, hNC⟩ := hC
  rw [heckeOperatorAlong_eq hαQ hβQ hFIQ hfinQ hNQ, heckeOperatorAlong_eq hαC hβC hFIC hfinC hNC]
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  change Pic0.mk (conormDegZero N (Pic0.degZeroCorrespondence _ _ hβQ hαQ hFIQ D)) =
    Pic0.mk (Pic0.degZeroCorrespondence _ _ hβC hαC hFIC (conormDegZero N D))
  refine congrArg Pic0.mk (Subtype.ext ?_)
  simp only [coe_conormDegZero, Pic0.coe_degZeroCorrespondence]
  exact conorm_heckeDiv N ℓ hαQ hβQ hαC hβC D

end HeckeLevel

end ModularCurve.K1BC
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex.ModularCurve P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex.ModularCurve.K1BC"
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex.ModularCurve"

theorem solution
    (N : ℕ) [NeZero N]
    (hin : ModularCurve.HeckeInputsAll N)
    (hinC : ∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.HeckeInputsAlong ℂ N ℓ) :
    ∃ ι : ModularCurve.JZero N →+
        AlgebraicCurve.Pic0 ℂ
          (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)),
      Function.Injective ι ∧
      (∀ z, IsOfFinAddOrder z → z ∈ ι.range) ∧
      ∀ (ℓ : Nat.Primes) (x : ModularCurve.JZero N),
        ι (ModularCurve.heckeOperatorBar N ℓ x) =
          (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.heckeOperatorAlong ℂ N ℓ)
            (ι x) := by
  refine ⟨ModularCurve.K1BC.iota N, ModularCurve.K1BC.iota_injective N,
    fun z hz => ModularCurve.K1BC.mem_range_iota_of_isOfFinAddOrder N hinC hz, fun ℓ x => ?_⟩
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  exact ModularCurve.K1BC.iota_heckeOperatorAlong N ℓ (hin ℓ) (hinC ℓ) x

end
p2m_reactivate "P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex.ModularCurve P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex.ModularCurve.K1BC"

end S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex
end P2MW
export P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex (solution)
