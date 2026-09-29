-- Prove2me | solution 1 for ModularCurve.exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/6d6a57f6-bc37-5573-9453-7465769c16f4

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorTotal
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionary
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_pt_eq_of_mem
import Theorems.Thm_ModularCurve_addSubgroupClosure_range_periodAlong_eq_top
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_abelJacobi_mem_periodLattice_of_isPrincipal
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_isPrincipal_of_abelJacobi_mem_periodLattice
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply"
p2m_attr_erase "simp" "HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane AlgebraicCurve
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "HeckeInputsAlong heckeOperatorAlong heckeOperatorAlong_eq heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral heckeDivBar heckePic0Bar jq jq_mem modularFunctionFieldFull modularFunctionField_le_full coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange clamp01_of_mem segmentPoint continuous_segmentPoint segmentPath coe_segmentPath intervalIntegrable_periodIntegrand periodAlong periodAlong_apply period periodLattice dualHeckeRep PeriodLatticeHeckeStable heckeGen ComplexPlaceDictionary exists_complexPlaceDictionary ComplexPlaceDictionary.exists_pt_eq_of_mem addSubgroupClosure_range_periodAlong_eq_top exists_hasEquivariantPrimitive isCurveOver_laurentBaseChange_modularFunctionFieldFull ComplexPlaceDictionary.abelJacobi_mem_periodLattice_of_isPrincipal ComplexPlaceDictionary.isPrincipal_of_abelJacobi_mem_periodLattice ComplexPlaceDictionary.exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice"
namespace AbelJacobiIsoGlue
p2m_open "ModularCurve"

section FTC

theorem hasDerivAt_affine (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a + (s : ℂ) * b) (b - a) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a) (-(1 : ℂ) * a) t := by
    simpa using ((hasDerivAt_const t (1 : ℂ)).sub h1).mul_const a
  have h3 : HasDerivAt (fun s : ℝ => (s : ℂ) * b) (1 * b) t := h1.mul_const b
  have := h2.add h3
  convert this using 1 <;> first | rfl | ring

theorem segmentPoint_eq_of_mem {τ₀ τ₁ : ℍ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ModularCurve.segmentPoint τ₀ τ₁ t = (1 - (t : ℂ)) * (τ₀ : ℂ) + (t : ℂ) * (τ₁ : ℂ) := by
  simp only [ModularCurve.segmentPoint, ModularCurve.clamp01_of_mem ht, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem periodAlong_eq_sub (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    {F : ℍ → ℂ} (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ₀ τ₁ : ℍ) :
    ModularCurve.periodAlong N τ₀ τ₁ f = F τ₁ - F τ₀ := by
  rw [ModularCurve.periodAlong_apply]
  set g : ℝ → ℂ := fun t => F (ModularCurve.segmentPath τ₀ τ₁ t) with hg
  have hgF : ∀ t, g t = (F ∘ ofComplex) (ModularCurve.segmentPoint τ₀ τ₁ t) := by
    intro t
    simp only [hg, Function.comp]
    congr 1
    rw [← ModularCurve.coe_segmentPath, ofComplex_apply]
  have hg0 : g 0 = F τ₀ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 0 = (τ₀ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨le_rfl, zero_le_one⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hg1 : g 1 = F τ₁ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 1 = (τ₁ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨zero_le_one, le_rfl⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hFcont : ∀ τ : ℍ, ContinuousAt (F ∘ ofComplex) (τ : ℂ) := fun τ => (hF τ).continuousAt
  have hgcont : Continuous g := by
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    refine continuous_iff_continuousAt.mpr fun t => ?_
    refine ContinuousAt.comp ?_ (ModularCurve.continuous_segmentPoint τ₀ τ₁).continuousAt
    have := hFcont (ModularCurve.segmentPath τ₀ τ₁ t)
    rwa [ModularCurve.coe_segmentPath] at this
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g (f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) t := by
    intro t ht
    have hpath : HasDerivAt (ModularCurve.segmentPoint τ₀ τ₁) ((τ₁ : ℂ) - τ₀) t := by
      refine (hasDerivAt_affine (τ₀ : ℂ) (τ₁ : ℂ) t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact segmentPoint_eq_of_mem (Set.Ioo_subset_Icc_self hs)
    have hFat : HasDerivAt (F ∘ ofComplex) (f (ModularCurve.segmentPath τ₀ τ₁ t))
        (ModularCurve.segmentPoint τ₀ τ₁ t) := by
      have := hF (ModularCurve.segmentPath τ₀ τ₁ t)
      rwa [ModularCurve.coe_segmentPath] at this
    have hcomp := hFat.comp t hpath
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    exact hcomp
  have hint : IntervalIntegrable
      (fun t => f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) MeasureTheory.volume 0 1 :=
    ModularCurve.intervalIntegrable_periodIntegrand N τ₀ τ₁ f 0 1
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    hgcont.continuousOn hderiv hint
  rw [key, hg0, hg1]

theorem periodAlong_eq_periodAlong_I_sub (N : ℕ) [NeZero N] (τ₀ τ₁ : ℍ) :
    ModularCurve.periodAlong N τ₀ τ₁ =
      ModularCurve.periodAlong N I τ₁ - ModularCurve.periodAlong N I τ₀ := by
  refine LinearMap.ext fun f => ?_
  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitive N f
  rw [LinearMap.sub_apply, periodAlong_eq_sub N f hF.1, periodAlong_eq_sub N f hF.1,
    periodAlong_eq_sub N f hF.1]
  ring

end FTC

section AJ

variable (N : ℕ)

def aj : (ℍ →₀ ℤ) →+ Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  Finsupp.liftAddHom fun τ => zmultiplesHom _ (ModularCurve.periodAlong N I τ)

theorem aj_apply (c : ℍ →₀ ℤ) :
    aj N c = c.sum fun τ n => n • ModularCurve.periodAlong N I τ := by
  simp only [aj, Finsupp.liftAddHom_apply]
  rfl

@[scoped simp]
theorem aj_single (τ : ℍ) (n : ℤ) : aj N (Finsupp.single τ n) = n • ModularCurve.periodAlong N I τ := by
  simp [aj_apply]

end AJ

section DVR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

end DVR

section Curve

variable {N : ℕ} [NeZero N]

local notation "𝔽" => (laurentBaseChange ℂ (modularFunctionFieldFull N))

scoped instance instIsCurveOver : IsCurveOver ℂ (laurentBaseChange ℂ (modularFunctionFieldFull N)) :=
  ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull ℂ N

theorem deg_eq_one (v : Place ℂ 𝔽) : v.deg = 1 :=
  IsCurveOver.deg_eq_one_of_isAlgClosed v

def jN (N : ℕ) [NeZero N] : laurentBaseChange ℂ (modularFunctionFieldFull N) :=
  ⟨ModularCurve.coeffEmb ℂ ModularCurve.jq,
    ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
      (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩

theorem exists_pt_eq (D : ModularCurve.ComplexPlaceDictionary N) (P : Place ℂ 𝔽)
    (hP : jN N ∈ P.toValuationSubring) : ∃ τ : ℍ, D.pt τ = P :=
  ModularCurve.ComplexPlaceDictionary.exists_pt_eq_of_mem D P hP

theorem exists_div (x : 𝔽) (hx : x ≠ 0) :
    ∃ Dx : Divisor ℂ 𝔽, (∀ v, Dx v = v.ord x) ∧ Divisor.degree Dx = 0 :=
  HasPrincipalDivisors.exists_divisor x hx

theorem exists_finset_cusps :
    ∃ S : Finset (Place ℂ 𝔽), ∀ v : Place ℂ 𝔽, jN N ∉ v.toValuationSubring → v ∈ S := by
  by_cases hj : jN N = 0
  · exact ⟨∅, fun v hv => (hv (by rw [hj]; exact zero_mem _)).elim⟩
  obtain ⟨Dj, hDj, -⟩ := exists_div (jN N) hj
  refine ⟨Dj.support, fun v hv => ?_⟩
  by_contra hvS
  have h0 : Dj v = 0 := Finsupp.notMem_support_iff.mp hvS
  exact hv (mem_of_ord_nonneg v hj (by rw [← hDj v, h0]))

theorem exists_decomp (D : ModularCurve.ComplexPlaceDictionary N) (E : Divisor ℂ 𝔽) :
    ∃ (x : 𝔽) (c : ℍ →₀ ℤ), x ≠ 0 ∧ ∀ v, E v = v.ord x + Finsupp.mapDomain D.pt c v := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_cusps (N := N)

  obtain ⟨x, hx0, hx⟩ := AlgebraicCurve.Place.exists_forall_ord_eq S (fun v => E v)
  obtain ⟨Dx, hDx, -⟩ := exists_div x hx0
  set E' : Divisor ℂ 𝔽 := E - Dx with hE'
  have hE'cusp : ∀ v, jN N ∉ v.toValuationSubring → E' v = 0 := by
    intro v hv
    simp only [hE', Finsupp.coe_sub, Pi.sub_apply, hDx v, hx v (hS v hv), sub_self]

  let lift : Place ℂ 𝔽 → ℍ := fun v =>
    if h : jN N ∈ v.toValuationSubring then (exists_pt_eq D v h).choose else I
  have hlift : ∀ v ∈ E'.support, D.pt (lift v) = v := by
    intro v hv
    have hj : jN N ∈ v.toValuationSubring := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hv) (hE'cusp v h)
    simp only [lift, dif_pos hj]
    exact (exists_pt_eq D v hj).choose_spec
  refine ⟨x, Finsupp.mapDomain lift E', hx0, fun v => ?_⟩
  have hcomp : Finsupp.mapDomain D.pt (Finsupp.mapDomain lift E') = E' := by
    rw [← Finsupp.mapDomain_comp]
    rw [Finsupp.mapDomain_congr (g := id) (fun v hv => by simp [Function.comp, hlift v hv]),
      Finsupp.mapDomain_id]
  rw [hcomp, hE']
  simp [hDx v]

theorem degree_mapDomain_pt (D : ModularCurve.ComplexPlaceDictionary N) (c : ℍ →₀ ℤ) :
    Divisor.degree (Finsupp.mapDomain D.pt c) = c.sum fun _ n => n := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, Finsupp.mapDomain_single, ih,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
      Divisor.degree_single, deg_eq_one]
    simp

end Curve

section AJClass

variable {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N)

local notation "𝔽" => (laurentBaseChange ℂ (modularFunctionFieldFull N))
local notation "Λ" => ModularCurve.periodLattice N

theorem aj_mem_of_forall_eq_ord {c : ℍ →₀ ℤ} {x : 𝔽} (hx : x ≠ 0)
    (h : ∀ v, Finsupp.mapDomain D.pt c v = v.ord x) : aj N c ∈ Λ := by
  rw [aj_apply]
  exact ModularCurve.ComplexPlaceDictionary.abelJacobi_mem_periodLattice_of_isPrincipal D c
    ⟨x, hx, h⟩

theorem mk_aj_eq_of_rel {c₁ c₂ : ℍ →₀ ℤ} {x : 𝔽} (hx : x ≠ 0)
    (h : ∀ v, Finsupp.mapDomain D.pt c₁ v = Finsupp.mapDomain D.pt c₂ v + v.ord x) :
    (Submodule.Quotient.mk (aj N c₁) : _ ⧸ Λ) = Submodule.Quotient.mk (aj N c₂) := by
  rw [Submodule.Quotient.eq, ← map_sub]
  refine aj_mem_of_forall_eq_ord D hx fun v => ?_
  rw [Finsupp.mapDomain_sub, Finsupp.coe_sub, Pi.sub_apply, h v]
  ring

def fn (E : Divisor ℂ 𝔽) : 𝔽 := (exists_decomp D E).choose

private def _root_.ModularCurve.AbelJacobiIsoGlue.lift (E : Divisor ℂ 𝔽) : ℍ →₀ ℤ := (exists_decomp D E).choose_spec.choose

p2m_export "ModularCurve.AbelJacobiIsoGlue" "lift"
theorem fn_ne_zero (E : Divisor ℂ 𝔽) : fn D E ≠ 0 :=
  (exists_decomp D E).choose_spec.choose_spec.1

theorem decomp_spec (E : Divisor ℂ 𝔽) (v : Place ℂ 𝔽) :
    E v = v.ord (fn D E) + Finsupp.mapDomain D.pt (lift D E) v :=
  (exists_decomp D E).choose_spec.choose_spec.2 v

def ajClassFun (E : Divisor ℂ 𝔽) :
    Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) ⧸ Λ :=
  Submodule.Quotient.mk (aj N (lift D E))

theorem ajClassFun_eq {E : Divisor ℂ 𝔽} {x : 𝔽} {c : ℍ →₀ ℤ} (hx : x ≠ 0)
    (h : ∀ v, E v = v.ord x + Finsupp.mapDomain D.pt c v) :
    ajClassFun D E = Submodule.Quotient.mk (aj N c) := by

  refine mk_aj_eq_of_rel D (x := x * (fn D E)⁻¹) (mul_ne_zero hx (inv_ne_zero (fn_ne_zero D E)))
    fun v => ?_
  have h1 := decomp_spec D E v
  have h2 := h v
  rw [v.ord_mul hx (inv_ne_zero (fn_ne_zero D E)), v.ord_inv]
  linarith

theorem ajClassFun_add (E₁ E₂ : Divisor ℂ 𝔽) :
    ajClassFun D (E₁ + E₂) = ajClassFun D E₁ + ajClassFun D E₂ := by
  have h : ∀ v, (E₁ + E₂) v = v.ord (fn D E₁ * fn D E₂) +
      Finsupp.mapDomain D.pt (lift D E₁ + lift D E₂) v := by
    intro v
    rw [Finsupp.coe_add, Pi.add_apply, decomp_spec D E₁ v, decomp_spec D E₂ v,
      v.ord_mul (fn_ne_zero D E₁) (fn_ne_zero D E₂), Finsupp.mapDomain_add,
      Finsupp.coe_add, Pi.add_apply]
    ring
  rw [ajClassFun_eq D (mul_ne_zero (fn_ne_zero D E₁) (fn_ne_zero D E₂)) h, map_add,
    Submodule.Quotient.mk_add]
  rfl

def ajClass : Divisor ℂ 𝔽 →+ Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) ⧸ Λ :=
  AddMonoidHom.mk' (ajClassFun D) (ajClassFun_add D)

theorem ajClass_apply (E : Divisor ℂ 𝔽) : ajClass D E = ajClassFun D E := rfl

theorem ajClass_mapDomain (c : ℍ →₀ ℤ) :
    ajClass D (Finsupp.mapDomain D.pt c) = Submodule.Quotient.mk (aj N c) :=
  ajClassFun_eq D (x := 1) one_ne_zero fun v => by simp

theorem ajClass_eq_zero_of_mem_principal {E : Divisor ℂ 𝔽}
    (hE : E ∈ Divisor.principal (K := ℂ) (F := 𝔽)) : ajClass D E = 0 := by
  obtain ⟨x, hx, h⟩ := hE
  rw [ajClass_apply, ajClassFun_eq D (c := 0) hx fun v => by simp [h v], map_zero,
    Submodule.Quotient.mk_zero]

theorem degree_mapDomain_lift_eq_zero {E : Divisor ℂ 𝔽} (hE : Divisor.degree E = 0) :
    Divisor.degree (Finsupp.mapDomain D.pt (lift D E)) = 0 := by
  obtain ⟨Dx, hDx, hdeg⟩ := exists_div (fn D E) (fn_ne_zero D E)
  have : Finsupp.mapDomain D.pt (lift D E) = E - Dx := by
    ext v
    rw [Finsupp.coe_sub, Pi.sub_apply, decomp_spec D E v, hDx v]
    ring
  rw [this, map_sub, hE, hdeg, sub_zero]

end AJClass

section Pic0

variable {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N)

local notation "𝔽" => (laurentBaseChange ℂ (modularFunctionFieldFull N))
local notation "Λ" => ModularCurve.periodLattice N

def abelJacobi : Pic0 ℂ 𝔽 →+ Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) ⧸ Λ :=
  QuotientAddGroup.lift _ ((ajClass D).comp (Divisor.degZero (K := ℂ) (F := 𝔽)).subtype)
    (by
      intro E hE
      rw [AddSubgroup.mem_addSubgroupOf] at hE
      exact ajClass_eq_zero_of_mem_principal D hE)

theorem abelJacobi_mk (E : Divisor.degZero (K := ℂ) (F := 𝔽)) :
    abelJacobi D (Pic0.mk E) = ajClass D (E : Divisor ℂ 𝔽) :=
  rfl

theorem abelJacobi_injective : Function.Injective (abelJacobi D) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective z
  rw [abelJacobi_mk, ajClass_apply, ajClassFun, Submodule.Quotient.mk_eq_zero, aj_apply] at hz
  have hdeg := degree_mapDomain_lift_eq_zero D (E := (E : Divisor ℂ 𝔽)) E.2
  obtain ⟨y, hy, hEy⟩ :=
    ModularCurve.ComplexPlaceDictionary.isPrincipal_of_abelJacobi_mem_periodLattice D _ hdeg hz
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  refine ⟨fn D E * y, mul_ne_zero (fn_ne_zero D E) hy, fun v => ?_⟩
  rw [v.ord_mul (fn_ne_zero D E) hy, ← hEy v]
  exact decomp_spec D E v

def twoPoint (τ₀ τ₁ : ℍ) : Divisor.degZero (K := ℂ) (F := 𝔽) :=
  ⟨Finsupp.mapDomain D.pt (Finsupp.single τ₁ 1 - Finsupp.single τ₀ 1), by
    rw [Divisor.mem_degZero, degree_mapDomain_pt, Finsupp.sum_sub_index (fun _ _ _ => rfl)]
    simp⟩

theorem abelJacobi_twoPoint (τ₀ τ₁ : ℍ) :
    abelJacobi D (Pic0.mk (twoPoint D τ₀ τ₁)) =
      Submodule.Quotient.mk (ModularCurve.periodAlong N τ₀ τ₁) := by
  rw [abelJacobi_mk, twoPoint, ajClass_mapDomain, map_sub, aj_single, aj_single, one_smul,
    one_smul, periodAlong_eq_periodAlong_I_sub N τ₀ τ₁]

theorem abelJacobi_surjective : Function.Surjective (abelJacobi D) := by
  intro y
  obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective (ModularCurve.periodLattice N) y
  have key : AddSubgroup.closure (Set.range fun p : ℍ × ℍ => ModularCurve.periodAlong N p.1 p.2) ≤
      (abelJacobi D).range.comap (ModularCurve.periodLattice N).mkQ.toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨p, rfl⟩
    exact ⟨Pic0.mk (twoPoint D p.1 p.2), abelJacobi_twoPoint D p.1 p.2⟩
  have hφ : φ ∈ AddSubgroup.closure
      (Set.range fun p : ℍ × ℍ => ModularCurve.periodAlong N p.1 p.2) := by
    rw [ModularCurve.addSubgroupClosure_range_periodAlong_eq_top N]; trivial
  exact key hφ

theorem abelJacobi_hecke (hst : ModularCurve.PeriodLatticeHeckeStable N) (ℓ : ℕ) [Fact ℓ.Prime]
    (hα : ModularCurve.HeckeAlphaBarIntegral ℂ N ℓ) (hβ : ModularCurve.HeckeBetaBarIntegral ℂ N ℓ)
    [HasPrincipalDivisors ℂ (laurentBaseChange ℂ (modularFunctionFieldFull (N * ℓ)))]
    (hFI : FundamentalIdentityAlong ℂ (ModularCurve.heckeBetaBar ℂ N ℓ) hβ)
    (hfin : FiniteAlong ℂ (ModularCurve.heckeAlphaBar ℂ N ℓ))
    (hN : NormFormulaAlong ℂ (ModularCurve.heckeAlphaBar ℂ N ℓ) hfin)
    (z : Pic0 ℂ 𝔽) (φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
    (hz : abelJacobi D z = Submodule.Quotient.mk φ) :
    abelJacobi D (ModularCurve.heckePic0Bar hα hβ hFI hfin hN z) =
      Submodule.Quotient.mk
        (ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ⟨ℓ, Fact.out⟩) φ) := by
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective z
  rw [ModularCurve.heckePic0Bar, Pic0.correspondence_mk, abelJacobi_mk, Pic0.coe_degZeroCorrespondence]
  change ajClass D (ModularCurve.heckeDivBar hα hβ (E : Divisor ℂ 𝔽)) = _
  rw [abelJacobi_mk] at hz

  obtain ⟨Dx, hDx, hdegx⟩ := exists_div (fn D E) (fn_ne_zero D E)
  have hE : (E : Divisor ℂ 𝔽) = Dx + Finsupp.mapDomain D.pt (lift D E) := by
    ext v
    rw [Finsupp.coe_add, Pi.add_apply, decomp_spec D E v, hDx v]
  have hdeg := degree_mapDomain_lift_eq_zero D (E := (E : Divisor ℂ 𝔽)) E.2

  have hprin : ModularCurve.heckeDivBar hα hβ Dx ∈ Divisor.principal (K := ℂ) (F := 𝔽) :=
    Divisor.correspondence_mem_principal _ _ hβ hα hfin hN ⟨fn D E, fn_ne_zero D E, hDx⟩
  obtain ⟨c', hc', hmem⟩ :=
    ModularCurve.ComplexPlaceDictionary.exists_mapDomain_eq_heckeDivBar_abelJacobi_sub_mem_periodLattice
      D ℓ hα hβ (lift D E) hdeg
  rw [hE, map_add, map_add, ajClass_eq_zero_of_mem_principal D hprin, zero_add, ← hc',
    ajClass_mapDomain]

  rw [ajClass_apply, ajClassFun, Submodule.Quotient.eq] at hz
  rw [Submodule.Quotient.eq]
  have h1 : aj N c' - ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ⟨ℓ, Fact.out⟩) (aj N (lift D E))
      ∈ ModularCurve.periodLattice N := by
    simpa only [aj_apply] using hmem
  have h2 := hst ⟨ℓ, Fact.out⟩ _ hz
  rw [map_sub] at h2
  have := add_mem h1 h2
  convert this using 1
  abel

end Pic0

end ModularCurve.AbelJacobiIsoGlue
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice.ModularCurve P2MW.S_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice.ModularCurve.AbelJacobiIsoGlue"
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice.ModularCurve P2MW.S_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice.ModularCurve.AbelJacobiIsoGlue"

open ModularCurve.AbelJacobiIsoGlue in
theorem solution
    (N : ℕ) [NeZero N]
    (hinC : ∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.HeckeInputsAlong ℂ N ℓ)
    (hst : ModularCurve.PeriodLatticeHeckeStable N) :
    ∃ v : AlgebraicCurve.Pic0 ℂ
          (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) ≃+
        (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) ⧸ ModularCurve.periodLattice N),
      ∀ (ℓ : Nat.Primes)
        (z : AlgebraicCurve.Pic0 ℂ
          (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)))
        (φ : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
        v z = Submodule.Quotient.mk φ →
        v ((haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.heckeOperatorAlong ℂ N ℓ) z) =
          Submodule.Quotient.mk (ModularCurve.dualHeckeRep N (ModularCurve.heckeGen ℓ) φ) := by
  obtain ⟨D⟩ := ModularCurve.exists_complexPlaceDictionary N
  refine ⟨AddEquiv.ofBijective (abelJacobi D) ⟨abelJacobi_injective D, abelJacobi_surjective D⟩,
    ?_⟩
  intro ℓ z φ hz
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  obtain ⟨hα, hβ, hP, hfin, hFI, hN⟩ := hinC ℓ
  rw [AddEquiv.ofBijective_apply] at hz ⊢
  show abelJacobi D (ModularCurve.heckeOperatorAlong ℂ N ℓ z) = _
  rw [ModularCurve.heckeOperatorAlong_eq hα hβ hFI hfin hN]
  exact abelJacobi_hecke D hst ℓ hα hβ hFI hfin hN z φ hz

end S_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice
end P2MW
export P2MW.S_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice (solution)
