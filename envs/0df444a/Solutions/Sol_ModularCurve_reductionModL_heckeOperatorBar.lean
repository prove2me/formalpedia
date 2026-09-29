-- Prove2me | solution 1 for ModularCurve.reductionModL_heckeOperatorBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7fbb9482-8f2a-54bc-ace9-974c5304edb4

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeOperatorModL
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_frobeniusInputsModL
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_kroneckerCongruence_norm_heckeBetaBar
import Theorems.Thm_ModularCurve_finrankAlong_frobeniusModL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reductionModL_heckeOperatorBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen"
p2m_attr_erase "simp" "ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve ModularCurve

namespace HeckeReductionCompatSol

section ResidueAlgClosed

open IsLocalRing Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem isAlgClosed_residueField [IsAlgClosed L] : IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ (fun f hf_monic hf_irr => ?_)
  have hf_lifts : f ∈ lifts (residue A) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => residue_surjective (f.coeff n)
  obtain ⟨g, hg_map, -, hg_monic⟩ := lifts_and_degree_eq_and_monic hf_lifts hf_monic
  have hgL_deg : (g.map (algebraMap A L)).degree ≠ 0 := by
    rw [hg_monic.degree_map]
    intro h0
    have hg_nat : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
    have hf_deg : f.natDegree = 0 := by
      rw [← hg_map, hg_monic.natDegree_map]
      exact hg_nat
    have hf1 : f = 1 := (hf_monic.natDegree_eq_zero).mp hf_deg
    exact hf_irr.not_isUnit (by rw [hf1]; exact isUnit_one)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hgL_deg
  have hα_int : IsIntegral A α := by
    refine ⟨g, hg_monic, ?_⟩
    rwa [IsRoot.def, eval_map] at hα
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hα_int
  refine ⟨residue A a, ?_⟩
  have hga : g.eval a = 0 := by
    have : algebraMap A L (g.eval a) = 0 := by
      have hcomm : algebraMap A L (g.eval a) = (g.map (algebraMap A L)).eval α := by
        rw [← ha, eval_map, eval₂_hom]
      rw [hcomm]
      exact hα
    exact (map_eq_zero_iff _ Subtype.coe_injective).mp this
  have : f.eval (residue A a) = residue A (g.eval a) := by
    rw [← hg_map, eval_map, eval₂_hom]
  rw [this, hga, map_zero]

end ResidueAlgClosed

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem pullbackAlong_apply_eq_ord [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) {f : F} {D : Divisor K F} (hD : ∀ v, D v = v.ord f)
    (w : Place K F') : Divisor.pullbackAlong φ hφ D w = w.ord (φ f) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.pullback_apply_eq_ord hD w

theorem pushforwardAlong_apply_eq_ord (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin) {g : F'} (hg : g ≠ 0)
    {D : Divisor K F'} (hD : ∀ w, D w = w.ord g) (v : Place K F) :
    Divisor.pushforwardAlong φ hφ D v = v.ord (letI := algebraAlong φ; Algebra.norm F g) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  exact hN g hg D hD v

end Along

section Frobenius

variable {K : Type*} [Field K] {N ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem norm_frobeniusModL_eq (hrank : finrankAlong K (frobeniusModL K N ℓ) = ℓ)
    {f g : modularFunctionFieldFullC K N} (hg : frobeniusModL K N ℓ g = f ^ ℓ) :
    (letI := algebraAlong (frobeniusModL K N ℓ);
      Algebra.norm (modularFunctionFieldFullC K N) f) = g := by
  letI := algebraAlong (frobeniusModL K N ℓ)
  haveI : CharP (modularFunctionFieldFullC K N) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (modularFunctionFieldFullC K N)).injective ℓ
  have hpow : (Algebra.norm (modularFunctionFieldFullC K N) f) ^ ℓ = g ^ ℓ := by
    have h3 : Algebra.norm (modularFunctionFieldFullC K N)
        (algebraMap (modularFunctionFieldFullC K N) (modularFunctionFieldFullC K N) g) =
          g ^ finrankAlong K (frobeniusModL K N ℓ) :=
      Algebra.norm_algebraMap g
    calc (Algebra.norm (modularFunctionFieldFullC K N) f) ^ ℓ
        = Algebra.norm (modularFunctionFieldFullC K N) (f ^ ℓ) :=
          (map_pow (Algebra.norm (modularFunctionFieldFullC K N)) f ℓ).symm
      _ = Algebra.norm (modularFunctionFieldFullC K N)
            (algebraMap (modularFunctionFieldFullC K N) (modularFunctionFieldFullC K N) g) := by
          rw [show algebraMap (modularFunctionFieldFullC K N) (modularFunctionFieldFullC K N) g =
            frobeniusModL K N ℓ g from rfl, hg]
      _ = g ^ finrankAlong K (frobeniusModL K N ℓ) := h3
      _ = g ^ ℓ := by rw [hrank]
  exact frobenius_inj (modularFunctionFieldFullC K N) ℓ hpow

theorem coe_eq_coeffMap_frobenius_of_frobeniusModL_eq_pow [NeZero N]
    {f g : modularFunctionFieldFullC K N} (hg : frobeniusModL K N ℓ g = f ^ ℓ) :
    (g : LaurentSeries K) = coeffMap (frobenius K ℓ) (f : LaurentSeries K) := by
  haveI := charP_laurentSeriesC K ℓ
  apply qExpand_injective ℓ
  have h := congrArg (fun z : modularFunctionFieldFullC K N => (z : LaurentSeries K)) hg
  simp only [coe_frobeniusModL] at h
  rw [h, show ((f ^ ℓ : modularFunctionFieldFullC K N) : LaurentSeries K) =
      (f : LaurentSeries K) ^ ℓ from rfl,
    pow_char_eq_coeffMap_frobenius_qExpand ℓ (f : LaurentSeries K), coeffMap_qExpand]

end Frobenius

section Engine

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {N : ℕ}
variable {r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) →
  Place k (modularFunctionFieldFullC k N)}

theorem int_eq_zero_of_forall_dvd {a : ℤ} (h : ∀ n : ℕ, n ≠ 0 → (n : ℤ) ∣ a) : a = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h (a.natAbs + 1) (Nat.succ_ne_zero _))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)

theorem mapDomain_comm_of_agree
    (hgen : PrincipalGeneratedByIntegral A π N)
    (T : Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Divisor L (laurentBaseChange L (modularFunctionFieldFull N)))
    (Tbar : Divisor k (modularFunctionFieldFullC k N) →+ Divisor k (modularFunctionFieldFullC k N))
    (hagree : ∀ D ∈ integralPrincipalDivisors A π N,
      Finsupp.mapDomain r (T D) = Tbar (Finsupp.mapDomain r D))
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)),
      ∃ y : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)), n • y = x)
    {D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))}
    (hD : D ∈ Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))) :
    Finsupp.mapDomain r (T D) = Tbar (Finsupp.mapDomain r D) := by
  classical
  set δ : Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+
      Divisor k (modularFunctionFieldFullC k N) :=
    (Finsupp.mapDomain.addMonoidHom r).comp T - Tbar.comp (Finsupp.mapDomain.addMonoidHom r) with hδ
  have hδapp : ∀ E, δ E = Finsupp.mapDomain r (T E) - Tbar (Finsupp.mapDomain r E) := fun E => rfl

  have hδprin : ∀ E ∈ Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)),
      δ E = 0 := by
    intro E hE
    have hE' := hgen hE
    clear hE
    induction hE' using AddSubgroup.closure_induction with
    | mem E hE => rw [hδapp, hagree E hE, sub_self]
    | zero => exact map_zero δ
    | add E E' _ _ hE hE' => rw [map_add, hE, hE', add_zero]
    | neg E _ hE => rw [map_neg, hE, neg_zero]

  have hδD : δ D = 0 := by
    ext Q
    rw [Finsupp.zero_apply]
    refine int_eq_zero_of_forall_dvd fun n hn => ?_
    obtain ⟨y, hy⟩ := hdiv n hn (Pic0.mk ⟨D, hD⟩)
    obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
    have hmem : ((⟨D, hD⟩ : Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)))
        - n • E : Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))) ∈
          (Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))).addSubgroupOf
            (Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N))) := by
      rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.mk_nsmul]
      exact hy.symm
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_nsmul] at hmem
    have h0 := hδprin _ hmem
    rw [map_sub, map_nsmul, sub_eq_zero] at h0
    refine ⟨δ (E : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) Q, ?_⟩
    rw [h0, Finsupp.smul_apply, nsmul_eq_mul]
  rw [hδapp] at hδD
  exact sub_eq_zero.mp hδD

end Engine

section Agree

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
variable {r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) →
  Place k (modularFunctionFieldFullC k N)}

set_option maxHeartbeats 6400000 in

theorem agree_on_integral
    (hr : IsPlaceReductionAlong A π N r)
    (hα : HeckeAlphaBarIntegral L N ℓ) (hβ : HeckeBetaBarIntegral L N ℓ)
    [HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull (N * ℓ)))]
    (hfin : FiniteAlong L (heckeAlphaBar L N ℓ)) (hN : NormFormulaAlong L (heckeAlphaBar L N ℓ) hfin)
    [HasPrincipalDivisors k (modularFunctionFieldFullC k N)]
    (hfin' : FiniteAlong k (frobeniusModL k N ℓ))
    (hN' : NormFormulaAlong k (frobeniusModL k N ℓ) hfin')
    (hrank : finrankAlong k (frobeniusModL k N ℓ) = ℓ)
    (hK1 : ∀ (y : LaurentSeries A)
      (hy : coeffMap A.subtype y ∈ laurentBaseChange L (modularFunctionFieldFull N)),
      ∃ y' : LaurentSeries A,
        coeffMap A.subtype y' =
          ((letI := algebraAlong (heckeAlphaBar L N ℓ)
            Algebra.norm (laurentBaseChange L (modularFunctionFieldFull N))
              (heckeBetaBar L N ℓ ⟨coeffMap A.subtype y, hy⟩) :
              laurentBaseChange L (modularFunctionFieldFull N)) : LaurentSeries L) ∧
        coeffMap π y' = coeffMap (frobenius k ℓ) (coeffMap π y) * qExpand k ℓ (coeffMap π y))
    {D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N))}
    (hD : D ∈ integralPrincipalDivisors A π N) :
    Finsupp.mapDomain r (heckeDivBar hα hβ D) = heckeDivOperatorModL k N ℓ (Finsupp.mapDomain r D) := by
  obtain ⟨y, hy, hyk, hne, hDy⟩ := hD

  set f : laurentBaseChange L (modularFunctionFieldFull N) := ⟨coeffMap A.subtype y, hy⟩ with hf_def
  set fbar : modularFunctionFieldFullC k N := ⟨coeffMap π y, hyk⟩ with hfbar_def
  have hfbar : fbar ≠ 0 := fun h => hne (congrArg Subtype.val h)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hne (map_zero _)
  have hf : f ≠ 0 := by
    intro h
    apply hy0
    have h' : coeffMap A.subtype y = 0 := congrArg Subtype.val h
    ext n
    have := congrArg (fun s : LaurentSeries L => s.coeff n) h'
    simp only [coeffMap_coeff] at this
    simpa using this
  have hβf : heckeBetaBar L N ℓ f ≠ 0 := (map_ne_zero _).mpr hf

  have hpull : ∀ w, Divisor.pullbackAlong (heckeBetaBar L N ℓ) hβ D w = w.ord (heckeBetaBar L N ℓ f) :=
    fun w => pullbackAlong_apply_eq_ord (heckeBetaBar L N ℓ) hβ hDy w
  have hT : ∀ v, heckeDivBar hα hβ D v =
      v.ord (letI := algebraAlong (heckeAlphaBar L N ℓ);
        Algebra.norm (laurentBaseChange L (modularFunctionFieldFull N)) (heckeBetaBar L N ℓ f)) := by
    intro v
    rw [heckeDivBar, Divisor.correspondence_apply]
    exact pushforwardAlong_apply_eq_ord (heckeAlphaBar L N ℓ) hα hfin hN hβf hpull v

  obtain ⟨y', hy'1, hy'2⟩ := hK1 y hy
  have hy'mem : coeffMap A.subtype y' ∈ laurentBaseChange L (modularFunctionFieldFull N) := by
    rw [hy'1]; exact SetLike.coe_mem _
  have hT' : ∀ v, heckeDivBar hα hβ D v =
      v.ord (⟨coeffMap A.subtype y', hy'mem⟩ : laurentBaseChange L (modularFunctionFieldFull N)) := by
    intro v
    rw [hT v]
    congr 1
    exact Subtype.ext hy'1.symm

  obtain ⟨g, hg⟩ := exists_frobeniusModL_eq_pow k N ℓ fbar
  have hgcoe : (g : LaurentSeries k) = coeffMap (frobenius k ℓ) (coeffMap π y) :=
    coe_eq_coeffMap_frobenius_of_frobeniusModL_eq_pow hg
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hg
    exact pow_ne_zero ℓ hfbar hg.symm
  have hFr0 : frobeniusModL k N ℓ fbar ≠ 0 := (map_ne_zero _).mpr hfbar
  have hprod : coeffMap π y' = ((g * frobeniusModL k N ℓ fbar : modularFunctionFieldFullC k N) :
      LaurentSeries k) := by
    rw [hy'2, ← hgcoe]
    rfl
  have hy'k : coeffMap π y' ∈ modularFunctionFieldFullC k N := by
    rw [hprod]; exact SetLike.coe_mem _
  have hy'ne : coeffMap π y' ≠ 0 := by
    rw [hprod]
    exact fun h => (mul_ne_zero hg0 hFr0) (Subtype.ext h)
  have hy'eq : (⟨coeffMap π y', hy'k⟩ : modularFunctionFieldFullC k N) = g * frobeniusModL k N ℓ fbar :=
    Subtype.ext hprod

  have hup : ∀ Q, Finsupp.mapDomain r (heckeDivBar hα hβ D) Q =
      Q.ord g + Q.ord (frobeniusModL k N ℓ fbar) := by
    intro Q
    rw [hr.2 y' hy'mem hy'k hy'ne (heckeDivBar hα hβ D) hT' Q, hy'eq, Q.ord_mul hg0 hFr0]
  have hdown : ∀ Q, Finsupp.mapDomain r D Q = Q.ord fbar := hr.2 y hy hyk hne D hDy

  have hpull' : ∀ Q, frobeniusDivPullbackModL k N ℓ (Finsupp.mapDomain r D) Q =
      Q.ord (frobeniusModL k N ℓ fbar) := fun Q =>
    pullbackAlong_apply_eq_ord (frobeniusModL k N ℓ) (frobeniusModL_isIntegral k N ℓ) hdown Q
  have hpush' : ∀ Q, frobeniusDivPushforwardModL k N ℓ (Finsupp.mapDomain r D) Q = Q.ord g := by
    intro Q
    have h1 := pushforwardAlong_apply_eq_ord (frobeniusModL k N ℓ) (frobeniusModL_isIntegral k N ℓ)
      hfin' hN' hfbar hdown Q
    have h2 := norm_frobeniusModL_eq (K := k) (N := N) hrank hg
    rw [h2] at h1
    exact h1

  ext Q
  rw [hup Q, heckeDivOperatorModL_apply, Finsupp.add_apply, hpush' Q, hpull' Q]

end Agree

end HeckeReductionCompatSol

open HeckeReductionCompatSol in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ] (h : ModularCurve.ReductionInputsModL A N)
    (z : ModularCurve.JZero N) :
    ModularCurve.reductionModL A N (ModularCurve.heckeOperatorBar N ⟨ℓ, Fact.out⟩ z) =
      ModularCurve.heckeOperatorModL (IsLocalRing.ResidueField A) N ℓ
        (ModularCurve.reductionModL A N z) := by

  have hin : HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ := heckeInputsAll N ⟨ℓ, Fact.out⟩
  obtain ⟨hα, hβ, hP, hfin, hFI, hN⟩ := hin
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := isAlgClosed_residueField A
  obtain ⟨hPk, hfin', hFI', hN'⟩ := frobeniusInputsModL (IsLocalRing.ResidueField A) (ℓ := ℓ) N
  haveI := hP
  haveI := hPk
  have hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ y : Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N), n • y = x := fun n hn x =>
    haveI := isCurveOver_modularFunctionFieldBar N
    ModularCurve.JZero.divisible N n hn x

  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  rw [heckeOperatorBar_apply]
  change reductionModL A N (heckeOperatorAlong (AlgebraicClosure ℚ) N ℓ (Pic0.mk D)) = _
  rw [heckeOperatorAlong_eq hα hβ hFI hfin hN, heckePic0Bar, Pic0.correspondence_mk,
    reductionModL_mk h, reductionModL_mk h, heckeOperatorModL_mk hfin' hFI' hN']
  congr 1
  apply Subtype.ext
  rw [coe_reductionDegZeroAlong, Pic0.coe_degZeroCorrespondence, coe_frobeniusDegZero_add,
    coe_reductionDegZeroAlong]

  exact mapDomain_comm_of_agree h.choose_spec.2 (heckeDivBar hα hβ)
    (heckeDivOperatorModL (IsLocalRing.ResidueField A) N ℓ)
    (fun E hE => agree_on_integral (isPlaceReductionModL_placeReductionModL h) hα hβ hfin hN
      hfin' hN' (finrankAlong_frobeniusModL (IsLocalRing.ResidueField A) N)
      (fun y hy => kroneckerCongruence_norm_heckeBetaBar N hℓN A y hy) hE)
    hdiv D.2

end
end S_ModularCurve_reductionModL_heckeOperatorBar
end P2MW
export P2MW.S_ModularCurve_reductionModL_heckeOperatorBar (solution)
