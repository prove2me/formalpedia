-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/889f0df3-0838-5b52-b31d-231d5f1c3928

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_divisorLawFst_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawFst_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_cuspLawInfty_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ValuationSubring.instIsAlgClosedResidueField ModularCurve.numberField_of_finiteDimensional ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.symPoly_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable section

namespace P2mWs18V56

section Generic

theorem mapDomain_apply_eq_sum {ι κ : Type*} [DecidableEq κ] (h : ι → κ) (D : ι →₀ ℤ) (w : κ) :
    Finsupp.mapDomain h D w = ∑ V ∈ D.support, (if h V = w then D V else 0) := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [Finsupp.single_apply]

theorem mapDomain_eq_zero_of_forall {ι κ : Type*} (h : ι → κ) (D : ι →₀ ℤ) (w : κ)
    (hz : ∀ V, h V = w → D V = 0) : Finsupp.mapDomain h D w = 0 := by
  classical
  rw [mapDomain_apply_eq_sum]
  refine Finset.sum_eq_zero fun V _ => ?_
  split_ifs with hV
  · exact hz V hV
  · rfl

theorem inv_mem_of_isUnit_vs {F : Type*} [Field F] (S : ValuationSubring F) {g : F} (h : g ∈ S)
    (hu : IsUnit (⟨g, h⟩ : ↥S)) : g ≠ 0 ∧ g⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hv' : g * (v : F) = 1 := congrArg Subtype.val hv
  have hg0 : g ≠ 0 := fun h0 => by rw [h0, zero_mul] at hv'; exact zero_ne_one hv'
  exact ⟨hg0, (eq_inv_of_mul_eq_one_right hv') ▸ v.2⟩

variable {L : Type*} [Field L] {A' : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A') Fbar]

theorem exists_inv_mem_residue_ne_zero (S : RegularProlongation A' F Fbar) {g : F} (h : g ∈ S.integers)
    (hres : S.residue ⟨g, h⟩ ≠ 0) : ∃ h' : g⁻¹ ∈ S.integers, S.residue ⟨g⁻¹, h'⟩ ≠ 0 := by
  obtain ⟨hg0, hinv⟩ := inv_mem_of_isUnit_vs S.integers h (S.isUnit_of_residue_ne_zero hres)
  refine ⟨hinv, fun h0 => ?_⟩
  have hmul : (⟨g, h⟩ : ↥S.integers) * ⟨g⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hg0)
  have := congrArg S.residue hmul
  rw [map_mul, h0, mul_zero, map_one] at this
  exact zero_ne_one this

theorem residue_mul_residue_inv (S : RegularProlongation A' F Fbar) {g : F} (h : g ∈ S.integers)
    (h' : g⁻¹ ∈ S.integers) (hg0 : g ≠ 0) : S.residue ⟨g, h⟩ * S.residue ⟨g⁻¹, h'⟩ = 1 := by
  have hmul : (⟨g, h⟩ : ↥S.integers) * ⟨g⁻¹, h'⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hg0)
  rw [← map_mul, hmul, map_one]

theorem exists_residue_mul_pow (S : RegularProlongation A' F Fbar) {f e : F} (hf : f ∈ S.integers)
    (he : e ∈ S.integers) (m : ℕ) :
    ∃ h : f * e ^ m ∈ S.integers, S.residue ⟨f * e ^ m, h⟩ = S.residue ⟨f, hf⟩ * S.residue ⟨e, he⟩ ^ m := by
  refine ⟨mul_mem hf (pow_mem he m), ?_⟩
  rw [← map_pow, ← map_mul]
  exact congrArg S.residue (Subtype.ext (by simp))

theorem ord_pow_nat {K : Type*} [Field K] [Algebra K F] (v : Place K F) (f : F) (m : ℕ) :
    v.ord (f ^ m) = (m : ℤ) * v.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]

end Generic

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
  (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
  (hreg : R.RegularityLaw W) (hO : R.OrderLawFixed)

local notation "𝔽" => modularFunctionFieldBar (N * q)
local notation "Pl0" => Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
local notation "Plk" => Place k (modularFunctionFieldC k N)

include hqN hW in
theorem fixed_of_mem_W {w : Plk} (hw : w ∈ W) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w :=
  frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr w ((hW w).1 hw)

include hW in
omit [Fact q.Prime] [CharP k q] [IsAlgClosed k] in
theorem affine_of_mem_W {w : Plk} (hw : w ∈ W) : IsAffineGeomPlace k N w := ((hW w).1 hw).2.1

omit [IsAlgClosed k] [DecidableEq k] in

theorem not_isStrictFst_of_fixed {V : Pl0}
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) = P.reduceFst V) :
    ¬ P.IsStrictFst V := fun h => h.2 hfix

omit [IsAlgClosed k] [DecidableEq k] in

theorem not_isStrictSnd_of_fixed {V : Pl0}
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V)) = P.reduceFst V) :
    ¬ P.IsStrictSnd V := by
  rintro ⟨h1, h2⟩
  apply h2
  apply frobOnPlacesGeomLevel_injective k N data hKr
  rw [← h1]
  exact hfix

omit [IsAlgClosed k] [DecidableEq k] in
theorem residue_ne_zero_of_residue₁_ne_zero {f : 𝔽} {h₁ : f ∈ R.R₁.integers} (h : R.residue₁ ⟨f, h₁⟩ ≠ 0) :
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 := fun h0 => h (by rw [residue₁_apply, h0, map_zero])

omit [IsAlgClosed k] [DecidableEq k] in
theorem residue₁_ne_zero_of_residue_ne_zero {f : 𝔽} {h₁ : f ∈ R.R₁.integers} (h : R.R₁.residue ⟨f, h₁⟩ ≠ 0) :
    R.residue₁ ⟨f, h₁⟩ ≠ 0 := by
  rw [residue₁_apply]
  exact (map_ne_zero R.ι).mpr h

omit [IsAlgClosed k] [DecidableEq k] in
theorem residue_ne_zero_of_residue₂_ne_zero {f : 𝔽} {h₂ : f ∈ R.R₂.integers} (h : R.residue₂ ⟨f, h₂⟩ ≠ 0) :
    R.R₂.residue ⟨f, h₂⟩ ≠ 0 := fun h0 => h (by rw [residue₂_apply, h0, map_zero])

omit [IsAlgClosed k] [DecidableEq k] in
theorem residue₂_ne_zero_of_residue_ne_zero {f : 𝔽} {h₂ : f ∈ R.R₂.integers} (h : R.R₂.residue ⟨f, h₂⟩ ≠ 0) :
    R.residue₂ ⟨f, h₂⟩ ≠ 0 := by
  rw [residue₂_apply]
  exact (map_ne_zero R.ι).mpr h

omit [IsAlgClosed k] [DecidableEq k] in
theorem forall_ord_nonneg_of_mem_nodeIntegers {w : Plk} {g : 𝔽} (hg : g ∈ R.nodeIntegers w) :
    ∀ V : Pl0, P.reduceFst V = w → 0 ≤ V.ord g :=
  fun _ hV => R.ord_nonneg_of_mem_nodeIntegers hg hV

include hqN hW hreg in

theorem residueFst_mem_of_mem_nodeIntegers {w : Plk} (hw : w ∈ W) (g : ↥(R.nodeIntegers w)) :
    (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring := by
  have hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w :=
    fixed_of_mem_W hqN W hW hw
  have haff : IsAffineGeomPlace k N w := affine_of_mem_W W hW hw
  have h := (hreg.1 (g : 𝔽) g.2.1 g.2.2.1 w hfix haff (forall_ord_nonneg_of_mem_nodeIntegers R g.2)).1
  by_cases h0 : (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) = 0
  · rw [h0]; exact zero_mem _
  · rw [nodeResidue₁_apply] at h0 ⊢
    exact w.mem_of_ord_nonneg h0 (h h0)

include hqN hW hreg in

theorem ord_residueFst_eq_zero_of_isUnit {w : Plk} (hw : w ∈ W) {g : ↥(R.nodeIntegers w)} (hu : IsUnit g) :
    w.ord (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) = 0 := by
  obtain ⟨g', hg'⟩ := hu.exists_right_inv
  have h1 := w.ord_nonneg_of_mem (residueFst_mem_of_mem_nodeIntegers R hqN W hW hreg hw g)
  have h2 := w.ord_nonneg_of_mem (residueFst_mem_of_mem_nodeIntegers R hqN W hW hreg hw g')
  have hval : (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) * R.nodeResidue₁ w g' = 1 := by
    rw [← map_mul, hg', map_one]
  have hg0 : (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hval; exact zero_ne_one hval
  have hg0' : (R.nodeResidue₁ w g' : ↥(modularFunctionFieldC k N)) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hval; exact zero_ne_one hval
  have := w.ord_mul hg0 hg0'
  rw [hval, Place.ord_one] at this
  omega

def MoverLike (e : 𝔽) : Prop :=
  e ≠ 0 ∧ (∃ h₁ : e ∈ R.R₁.integers, R.R₁.residue ⟨e, h₁⟩ ≠ 0) ∧
    (∃ h₂ : e ∈ R.R₂.integers, R.R₂.residue ⟨e, h₂⟩ ≠ 0) ∧
    ∀ w ∈ W, ∀ V : Pl0, P.reduceFst V = w → V.ord e = 0

omit [IsAlgClosed k] [DecidableEq k] in
theorem MoverLike.inv {e : 𝔽} (he : MoverLike R W e) : MoverLike R W e⁻¹ := by
  obtain ⟨he0, ⟨h₁, hr₁⟩, ⟨h₂, hr₂⟩, hV⟩ := he
  refine ⟨inv_ne_zero he0, exists_inv_mem_residue_ne_zero R.R₁ h₁ hr₁,
    exists_inv_mem_residue_ne_zero R.R₂ h₂ hr₂, fun w hw V hVw => ?_⟩
  rw [Place.ord_inv, hV w hw V hVw, neg_zero]

omit [IsAlgClosed k] [DecidableEq k] in
theorem MoverLike.mem_nodeIntegers {e : 𝔽} (he : MoverLike R W e) {w : Plk} (hw : w ∈ W) :
    e ∈ R.nodeIntegers w := by
  obtain ⟨he0, ⟨h₁, _⟩, ⟨h₂, _⟩, hV⟩ := he
  exact ⟨h₁, h₂, fun V hVw => V.mem_of_ord_nonneg he0 (hV w hw V hVw).ge⟩

omit [IsAlgClosed k] [DecidableEq k] in
theorem MoverLike.isUnit {e : 𝔽} (he : MoverLike R W e) {w : Plk} (hw : w ∈ W) :
    IsUnit (⟨e, he.mem_nodeIntegers R W hw⟩ : ↥(R.nodeIntegers w)) := by
  refine isUnit_iff_exists_inv.mpr ⟨⟨e⁻¹, (he.inv R W).mem_nodeIntegers R W hw⟩, ?_⟩
  exact Subtype.ext (mul_inv_cancel₀ he.1)

include hqN hW hreg in

theorem MoverLike.ord_residue₁_eq_zero {e : 𝔽} (he : MoverLike R W e) {w : Plk} (hw : w ∈ W)
    (h₁ : e ∈ R.R₁.integers) :
    w.ord (R.residue₁ ⟨e, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
  have := ord_residueFst_eq_zero_of_isUnit R hqN W hW hreg hw (he.isUnit R W hw)
  rw [nodeResidue₁_apply] at this
  exact this

def Good (y : Plk → 𝔽) (n : Plk → ℕ) (f : 𝔽) : Prop :=
  f ≠ 0 ∧
    (∃ h₁ : f ∈ R.R₁.integers, R.R₁.residue ⟨f, h₁⟩ ≠ 0 ∧
      ∀ (w : Plk) (_ : w ∈ W), w.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = -((n w : ℕ) : ℤ)) ∧
    (∀ (w : Plk) (_ : w ∈ W), ∃ h : f * y w ^ n w ∈ R.nodeIntegers w,
      IsUnit (⟨f * y w ^ n w, h⟩ : ↥(R.nodeIntegers w))) ∧
    (∀ w ∈ W, ∀ V : Pl0, P.reduceFst V = w → V.ord f = 0)

include hqN hW hreg in

theorem good_mul_pow {y : Plk → 𝔽} {n : Plk → ℕ} {f : 𝔽} (hf : Good R W y n f) {e : 𝔽} (he : MoverLike R W e)
    (m : ℕ) : Good R W y n (f * e ^ m) := by
  obtain ⟨hf0, ⟨hf₁, hfr, hford⟩, hfu, hfV⟩ := hf
  have he' := he
  obtain ⟨he0, ⟨he₁, her⟩, ⟨he₂, _⟩, heV⟩ := he'
  have hem0 : e ^ m ≠ 0 := pow_ne_zero m he0
  obtain ⟨hfe₁, hres⟩ := exists_residue_mul_pow R.R₁ hf₁ he₁ m
  refine ⟨mul_ne_zero hf0 hem0, ⟨hfe₁, ?_, fun w hw => ?_⟩, fun w hw => ?_, fun w hw V hVw => ?_⟩
  ·
    rw [hres]
    exact mul_ne_zero hfr (pow_ne_zero m her)
  ·
    have hmul : (R.residue₁ ⟨f * e ^ m, hfe₁⟩ : ↥(modularFunctionFieldC k N))
        = R.residue₁ ⟨f, hf₁⟩ * R.residue₁ ⟨e, he₁⟩ ^ m := by
      simp only [residue₁_apply]
      rw [hres, map_mul, map_pow]
    have hr0 : (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 :=
      residue₁_ne_zero_of_residue_ne_zero R hfr
    have he0' : (R.residue₁ ⟨e, he₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 :=
      residue₁_ne_zero_of_residue_ne_zero R her
    rw [hmul, w.ord_mul hr0 (pow_ne_zero m he0'), ord_pow_nat, hford w hw,
      he.ord_residue₁_eq_zero R hqN W hW hreg hw he₁, mul_zero, add_zero]
  ·
    obtain ⟨hmem, hu⟩ := hfu w hw
    have heN : e ∈ R.nodeIntegers w := he.mem_nodeIntegers R W hw
    let U : ↥(R.nodeIntegers w) := ⟨f * y w ^ n w, hmem⟩ * ⟨e, heN⟩ ^ m
    have hUval : (U : 𝔽) = f * e ^ m * y w ^ n w := by
      simp only [U, Subring.coe_mul, SubmonoidClass.coe_pow]
      ring
    have hmem' : f * e ^ m * y w ^ n w ∈ R.nodeIntegers w := by rw [← hUval]; exact U.2
    refine ⟨hmem', ?_⟩
    have hU : IsUnit U := hu.mul ((he.isUnit R W hw).pow m)
    have hEq : (⟨f * e ^ m * y w ^ n w, hmem'⟩ : ↥(R.nodeIntegers w)) = U := Subtype.ext hUval.symm
    rw [hEq]
    exact hU
  ·
    rw [V.ord_mul hf0 hem0, ord_pow_nat, hfV w hw V hVw, heV w hw V hVw, mul_zero, add_zero]

section Clearing

variable (hmodel : R.IsModel) (hval : R.NodeValueLaw W)
  (T : Finset (Place k (modularFunctionFieldC k N))) (hTW : ∀ t ∈ T, t ∉ W)

include hqN hW hreg hO hmodel hval hTW in

theorem exists_mover {V₀ : Pl0} (hV₀ : P.reduceFst V₀ ∈ T) :
    ∃ g : 𝔽, MoverLike R W g ∧ V₀.ord g = 1 ∧ ∀ V : Pl0, V ≠ V₀ → P.reduceFst V ∈ T → V.ord g = 0 := by
  classical
  have hT : ∀ t ∈ T, t ∉ ssPlaces q N k := fun t ht hss => hTW t ht ((hW t).2 hss)
  obtain ⟨g, D, hg0, ⟨h₁, h₂, hr₁, hr₂⟩, hD, hDV₀, hstrict, hnotT, -⟩ :=
    exists_ord_eq_one_forall_isStrict_reduceFst_reduceSnd_notMem_forall_inertia_smul_eq_of_isModel q A N k red data
      hKr hα hβ hqN P W hW R hmodel hreg hval hO T hT V₀ (Or.inl hV₀)
  refine ⟨g, ⟨hg0, ⟨h₁, residue_ne_zero_of_residue₁_ne_zero R hr₁⟩, ⟨h₂, residue_ne_zero_of_residue₂_ne_zero R hr₂⟩,
    fun w hw V hVw => ?_⟩, ?_, fun V hne hVT => ?_⟩
  ·
    rw [← hD]
    by_contra hne0
    have hVs : V ∈ D.support := Finsupp.mem_support_iff.mpr hne0
    have hVne : V ≠ V₀ := by
      rintro rfl
      exact hTW _ hV₀ (by rw [hVw]; exact hw)
    have hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V))
        = P.reduceFst V := by
      rw [hVw]; exact fixed_of_mem_W hqN W hW hw
    rcases hstrict V hVs hVne with hs | hs
    · exact not_isStrictFst_of_fixed hfix hs
    · exact not_isStrictSnd_of_fixed hfix hs
  · rw [← hD]; exact hDV₀
  · rw [← hD]
    by_contra hne0
    exact (hnotT V (Finsupp.mem_support_iff.mpr hne0) hne).1 hVT

include hqN hW hreg in

theorem clear_step {y : Plk → 𝔽} {n : Plk → ℕ} {f : 𝔽} (hf : Good R W y n f) {e : 𝔽} (he : MoverLike R W e)
    {V₀ : Pl0} (heT : ∀ V : Pl0, V ≠ V₀ → P.reduceFst V ∈ T → V.ord e = 0) (m : ℕ)
    (hcancel : V₀.ord f + (m : ℤ) * V₀.ord e = 0) :
    Good R W y n (f * e ^ m) ∧ V₀.ord (f * e ^ m) = 0 ∧
      ∀ V : Pl0, V ≠ V₀ → P.reduceFst V ∈ T → V.ord (f * e ^ m) = V.ord f := by
  have hem0 : e ^ m ≠ 0 := pow_ne_zero m he.1
  refine ⟨good_mul_pow R hqN W hW hreg hf he m, ?_, fun V hne hVT => ?_⟩
  · rw [V₀.ord_mul hf.1 hem0, ord_pow_nat, hcancel]
  · rw [V.ord_mul hf.1 hem0, ord_pow_nat, heT V hne hVT, mul_zero, add_zero]

include hqN hW hreg hO hmodel hval hTW in

theorem exists_good_forall_ord_eq_zero {y : Plk → 𝔽} {n : Plk → ℕ} :
    ∀ (m : ℕ) (f : 𝔽), Good R W y n f →
      (∃ S : Finset Pl0, S.card ≤ m ∧ ∀ V : Pl0, P.reduceFst V ∈ T → V.ord f ≠ 0 → V ∈ S) →
      ∃ f' : 𝔽, Good R W y n f' ∧ ∀ V : Pl0, P.reduceFst V ∈ T → V.ord f' = 0 := by
  classical
  intro m
  induction m with
  | zero =>
    rintro f hf ⟨S, hS, hSf⟩
    refine ⟨f, hf, fun V hVT => ?_⟩
    by_contra hne
    have := hSf V hVT hne
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hS)] at this
    simp at this
  | succ m ih =>
    rintro f hf ⟨S, hS, hSf⟩
    by_cases hclear : ∀ V : Pl0, P.reduceFst V ∈ T → V.ord f = 0
    · exact ⟨f, hf, hclear⟩
    push Not at hclear
    obtain ⟨V₀, hV₀T, hV₀⟩ := hclear
    obtain ⟨g, hg, hgV₀, hgT⟩ := exists_mover R hqN W hW hreg hO hmodel hval T hTW hV₀T

    have key : ∃ (e : 𝔽) (m' : ℕ), MoverLike R W e ∧ (∀ V : Pl0, V ≠ V₀ → P.reduceFst V ∈ T → V.ord e = 0) ∧
        V₀.ord f + (m' : ℤ) * V₀.ord e = 0 := by
      rcases Int.eq_nat_or_neg (V₀.ord f) with ⟨m', hm' | hm'⟩
      · refine ⟨g⁻¹, m', hg.inv R W, fun V hne hVT => ?_, ?_⟩
        · rw [Place.ord_inv, hgT V hne hVT, neg_zero]
        · rw [Place.ord_inv, hgV₀, hm']; ring
      · exact ⟨g, m', hg, hgT, by rw [hgV₀, hm']; ring⟩
    obtain ⟨e, m', he, heT, hcancel⟩ := key
    obtain ⟨hf', hV₀', hother⟩ := clear_step R hqN W hW hreg T hf he heT m' hcancel
    refine ih (f * e ^ m') hf' ⟨S.erase V₀, ?_, fun V hVT hne => ?_⟩
    · have hV₀S : V₀ ∈ S := hSf V₀ hV₀T hV₀
      rw [Finset.card_erase_of_mem hV₀S]
      omega
    · have hVne : V ≠ V₀ := by rintro rfl; exact hne hV₀'
      rw [hother V hVne hVT] at hne
      exact Finset.mem_erase.mpr ⟨hVne, hSf V hVT hne⟩

end Clearing

section OffW

variable (hmodel : R.IsModel)
  (Z : Finset (Place k (modularFunctionFieldC k N)))
  (hZ : ∀ v : Place k (modularFunctionFieldC k N),
    v ∈ Z ↔ frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)

omit [IsAlgClosed k] [DecidableEq k] in

theorem mapDomain_fstDiv_eq_zero {f : 𝔽} (G : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (hG : ∀ V, G V = V.ord f) {v : Plk} (hzv : ∀ V : Pl0, P.reduceFst V = v → V.ord f = 0) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv G) v = 0 := by
  classical
  refine mapDomain_eq_zero_of_forall _ _ _ fun V hV => ?_
  rw [PlaceSpecialization.fstDiv, Finsupp.filter_apply, hG, hzv V hV, ite_self]

include hqN hW hreg in

theorem ord_residue₁_eq_zero_of_fixed_affine {f : 𝔽} (hf0 : f ≠ 0) (h₁ : f ∈ R.R₁.integers)
    (hres : R.R₁.residue ⟨f, h₁⟩ ≠ 0) {v : Plk}
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (haff : IsAffineGeomPlace k N v) (hv : v ∉ W) (hzv : ∀ V : Pl0, P.reduceFst V = v → V.ord f = 0) :
    v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
  have hge : 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) :=
    regularityLawFst_oneSided hqN P W hW R hreg f h₁ hres v hfix haff hv (fun V hV => (hzv V hV).ge)
  obtain ⟨h₁', hres'⟩ := exists_inv_mem_residue_ne_zero R.R₁ h₁ hres
  have hge' : 0 ≤ v.ord (R.residue₁ ⟨f⁻¹, h₁'⟩ : ↥(modularFunctionFieldC k N)) :=
    regularityLawFst_oneSided hqN P W hW R hreg f⁻¹ h₁' hres' v hfix haff hv
      (fun V hV => le_of_eq (by rw [Place.ord_inv, hzv V hV, neg_zero]))
  have hmul : (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) * R.residue₁ ⟨f⁻¹, h₁'⟩ = 1 := by
    simp only [residue₁_apply]
    rw [← map_mul, residue_mul_residue_inv R.R₁ h₁ h₁' hf0, map_one]
  have hr0 : (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := residue₁_ne_zero_of_residue_ne_zero R hres
  have hr0' : (R.residue₁ ⟨f⁻¹, h₁'⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 :=
    residue₁_ne_zero_of_residue_ne_zero R hres'
  have := v.ord_mul hr0 hr0'
  rw [hmul, Place.ord_one] at this
  omega

include hqN hmodel in
omit [IsAlgClosed k] [DecidableEq k] in

theorem ord_residue₁_eq_zero_of_not_affine {f : 𝔽} (h₁ : f ∈ R.R₁.integers) (hres : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (G : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hG : ∀ V, G V = V.ord f) {v : Plk}
    (haff : ¬ IsAffineGeomPlace k N v) (hzv : ∀ V : Pl0, P.reduceFst V = v → V.ord f = 0) :
    v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
  classical
  obtain ⟨C, hC, hCv⟩ :=
    (exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffineGeomPlace hqN P v haff).1
  have hlaw := cuspLawInfty_oneSided hqN P R hmodel f h₁ hres G hG C hC
  rw [hCv] at hlaw
  rw [← hlaw]
  refine mapDomain_eq_zero_of_forall _ _ _ fun V hV => ?_
  rw [Finsupp.filter_apply, hG, hzv V hV, ite_self]

include hqN hW hreg hmodel hZ in

theorem mapDomain_fstDiv_eq_ord_residue₁ {f : 𝔽} (hf0 : f ≠ 0) (h₁ : f ∈ R.R₁.integers)
    (hres : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (hzero : ∀ z ∈ Z, z ∉ W → ∀ V : Pl0, P.reduceFst V = z → V.ord f = 0)
    (G : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hG : ∀ V, G V = V.ord f)
    (v : Plk) (hv : v ∉ W) :
    Finsupp.mapDomain P.reduceFst (P.fstDiv G) v = v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) := by
  by_cases hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v
  ·
    have hzv : ∀ V : Pl0, P.reduceFst V = v → V.ord f = 0 := hzero v ((hZ v).2 hfix) hv
    rw [mapDomain_fstDiv_eq_zero G hG hzv]
    by_cases haff : IsAffineGeomPlace k N v
    · exact (ord_residue₁_eq_zero_of_fixed_affine R hqN W hW hreg hf0 h₁ hres hfix haff hv hzv).symm
    · exact (ord_residue₁_eq_zero_of_not_affine R hqN hmodel h₁ hres G hG haff hzv).symm
  ·
    exact divisorLawFst_oneSided hqN P R hmodel f h₁ hres G hG v hfix

end OffW

end P2mWs18V56

end

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W) (hO : R.OrderLawFixed)
    (Z : Finset (Place k (modularFunctionFieldC k N)))
    (hZ : ∀ v : Place k (modularFunctionFieldC k N),
      v ∈ Z ↔ frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (y : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldBar (N * q)))
    (n : Place k (modularFunctionFieldC k N) → ℕ)
    (hyS : ∀ w ∈ W, y w ∈ R.nodeIntegers w)
    (hy₁ : ∀ w ∈ W, ∃ h : y w ∈ R.R₁.integers, R.R₁.residue ⟨y w, h⟩ ≠ 0)
    (hyV : ∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w → V.ord (y w) = 0)
    (hy_ord1 : ∀ (w) (_ : w ∈ W) (h : y w ∈ R.R₁.integers),
      w.ord (R.residue₁ ⟨y w, h⟩ : ↥(modularFunctionFieldC k N)) = 1)
    (hvert : ∀ w ∈ W, ∀ w' ∈ W,
      ∃ h : y w ^ n w * (y w' ^ n w')⁻¹ ∈ R.R₂.integers, R.R₂.residue ⟨y w ^ n w * (y w' ^ n w')⁻¹, h⟩ ≠ 0) :
    ∃ f : ↥(modularFunctionFieldBar (N * q)), f ≠ 0 ∧
      (∃ h₁ : f ∈ R.R₁.integers, R.R₁.residue ⟨f, h₁⟩ ≠ 0 ∧
        (∀ (w) (_ : w ∈ W), w.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = -((n w : ℕ) : ℤ)) ∧
        (∀ G : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
          (∀ V, G V = V.ord f) →
          ∀ v : Place k (modularFunctionFieldC k N), v ∉ W →
            Finsupp.mapDomain P.reduceFst (P.fstDiv G) v
              = v.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)))) ∧
      (∀ (w) (hw : w ∈ W), ∃ h : f * y w ^ n w ∈ R.nodeIntegers w,
        IsUnit (⟨f * y w ^ n w, h⟩ : ↥(R.nodeIntegers w))) ∧
      (∀ z ∈ Z, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V = z → V.ord f = 0) := by
  classical

  obtain ⟨f₀, hf₀0, ⟨h₁₀, hres₀, hord₀⟩, hunit₀, hV₀⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg
      R hqN hmodel W hW hreg hval hO y n hyS hy₁ hyV hy_ord1 hvert
  have hgood₀ : P2mWs18V56.Good R W y n f₀ := ⟨hf₀0, ⟨h₁₀, hres₀, hord₀⟩, hunit₀, hV₀⟩

  let T : Finset (Place k (modularFunctionFieldC k N)) := Z.filter (fun z => z ∉ W)
  have hTW : ∀ t ∈ T, t ∉ W := fun t ht => (Finset.mem_filter.mp ht).2

  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f₀ hf₀0
  obtain ⟨f, hgood, hclear⟩ := P2mWs18V56.exists_good_forall_ord_eq_zero R hqN W hW hreg hO hmodel hval T hTW
    D₀.support.card f₀ hgood₀ ⟨D₀.support, le_rfl, fun V _ hne => Finsupp.mem_support_iff.mpr (by rw [hD₀]; exact hne)⟩
  obtain ⟨hf0, ⟨h₁, hres, hord⟩, hunit, hVW⟩ := hgood
  have hzero : ∀ z ∈ Z, z ∉ W → ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = z → V.ord f = 0 :=
    fun z hz hzW V hV => hclear V (by rw [hV]; exact Finset.mem_filter.mpr ⟨hz, hzW⟩)
  refine ⟨f, hf0, ⟨h₁, hres, hord, fun G hG v hv => ?_⟩, hunit, fun z hz V hV => ?_⟩
  · exact P2mWs18V56.mapDomain_fstDiv_eq_ord_residue₁ R hqN W hW hreg hmodel Z hZ hf0 h₁ hres hzero G hG v hv
  · by_cases hzW : z ∈ W
    · exact hVW z hzW V hV
    · exact hzero z hz hzW V hV

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_and_forall_ord_eq_zero (solution)
