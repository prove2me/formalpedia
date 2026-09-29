-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_commonUnit_pole_reduceSnd_of_regularityLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9ec71186-6d2f-5236-875b-ead9100a3c71

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_stichtenothGenusExists_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty
import Theorems.Thm_ModularCurve_exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces
import Theorems.Thm_ModularCurve_ssPlaces_finite
import Theorems.Thm_ModularCurve_degree_add_one_sub_genusFF_le_finrank_riemannRochSpace
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_map_intCast_pow_char_eq_qExpand
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictSnd_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_atkinLehnerBar_smul
import Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_constantsAreBase_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false
set_option autoImplicit false
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw.AlgebraicCurve ModularCurve~coeffEmb_jq~dedekindPsi_pos P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw.ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~IsCuspidal~IsZeroSide~IsCuspidal' P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw.ModularCurve.PlaceSpecialization.ProlongationTuple"

noncomputable section

private noncomputable abbrev algebraFullCShortcut (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Algebra K ↥(modularFunctionFieldFullC K N) := inferInstance
example (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    algebraFullCShortcut K N = (inferInstance : Algebra K ↥(modularFunctionFieldFullC K N)) := rfl
private noncomputable abbrev algebraCShortcut (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Algebra K ↥(modularFunctionFieldC K N) := inferInstance
example (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    algebraCShortcut K N = (inferInstance : Algebra K ↥(modularFunctionFieldC K N)) := rfl
private noncomputable abbrev moduleCShortcut (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    Module K ↥(modularFunctionFieldC K N) := inferInstance
example (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    moduleCShortcut K N = (inferInstance : Module K ↥(modularFunctionFieldC K N)) := rfl
private noncomputable abbrev algebraBarShortcut (M : ℕ) [NeZero M] :
    Algebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) := inferInstance
example (M : ℕ) [NeZero M] :
    algebraBarShortcut M
      = (inferInstance : Algebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M)) := rfl
private noncomputable abbrev moduleBarShortcut (M : ℕ) [NeZero M] :
    Module (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) := inferInstance
example (M : ℕ) [NeZero M] :
    moduleBarShortcut M
      = (inferInstance : Module (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M)) := rfl
private theorem hasPrincipalDivisorsBarShortcut (M : ℕ) [NeZero M] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M) :=
  ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional M
attribute [local instance high] algebraFullCShortcut algebraCShortcut moduleCShortcut algebraBarShortcut moduleBarShortcut hasPrincipalDivisorsBarShortcut

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.HasValue Place.hasValue_algebraMap Place.HasValue.mul Place.HasValue.unique Place Place.ord Place.ord_zero Place.ord_one Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor algebraAlong isIntegral_along Place.ramificationIndexAlong Place.ord_restrictAlong IsCurveOver IsCurveOver.finiteResidue RegularProlongation ConstantReduction ConstantReduction.ord_algebraMap ConstantReduction.ord_smul riemannRochSpace mem_riemannRochSpace_iff genusFF LSpace ell ell_zero_eq_one_of_constantsAreBase RegularProlongation.exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq genus exists_canonicalDivisor_genus_riemannRoch finiteDimensional_lSpace"
namespace OrderBox
p2m_open "AlgebraicCurve"

section Core

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private structure IsOrderFun (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (v : V → ℤ) : Prop where
  min_le_add : ∀ x y : V, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → min (v x) (v y) ≤ v (x + y)
  smul_eq : ∀ (c : K) (x : V), c ≠ 0 → x ≠ 0 → v (c • x) = v x

namespace IsOrderFun

variable {v : V → ℤ}

private theorem zero_or_le_add (hv : IsOrderFun K v) {n : ℤ} {x y : V}
    (hx : x = 0 ∨ n ≤ v x) (hy : y = 0 ∨ n ≤ v y) : x + y = 0 ∨ n ≤ v (x + y) := by
  by_cases hx0 : x = 0
  · subst hx0
    rwa [zero_add]
  by_cases hy0 : y = 0
  · subst hy0
    rwa [add_zero]
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  have h := hv.min_le_add x y hx0 hy0 hxy
  have hx' := hx.resolve_left hx0
  have hy' := hy.resolve_left hy0
  right
  omega

private theorem zero_or_le_smul (hv : IsOrderFun K v) {n : ℤ} (c : K) {x : V}
    (hx : x = 0 ∨ n ≤ v x) : c • x = 0 ∨ n ≤ v (c • x) := by
  by_cases hc : c = 0
  · left
    rw [hc, zero_smul]
  by_cases hx0 : x = 0
  · left
    rw [hx0, smul_zero]
  right
  rw [hv.smul_eq c x hc hx0]
  exact hx.resolve_left hx0

private theorem zero_or_le_sum (hv : IsOrderFun K v) {n : ℤ} {ι : Type*} (s : Finset ι) (f : ι → V)
    (h : ∀ i ∈ s, f i = 0 ∨ n ≤ v (f i)) : (∑ i ∈ s, f i) = 0 ∨ n ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl Finset.sum_empty
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hv.zero_or_le_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private def box (hv : IsOrderFun K v) (n : ℤ) : Submodule K V where
  carrier := {x | x = 0 ∨ n ≤ v x}
  zero_mem' := Or.inl rfl
  add_mem' hx hy := hv.zero_or_le_add hx hy
  smul_mem' c _ hx := hv.zero_or_le_smul c hx

private theorem mem_box (hv : IsOrderFun K v) {n : ℤ} {x : V} : x ∈ hv.box n ↔ x = 0 ∨ n ≤ v x :=
  Iff.rfl

private theorem linearIndependent_of_injective (hv : IsOrderFun K v) {ι : Type*} (f : ι → V)
    (hf : ∀ i, f i ≠ 0) (hinj : Function.Injective fun i => v (f i)) :
    LinearIndependent K f := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci

  obtain ⟨i₀, hi₀, hmin⟩ := (s.filter fun j => c j ≠ 0).exists_min_image (fun j => v (f j))
    ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨hi₀s, hci₀⟩ := Finset.mem_filter.mp hi₀

  have hrest : ∀ j ∈ s.erase i₀, c j • f j = 0 ∨ v (f i₀) + 1 ≤ v (c j • f j) := by
    intro j hj
    by_cases hcj : c j = 0
    · left
      rw [hcj, zero_smul]
    right
    rw [hv.smul_eq _ _ hcj (hf j)]
    have hle := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hj, hcj⟩)
    have hne : v (f j) ≠ v (f i₀) := fun h => Finset.ne_of_mem_erase hj (hinj h)
    omega
  have hbox := hv.zero_or_le_sum (s.erase i₀) (fun j => c j • f j) hrest

  have hlead : c i₀ • f i₀ = -∑ j ∈ s.erase i₀, c j • f j := by
    rw [← Finset.add_sum_erase s _ hi₀s] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  have hne0 : c i₀ • f i₀ ≠ 0 := smul_ne_zero hci₀ (hf i₀)
  rcases hbox with h0 | hle
  · exact hne0 (by rw [hlead, h0, neg_zero])
  · have hneg : v (c i₀ • f i₀) = v (∑ j ∈ s.erase i₀, c j • f j) := by
      rw [hlead, ← neg_one_smul K, hv.smul_eq _ _ (by norm_num) (fun h => hne0 (by
        rw [hlead, h, neg_zero]))]
    rw [← hneg, hv.smul_eq _ _ hci₀ (hf i₀)] at hle
    omega

private theorem finite_image (hv : IsOrderFun K v) (M : Submodule K V) [FiniteDimensional K M] :
    (v '' {x | x ∈ M ∧ x ≠ 0}).Finite := by
  classical
  by_contra hinf
  obtain ⟨T, hTsub, hTcard⟩ := Set.not_finite.mp hinf |>.exists_subset_card_eq
    (Module.finrank K M + 1)
  have hw : ∀ n ∈ T, ∃ x : V, (x ∈ M ∧ x ≠ 0) ∧ v x = n := fun n hn =>
    hTsub (Finset.mem_coe.mpr hn)
  choose! g hg using hw
  have hli : LinearIndependent K (fun n : T => (⟨g n, (hg n n.2).1.1⟩ : M)) := by
    refine LinearIndependent.of_comp M.subtype ?_
    refine hv.linearIndependent_of_injective (fun n : T => g n) (fun n => (hg n n.2).1.2) ?_
    intro a b hab
    apply Subtype.ext
    have ha := (hg a a.2).2
    have hb := (hg b b.2).2
    simp only at hab
    rw [ha, hb] at hab
    exact hab
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, hTcard] at hcard
  omega

end IsOrderFun

variable {V₁ : Type*} [AddCommGroup V₁] [Module K V₁] {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]

private theorem exists_box [Infinite K] {v₁ : V₁ → ℤ} {v₂ : V₂ → ℤ}
    (hv₁ : IsOrderFun K v₁) (hv₂ : IsOrderFun K v₂)
    (M : Submodule K (V₁ × V₂)) [FiniteDimensional K M] (m : ℤ)
    (e : V₁ × V₂) (he : e ∈ M) (he₁ : e.1 ≠ 0) (he₂ : e.2 ≠ 0)
    (hve₁ : v₁ e.1 = 0) (hve₂ : v₂ e.2 = 0)
    (hlaw : ∀ g ∈ M, g.1 ≠ 0 → g.2 ≠ 0 → -m ≤ v₁ g.1 + v₂ g.2) :
    ∃ s : ℤ, -m ≤ s ∧ s ≤ 0 ∧
      ∀ g ∈ M, (g.1 = 0 ∨ s ≤ v₁ g.1) ∧ (g.2 = 0 ∨ -m - s ≤ v₂ g.2) := by
  classical
  have hm : 0 ≤ m := by
    have h := hlaw e he he₁ he₂
    rw [hve₁, hve₂] at h
    omega

  set T : Set ℤ := v₁ '' {x | x ∈ M.map (LinearMap.fst K V₁ V₂) ∧ x ≠ 0} with hT
  haveI : Finite T := (hv₁.finite_image (M.map (LinearMap.fst K V₁ V₂))).to_subtype
  have h0T : (0 : ℤ) ∈ T := ⟨e.1, ⟨⟨e, he, rfl⟩, he₁⟩, hve₁⟩

  let B : T → Submodule K (V₁ × V₂) := fun t => (hv₁.box (t : ℤ)).prod (hv₂.box (-m - (t : ℤ)))
  have hmemB : ∀ (t : T) (g : V₁ × V₂),
      g ∈ B t ↔ (g.1 = 0 ∨ (t : ℤ) ≤ v₁ g.1) ∧ (g.2 = 0 ∨ -m - (t : ℤ) ≤ v₂ g.2) := fun t g => by
    simp only [B, Submodule.mem_prod, IsOrderFun.mem_box]

  have hsnd : ∀ g ∈ M, g.1 = 0 → g.2 ≠ 0 → -m ≤ v₂ g.2 := by
    intro g hg hg1 hg2

    obtain ⟨c, hc0, hc⟩ : ∃ c : K, c ≠ 0 ∧ g.2 + c • e.2 ≠ 0 := by
      by_cases h1 : g.2 + (1 : K) • e.2 ≠ 0
      · exact ⟨1, one_ne_zero, h1⟩
      obtain ⟨d, hd⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset K)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
      refine ⟨d, hd.1, fun hd' => hd.2 ?_⟩
      push Not at h1
      have hsub : (d - 1) • e.2 = 0 := by
        rw [sub_smul, sub_eq_zero]
        exact (neg_eq_of_add_eq_zero_right hd').symm.trans (neg_eq_of_add_eq_zero_right h1)
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right he₂)
    have hgc : g + c • e ∈ M := M.add_mem hg (M.smul_mem c he)
    have hfst : (g + c • e).1 = c • e.1 := by rw [Prod.fst_add, Prod.smul_fst, hg1, zero_add]
    have hsnd' : (g + c • e).2 = g.2 + c • e.2 := by rw [Prod.snd_add, Prod.smul_snd]
    have hl := hlaw (g + c • e) hgc (by rw [hfst]; exact smul_ne_zero hc0 he₁)
      (by rw [hsnd']; exact hc)
    rw [hfst, hv₁.smul_eq c e.1 hc0 he₁, hve₁, zero_add, hsnd'] at hl

    have hb₁ : g.2 + c • e.2 = 0 ∨ -m ≤ v₂ (g.2 + c • e.2) := Or.inr hl
    have hb₂ : (-c) • e.2 = 0 ∨ -m ≤ v₂ ((-c) • e.2) := by
      right
      rw [hv₂.smul_eq _ _ (neg_ne_zero.mpr hc0) he₂, hve₂]
      omega
    have h := hv₂.zero_or_le_add hb₁ hb₂
    rw [neg_smul, add_neg_cancel_right] at h
    exact h.resolve_left hg2

  have hcover : ∀ g ∈ M, ∃ t : T, g ∈ B t := by
    intro g hg
    by_cases hg1 : g.1 = 0
    · refine ⟨⟨0, h0T⟩, (hmemB _ _).mpr ⟨Or.inl hg1, ?_⟩⟩
      by_cases hg2 : g.2 = 0
      · exact Or.inl hg2
      · right
        have h := hsnd g hg hg1 hg2
        show -m - 0 ≤ v₂ g.2
        omega
    · refine ⟨⟨v₁ g.1, g.1, ⟨⟨g, hg, rfl⟩, hg1⟩, rfl⟩, (hmemB _ _).mpr ⟨Or.inr le_rfl, ?_⟩⟩
      by_cases hg2 : g.2 = 0
      · exact Or.inl hg2
      · right
        have h := hlaw g hg hg1 hg2
        show -m - v₁ g.1 ≤ v₂ g.2
        omega

  obtain ⟨t, ht⟩ : ∃ t : T, (B t).comap M.subtype = ⊤ := by
    by_contra hnone
    push Not at hnone
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top _ hnone
    obtain ⟨t, hxt⟩ := hcover (x : V₁ × V₂) x.2
    exact hx t hxt
  have hall : ∀ g ∈ M, g ∈ B t := fun g hg => by
    have h : (⟨g, hg⟩ : M) ∈ (B t).comap M.subtype := by
      rw [ht]
      exact Submodule.mem_top
    exact h
  have heB := (hmemB t e).mp (hall e he)
  refine ⟨t, ?_, ?_, fun g hg => (hmemB t g).mp (hall g hg)⟩
  · rcases heB.2 with h | h
    · exact absurd h he₂
    · rw [hve₂] at h
      omega
  · rcases heB.1 with h | h
    · exact absurd h he₁
    · rwa [hve₁] at h

end Core

section PlaceOrder

open IsLocalRing

variable {k₀ k F : Type*} [Field k₀] [Field k] [Field F] [Algebra k F]
  [Algebra k₀ k] [Algebra k₀ F] [IsScalarTower k₀ k F]

private theorem min_placeOrd_le_placeOrd_add (w : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (w.ord x) (w.ord y) ≤ w.ord (x + y) := by
  have hux := w.adicValuation_ne_zero hx
  have huy := w.adicValuation_ne_zero hy
  have huxy := w.adicValuation_ne_zero hxy
  unfold Place.ord
  rcases le_max_iff.mp (w.adicValuation.map_add x y) with h | h
  · have h' := (WithZero.log_le_log huxy hux).mpr h
    exact (min_le_left _ _).trans (by omega)
  · have h' := (WithZero.log_le_log huxy huy).mpr h
    exact (min_le_right _ _).trans (by omega)

private theorem isOrderFun_placeOrd (w : Place k F) : IsOrderFun k₀ (V := F) (fun x => w.ord x) where
  min_le_add x y hx hy hxy := min_placeOrd_le_placeOrd_add w hx hy hxy
  smul_eq c x hc hx := by
    show w.ord (c • x) = w.ord x
    rw [← IsScalarTower.algebraMap_smul k c x]
    exact ConstantReduction.ord_smul w ((map_ne_zero (algebraMap k₀ k)).mpr hc) x

end PlaceOrder

section Pair

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
  {k Fk : Type*} [Field k] [Field Fk] [Algebra k Fk]
  [Algebra (ResidueField A) k] [Algebra (ResidueField A) Fk] [IsScalarTower (ResidueField A) k Fk]

private def pairSpace (R₁ R₂ : RegularProlongation A F Fb) (ι : Fb →+* Fk)
    (hι : ∀ c, ι (algebraMap (ResidueField A) Fb c) = algebraMap (ResidueField A) Fk c)
    (W : Submodule L F) : Submodule (ResidueField A) (Fk × Fk) where
  carrier := {g | ∃ (f : F) (_ : f ∈ W) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
    g = (ι (R₁.residue ⟨f, h₁⟩), ι (R₂.residue ⟨f, h₂⟩))}
  zero_mem' := by
    refine ⟨0, W.zero_mem, R₁.integers.zero_mem, R₂.integers.zero_mem, ?_⟩
    have e₁ : (⟨(0 : F), R₁.integers.zero_mem⟩ : R₁.integers) = 0 := rfl
    have e₂ : (⟨(0 : F), R₂.integers.zero_mem⟩ : R₂.integers) = 0 := rfl
    rw [e₁, e₂]
    simp only [map_zero]
    rfl
  add_mem' := by
    rintro g g' ⟨f, hf, h₁, h₂, rfl⟩ ⟨f', hf', h₁', h₂', rfl⟩
    refine ⟨f + f', W.add_mem hf hf', add_mem h₁ h₁', add_mem h₂ h₂', ?_⟩
    have e₁ : (⟨f + f', add_mem h₁ h₁'⟩ : R₁.integers) = ⟨f, h₁⟩ + ⟨f', h₁'⟩ := rfl
    have e₂ : (⟨f + f', add_mem h₂ h₂'⟩ : R₂.integers) = ⟨f, h₂⟩ + ⟨f', h₂'⟩ := rfl
    rw [e₁, e₂]
    simp only [map_add]
    rfl
  smul_mem' := by
    rintro c g ⟨f, hf, h₁, h₂, rfl⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    have ha₁ : algebraMap L F (a : L) ∈ R₁.integers := (R₁.algebraMap_mem_iff _).mpr a.2
    have ha₂ : algebraMap L F (a : L) ∈ R₂.integers := (R₂.algebraMap_mem_iff _).mpr a.2
    refine ⟨algebraMap L F (a : L) * f, ?_, mul_mem ha₁ h₁, mul_mem ha₂ h₂, ?_⟩
    · rw [← Algebra.smul_def]
      exact W.smul_mem _ hf
    have e₁ : (⟨algebraMap L F (a : L) * f, mul_mem ha₁ h₁⟩ : R₁.integers)
        = ⟨_, ha₁⟩ * ⟨f, h₁⟩ := rfl
    have e₂ : (⟨algebraMap L F (a : L) * f, mul_mem ha₂ h₂⟩ : R₂.integers)
        = ⟨_, ha₂⟩ * ⟨f, h₂⟩ := rfl
    rw [e₁, e₂]
    simp only [map_mul, R₁.residue_algebraMap a, R₂.residue_algebraMap a, hι]
    rw [Prod.smul_mk, Algebra.smul_def, Algebra.smul_def]

private theorem exists_box_of_orderLaw [Infinite (ResidueField A)]
    (R₁ R₂ : RegularProlongation A F Fb) (ι : Fb →+* Fk)
    (hι : ∀ c, ι (algebraMap (ResidueField A) Fb c) = algebraMap (ResidueField A) Fk c)
    (W : Submodule L F) (h1 : (1 : F) ∈ W)
    [FiniteDimensional (ResidueField A) (pairSpace R₁ R₂ ι hι W)]
    (w₁ w₂ : Place k Fk) (m : ℤ)
    (hlaw : ∀ (f : F), f ∈ W → ∀ (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
      R₁.residue ⟨f, h₁⟩ ≠ 0 → R₂.residue ⟨f, h₂⟩ ≠ 0 →
        -m ≤ w₁.ord (ι (R₁.residue ⟨f, h₁⟩)) + w₂.ord (ι (R₂.residue ⟨f, h₂⟩))) :
    ∃ s : ℤ, -m ≤ s ∧ s ≤ 0 ∧
      ∀ (f : F), f ∈ W → ∀ (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
        (ι (R₁.residue ⟨f, h₁⟩) = 0 ∨ s ≤ w₁.ord (ι (R₁.residue ⟨f, h₁⟩))) ∧
        (ι (R₂.residue ⟨f, h₂⟩) = 0 ∨ -m - s ≤ w₂.ord (ι (R₂.residue ⟨f, h₂⟩))) := by
  have hv₁ := isOrderFun_placeOrd (k₀ := ResidueField A) w₁
  have hv₂ := isOrderFun_placeOrd (k₀ := ResidueField A) w₂
  have he : ((1 : Fk), (1 : Fk)) ∈ pairSpace R₁ R₂ ι hι W := by
    refine ⟨1, h1, R₁.integers.one_mem, R₂.integers.one_mem, ?_⟩
    have e₁ : (⟨(1 : F), R₁.integers.one_mem⟩ : R₁.integers) = 1 := rfl
    have e₂ : (⟨(1 : F), R₂.integers.one_mem⟩ : R₂.integers) = 1 := rfl
    rw [e₁, e₂]
    simp only [map_one]
  obtain ⟨s, hs₁, hs₂, hall⟩ := exists_box hv₁ hv₂ (pairSpace R₁ R₂ ι hι W) m ((1 : Fk), (1 : Fk))
    he one_ne_zero one_ne_zero w₁.ord_one w₂.ord_one (by
      rintro g ⟨f, hf, h₁, h₂, rfl⟩ hg₁ hg₂
      exact hlaw f hf h₁ h₂ (fun h => hg₁ (by simp only [h, map_zero]))
        (fun h => hg₂ (by simp only [h, map_zero])))
  exact ⟨s, hs₁, hs₂, fun f hf h₁ h₂ => hall _ ⟨f, hf, h₁, h₂, rfl⟩⟩

end Pair

section Device

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
  {k Fk : Type*} [Field k] [Field Fk] [Algebra k Fk]
  [Algebra (ResidueField A) k] [Algebra (ResidueField A) Fk] [IsScalarTower (ResidueField A) k Fk]

private theorem exists_forall_mul_inv_mem {ι : Type*} (s : Finset ι) (c : ι → L) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hc₀ : c i₀ ≠ 0) : ∃ j ∈ s, c j ≠ 0 ∧ ∀ i ∈ s, c i * (c j)⁻¹ ∈ A := by
  classical
  obtain ⟨j, hjs, hmax⟩ := s.exists_max_image (fun i => A.valuation (c i)) ⟨i₀, hi₀⟩
  have hvj : A.valuation (c j) ≠ 0 := by
    intro h0
    have h := hmax i₀ hi₀
    rw [h0, le_zero_iff, Valuation.zero_iff] at h
    exact hc₀ h
  refine ⟨j, hjs, fun h => hvj (by rw [h, Valuation.map_zero]), fun i hi => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv]
  calc A.valuation (c i) * (A.valuation (c j))⁻¹
      ≤ A.valuation (c j) * (A.valuation (c j))⁻¹ := by
        gcongr
        exact hmax i hi
    _ = 1 := mul_inv_cancel₀ hvj

private theorem linearIndependent_of_pairs (R₁ R₂ : RegularProlongation A F Fb) (ι : Fb →+* Fk)
    (hι : ∀ c, ι (algebraMap (ResidueField A) Fb c) = algebraMap (ResidueField A) Fk c)
    {I : Type*} (f : I → F) (h₁ : ∀ i, f i ∈ R₁.integers) (h₂ : ∀ i, f i ∈ R₂.integers)
    (hli : LinearIndependent (ResidueField A)
      (fun i => (ι (R₁.residue ⟨f i, h₁ i⟩), ι (R₂.residue ⟨f i, h₂ i⟩)))) :
    LinearIndependent L f := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci
  obtain ⟨j, hjs, hcj, hA⟩ := exists_forall_mul_inv_mem (A := A) s c hi hci

  let a : I → A := fun i => if hi : i ∈ s then ⟨c i * (c j)⁻¹, hA i hi⟩ else 0
  have ha : ∀ i ∈ s, ((a i : A) : L) = c i * (c j)⁻¹ := fun i hi => by simp [a, hi]
  have haj : a j = 1 := Subtype.ext (by rw [ha j hjs]; exact mul_inv_cancel₀ hcj)
  have hrel : ∑ i ∈ s, algebraMap L F ((a i : A) : L) * f i = 0 := by
    have h : ∑ i ∈ s, algebraMap L F ((a i : A) : L) * f i = (c j)⁻¹ • ∑ i ∈ s, c i • f i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ha i hi, ← Algebra.smul_def, smul_smul, mul_comm]
    rw [h, hsum, smul_zero]

  have key : ∀ (R : RegularProlongation A F Fb) (hR : ∀ i, f i ∈ R.integers),
      ∑ i ∈ s, (IsLocalRing.residue A (a i)) • ι (R.residue ⟨f i, hR i⟩) = 0 := by
    intro R hR
    let x : I → R.integers := fun i =>
      ⟨algebraMap L F ((a i : A) : L) * f i, mul_mem ((R.algebraMap_mem_iff _).mpr (a i).2) (hR i)⟩
    have hx0 : ∑ i ∈ s, x i = 0 := Subtype.ext ((map_sum R.integers.subtype x s).trans hrel)
    have h := congrArg (fun y => ι (R.residue y)) hx0
    simp only [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hxi : x i = ⟨_, (R.algebraMap_mem_iff _).mpr (a i).2⟩ * ⟨f i, hR i⟩ := rfl
    rw [hxi, map_mul, map_mul, R.residue_algebraMap (a i), hι, Algebra.smul_def]
  have hpair : ∑ i ∈ s, (IsLocalRing.residue A (a i)) •
      (ι (R₁.residue ⟨f i, h₁ i⟩), ι (R₂.residue ⟨f i, h₂ i⟩)) = 0 := by
    rw [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero]
    exact ⟨(Finset.sum_congr rfl fun i _ => rfl).trans (key R₁ h₁),
      (Finset.sum_congr rfl fun i _ => rfl).trans (key R₂ h₂)⟩
  have h0 := (linearIndependent_iff'.mp hli) s (fun i => IsLocalRing.residue A (a i)) hpair j hjs
  simp only [haj, map_one] at h0
  exact one_ne_zero h0

private theorem finiteDimensional_pairSpace (R₁ R₂ : RegularProlongation A F Fb) (ι : Fb →+* Fk)
    (hι : ∀ c, ι (algebraMap (ResidueField A) Fb c) = algebraMap (ResidueField A) Fk c)
    (W : Submodule L F) [FiniteDimensional L W] :
    FiniteDimensional (ResidueField A) (pairSpace R₁ R₂ ι hι W) := by
  classical
  obtain ⟨T, hTS, hspan, hli⟩ :=
    exists_linearIndependent (ResidueField A) (pairSpace R₁ R₂ ι hι W : Set (Fk × Fk))
  have hTfin : T.Finite := by
    by_contra hinf
    obtain ⟨T', hT', hcard⟩ := Set.not_finite.mp hinf |>.exists_subset_card_eq (Module.finrank L W + 1)
    have hpre : ∀ p ∈ T', ∃ (f : F) (_ : f ∈ W) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers),
        p = (ι (R₁.residue ⟨f, hf₁⟩), ι (R₂.residue ⟨f, hf₂⟩)) := fun p hp =>
      hTS (hT' (Finset.mem_coe.mpr hp))
    choose! g hgW hg₁ hg₂ hgp using hpre
    have hsub : LinearIndependent (ResidueField A) (fun p : T' => (p : Fk × Fk)) :=
      hli.comp (fun p : T' => (⟨(p : Fk × Fk), hT' (Finset.mem_coe.mpr p.2)⟩ : T))
        (fun p p' h => Subtype.ext (by simpa using congrArg (fun z : T => (z : Fk × Fk)) h))
    have hliT' : LinearIndependent (ResidueField A)
        (fun p : T' => (ι (R₁.residue ⟨g p, hg₁ p p.2⟩), ι (R₂.residue ⟨g p, hg₂ p p.2⟩))) := by
      have hfeq : (fun p : T' => (ι (R₁.residue ⟨g p, hg₁ p p.2⟩), ι (R₂.residue ⟨g p, hg₂ p p.2⟩)))
          = (fun p : T' => (p : Fk × Fk)) := funext fun p => (hgp p p.2).symm
      rw [hfeq]
      exact hsub
    have hliL : LinearIndependent L (fun p : T' => g p) :=
      linearIndependent_of_pairs R₁ R₂ ι hι _ (fun p => hg₁ p p.2) (fun p => hg₂ p p.2) hliT'
    have hliW : LinearIndependent L (fun p : T' => (⟨g p, hgW p p.2⟩ : W)) :=
      LinearIndependent.of_comp W.subtype hliL
    have hle := hliW.fintype_card_le_finrank
    rw [Fintype.card_coe, hcard] at hle
    omega
  have hspan' : Submodule.span (ResidueField A) T = pairSpace R₁ R₂ ι hι W := by
    rw [hspan, Submodule.span_eq]
  rw [← hspan']
  exact FiniteDimensional.span_of_finite _ hTfin

end Device

end AlgebraicCurve.OrderBox

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw.AlgebraicCurve ModularCurve~coeffEmb_jq~dedekindPsi_pos P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw.ModularCurve"

section InsepDegree
variable {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]

private theorem AuxNS.not_mem_adjoin_pow_of_transcendental {q : ℕ} (hq : q.Prime) {t : F}
    (ht : Transcendental κ t) : t ∉ IntermediateField.adjoin κ ({t ^ q} : Set F) := by
  intro hmem
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff κ t).mp hmem
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero] at hrs
    rw [hrs] at ht
    exact ht isAlgebraic_zero
  have hS : Polynomial.aeval (t ^ q) s ≠ 0 := fun h0 =>
    hs0 ((Polynomial.expand_eq_zero hq.pos).mp
      (transcendental_iff.mp ht (Polynomial.expand κ q s) (by rwa [Polynomial.expand_aeval])))
  have hmul : t * Polynomial.aeval (t ^ q) s = Polynomial.aeval (t ^ q) r := (eq_div_iff hS).mp hrs
  have hP : Polynomial.aeval t (Polynomial.X * Polynomial.expand κ q s - Polynomial.expand κ q r) = 0 := by
    rw [map_sub, map_mul, Polynomial.aeval_X, Polynomial.expand_aeval, Polynomial.expand_aeval, hmul,
      sub_self]
  have hz := transcendental_iff.mp ht _ hP
  have hnd : ¬ q ∣ q * s.natDegree + 1 := fun h =>
    hq.ne_one (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right q _)).mp h))
  have hc := congrArg (fun p : Polynomial κ => p.coeff (q * s.natDegree + 1)) hz
  simp only [Polynomial.coeff_sub, Polynomial.coeff_zero, Polynomial.coeff_X_mul,
    Polynomial.coeff_expand hq.pos] at hc
  rw [if_pos (dvd_mul_right q _), if_neg hnd, Nat.mul_div_cancel_left _ hq.pos, sub_zero,
    Polynomial.coeff_natDegree] at hc
  exact hs0 (Polynomial.leadingCoeff_eq_zero.mp hc)

private theorem AuxNS.relfinrank_adjoin_pow_char (q : ℕ) (hq : q.Prime) [CharP κ q] {t : F}
    (ht : Transcendental κ t) :
    (IntermediateField.adjoin κ ({t ^ q} : Set F)).relfinrank (IntermediateField.adjoin κ ({t} : Set F))
      = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP F q := charP_of_injective_algebraMap (algebraMap κ F).injective q
  have hle : IntermediateField.adjoin κ ({t ^ q} : Set F) ≤ IntermediateField.adjoin κ ({t} : Set F) :=
    IntermediateField.adjoin_simple_le_iff.mpr (pow_mem (IntermediateField.mem_adjoin_simple_self κ t) q)
  have hnot := AuxNS.not_mem_adjoin_pow_of_transcendental (κ := κ) hq ht
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]

  have hE : IntermediateField.extendScalars hle
      = IntermediateField.adjoin (IntermediateField.adjoin κ ({t ^ q} : Set F)) ({t} : Set F) := by
    apply le_antisymm
    · intro x hx
      have hsub : IntermediateField.adjoin κ ({t} : Set F) ≤
          (IntermediateField.adjoin (IntermediateField.adjoin κ ({t ^ q} : Set F))
            ({t} : Set F)).restrictScalars κ :=
        IntermediateField.adjoin_simple_le_iff.mpr
          (IntermediateField.mem_adjoin_simple_self (IntermediateField.adjoin κ ({t ^ q} : Set F)) t)
      exact hsub ((IntermediateField.mem_extendScalars hle).mp hx)
    · exact IntermediateField.adjoin_simple_le_iff.mpr
        ((IntermediateField.mem_extendScalars hle).mpr (IntermediateField.mem_adjoin_simple_self κ t))
  rw [hE]

  obtain ⟨a, ha⟩ : ∃ a : IntermediateField.adjoin κ ({t ^ q} : Set F), (a : F) = t ^ q :=
    ⟨⟨t ^ q, IntermediateField.mem_adjoin_simple_self κ (t ^ q)⟩, rfl⟩
  have hmonic : (Polynomial.X ^ q - Polynomial.C a).Monic := Polynomial.monic_X_pow_sub_C a hq.ne_zero
  have haeval : Polynomial.aeval t (Polynomial.X ^ q - Polynomial.C a) = 0 := by simp [ha]
  have hirr : Irreducible (Polynomial.X ^ q - Polynomial.C a) := by
    refine X_pow_sub_C_irreducible_of_prime hq fun b hb => hnot ?_
    have h1 : (b : F) ^ q = t ^ q := by
      have h := congrArg (fun x : IntermediateField.adjoin κ ({t ^ q} : Set F) => (x : F)) hb
      simpa [ha] using h
    have h3 : ((b : F) - t) ^ q = 0 := by rw [sub_pow_char, h1, sub_self]
    have h2 : (b : F) = t := sub_eq_zero.mp ((pow_eq_zero_iff hq.ne_zero).mp h3)
    have hb2 : (b : F) ∈ IntermediateField.adjoin κ ({t ^ q} : Set F) := b.2
    rw [h2] at hb2
    exact hb2
  have hint : IsIntegral (IntermediateField.adjoin κ ({t ^ q} : Set F)) t :=
    ⟨_, hmonic, by rwa [← Polynomial.aeval_def]⟩
  have hmin := minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
  rw [IntermediateField.adjoin.finrank hint, ← hmin, Polynomial.natDegree_X_pow_sub_C]

private theorem AuxNS.finrank_adjoin_pow_char (q : ℕ) (hq : q.Prime) [CharP κ q] {t : F}
    (ht : Transcendental κ t) :
    Module.finrank (IntermediateField.adjoin κ ({t ^ q} : Set F)) F
      = q * Module.finrank (IntermediateField.adjoin κ ({t} : Set F)) F := by
  have hle : IntermediateField.adjoin κ ({t ^ q} : Set F) ≤ IntermediateField.adjoin κ ({t} : Set F) :=
    IntermediateField.adjoin_simple_le_iff.mpr (pow_mem (IntermediateField.mem_adjoin_simple_self κ t) q)
  rw [← IntermediateField.relfinrank_mul_finrank_top hle, AuxNS.relfinrank_adjoin_pow_char q hq ht]

end InsepDegree

section N1Generic

private theorem AuxNS.dedekindPsi_pos (M : ℕ) [NeZero M] : 0 < dedekindPsi M := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ M.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne M), squarefree_one⟩
  have h2 : M / 1 ≤ ∑ d ∈ M.divisors.filter Squarefree, M / d :=
    Finset.single_le_sum (f := fun d => M / d) (fun _ _ => Nat.zero_le _) h1
  rw [Nat.div_one] at h2
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne M)) h2

private theorem AuxNS.transcendental_jqModC_full (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] :
    Transcendental K (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) := by
  intro halg
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral)
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp ((minpoly.degree_eq_one_iff (A := K)
    (x := (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N))).mp hdeg)
  have h0 : algebraMap K (LaurentSeries K) c = jqModC K := congrArg Subtype.val hc
  rw [algebraMap_laurentSeries_eq_single] at h0
  have h2 := congrArg (fun s : LaurentSeries K => s.coeff (-1 : ℤ)) h0
  change (HahnSeries.single (0 : ℤ) c).coeff (-1 : ℤ) = (jqModC K).coeff (-1 : ℤ) at h2
  rw [HahnSeries.coeff_single_of_ne (by decide : (-1 : ℤ) ≠ 0), coeff_jqModC_neg_one] at h2
  exact zero_ne_one h2

end N1Generic

section N1aGeneric

private noncomputable def AuxNS.frobDefectZ (q : ℕ) [NeZero q] : LaurentSeries ℤ :=
  qExpand ℤ q (jqModC ℤ) - jqModC ℤ ^ q

private theorem AuxNS.dvd_coeff_frobDefectZ (q : ℕ) [NeZero q] [Fact q.Prime] (n : ℤ) :
    (q : ℤ) ∣ (AuxNS.frobDefectZ q).coeff n := by
  have h0 : coeffMap (Int.castRingHom (ZMod q)) (AuxNS.frobDefectZ q) = 0 := by
    have hJ : coeffMap (Int.castRingHom (ZMod q)) (jqModC ℤ) = (jqModC ℤ).map (Int.castRingHom (ZMod q)) :=
      rfl
    rw [AuxNS.frobDefectZ, map_sub, map_pow, ModularCurve.coeffSemilinearAut.coeffMap_qExpand, hJ,
      map_intCast_pow_char_eq_qExpand (K := ZMod q) q (jqModC ℤ), sub_self]
  have h1 : (((AuxNS.frobDefectZ q).coeff n : ℤ) : ZMod q) = 0 := by
    have h := congrArg (fun s : LaurentSeries (ZMod q) => s.coeff n) h0
    simpa [coeffMap_coeff] using h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h1

private noncomputable def AuxNS.frobQuotZ (q : ℕ) [NeZero q] : LaurentSeries ℤ where
  coeff n := (AuxNS.frobDefectZ q).coeff n / (q : ℤ)
  isPWO_support' := (AuxNS.frobDefectZ q).isPWO_support.mono fun n hn =>
    (HahnSeries.mem_support _ _).mpr fun h0 => (Function.mem_support.mp hn) (by simp [h0])

private theorem AuxNS.coeff_frobQuotZ (q : ℕ) [NeZero q] (n : ℤ) :
    (AuxNS.frobQuotZ q).coeff n = (AuxNS.frobDefectZ q).coeff n / (q : ℤ) := rfl

open HahnSeries in
private theorem AuxNS.natCast_mul_coeffMap_frobQuotZ (q : ℕ) [NeZero q] [Fact q.Prime] :
    (q : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) (AuxNS.frobQuotZ q)
      = qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ)) - jqModC (AlgebraicClosure ℚ) ^ q := by
  have hq : q.Prime := Fact.out
  have hnum : coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) (AuxNS.frobDefectZ q)
      = qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ)) - jqModC (AlgebraicClosure ℚ) ^ q := by
    have hJ : coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) (jqModC ℤ) = jqModC (AlgebraicClosure ℚ) :=
      map_jqModC _
    rw [AuxNS.frobDefectZ, map_sub, map_pow, ModularCurve.coeffSemilinearAut.coeffMap_qExpand, hJ]
  rw [← hnum, ← map_natCast (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) q,
    algebraMap_laurentSeries_eq_single, ← C_apply, C_mul_eq_smul]
  ext n
  rw [coeff_smul, smul_eq_mul, coeffMap_coeff, coeffMap_coeff, eq_intCast, eq_intCast, AuxNS.coeff_frobQuotZ]
  obtain ⟨m, hm⟩ := AuxNS.dvd_coeff_frobDefectZ q n
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [hm, Int.mul_ediv_cancel_left m hq0]
  simp

end N1aGeneric

section KGeneric

variable {K₁ F₁ : Type*} [Field K₁] [Field F₁] [Algebra K₁ F₁]

private theorem AuxNS.hasValue_zero (v : Place K₁ F₁) : v.HasValue (0 : F₁) 0 := by
  have h := Place.hasValue_algebraMap v (0 : K₁)
  rwa [map_zero] at h

private theorem AuxNS.hasValue_add {v : Place K₁ F₁} {g g' : F₁} {a a' : K₁} (h : v.HasValue g a)
    (h' : v.HasValue g' a') : v.HasValue (g + g') (a + a') :=
  ⟨add_mem h.mem h'.mem, by
    rw [show (⟨g + g', add_mem h.mem h'.mem⟩ : v.toValuationSubring) = ⟨g, h.mem⟩ + ⟨g', h'.mem⟩ from rfl]
    simp only [map_add, h.residue_eq, h'.residue_eq]⟩

private theorem AuxNS.hasValue_smul {v : Place K₁ F₁} {g : F₁} {a : K₁} (c : K₁) (h : v.HasValue g a) :
    v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]
  exact Place.HasValue.mul (v := v) (Place.hasValue_algebraMap v c) h

private theorem AuxNS.ord_pos_of_hasValue_zero {v : Place K₁ F₁} {g : F₁} (hg : g ≠ 0) (h : v.HasValue g 0) :
    0 < v.ord g := by
  have hmax : (⟨g, h.mem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.residue_eq_zero_iff _).mp (by rw [h.residue_eq, map_zero])
  have hnonunit : ¬ IsUnit (⟨g, h.mem⟩ : v.toValuationSubring) :=
    _root_.mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmax)
  rcases (v.ord_nonneg_of_mem h.mem).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply hnonunit
    have hinv : g⁻¹ ∈ v.toValuationSubring :=
      v.mem_of_ord_nonneg (inv_ne_zero hg) (by have h1 := v.ord_inv g; omega)
    exact isUnit_iff_exists_inv.mpr ⟨⟨g⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hg)⟩

private theorem AuxNS.ell_eq_of_eq_fullC (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N]
    (S : IntermediateField K (LaurentSeries K)) (hS : S = modularFunctionFieldFullC K N) (D : Divisor K S)
    (hD : 2 * (genusFF K S : ℤ) - 1 ≤ D.degree) : (ell D : ℤ) = D.degree + 1 - genusFF K S := by
  subst hS
  exact ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC K N D hD

end KGeneric

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_one_apply jq dedekindPsi ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral deg_eq_one_modularFunctionFieldC frobeniusGeomLevel_jq frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective ord_frobOnPlaces_of_pow_eq KroneckerCongruence nodePairsOfPlaces smulNodePair_mem_nodePairsOfPlaces fst_mem_of_mem_nodePairsOfPlaces isSupersingularPlace_iff ssPlaces mem_ssPlaces_iff jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero IsCentreOf IsAffineGeomPlace coeff_jqModC_neg_one coeffSemilinearAut.coeffMap_qExpand coeffSemilinearAut arithFrobC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull atkinLehnerInvolutionFull_eq_refl geomAut coe_geomAut_coeffEmb modularFunctionFieldFullC jqModC_mem_full coeffMap_qExpand hasPrincipalDivisors_modularFunctionFieldBar_unconditional arithFrobC_smul_eq_frobOnPlacesGeomLevel arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd deg_eq_one_modularFunctionFieldBar stichtenothGenusExists_modularFunctionFieldBar nonempty_modularPolynomialData ModularPolynomialData.eval_jqNModC_mul_eq_zero isCurveOver_modularFunctionFieldC_of_perfectField exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces ssPlaces_finite degree_add_one_sub_genusFF_le_finrank_riemannRochSpace exists_isAtkinLehnerAutFull_of_prime_of_not_dvd finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi map_intCast_pow_char_eq_qExpand CompEq.finrank_adjoin_jBar_eq_dedekindPsi jBar dedekindPsi_mul_of_coprime dedekindPsi_prime modularFunctionFieldC_eq_modularFunctionFieldFullC ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC constantsAreBase_modularFunctionFieldC_of_perfectField"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple reduceFst reduceSnd IsStrictFst IsStrictSnd IsGoodDiv fstDiv sndDiv sp d0_j d0_j_pole d4 exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq isStrictSnd_atkinLehnerBar_smul_iff reduceFst_atkinLehnerBar_smul reduceSnd_atkinLehnerBar_smul"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "atkinLehnerBar jFun jQFun IsCuspidal IsCuspidal' IsInftySide IsZeroSide mem_integers₂_iff residue₁ residue₂ residue₁_apply residue₂_apply DivisorLawFst DivisorLawSnd OrderLawFixed CuspLawInfty CuspLawZero IsModel RegularityLaw ι_coe R₁ ι redBar_residue mem_integersFst_iff R₂ redBar residue₁_coeffMap mem_integersSnd_iff residue₂_eq not_isInftySide_of_isZeroSide isInftySide_or_isZeroSide_of_isCuspidal reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization~IsInftySide~jFun~IsCuspidal~IsZeroSide~IsCuspidal' ModularCurve~coeffEmb_jq~dedekindPsi_pos"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq~dedekindPsi_pos P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw.ModularCurve ModularCurve.PlaceSpecialization~IsInftySide~jFun~IsCuspidal~IsZeroSide~IsCuspidal' P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw.ModularCurve.PlaceSpecialization"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

omit [IsAlgClosed k] [DecidableEq k] in
private theorem ι_algebraMap_eq (R : ProlongationTuple P) (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) c)
      = algebraMap k (modularFunctionFieldC k N) (R.redBar c) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c)
    = algebraMap k (LaurentSeries k) (R.redBar c)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem neg_mass_le_ord_add_ord (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (haff : IsAffineGeomPlace k N v)
    (f : modularFunctionFieldBar (N * q)) (hfV : f ∈ riemannRochSpace E)
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hne₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hne₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0) :
    -(Finsupp.mapDomain P.reduceFst E v) ≤ v.ord (R.ι (R.R₁.residue ⟨f, h₁⟩))
      + (frobOnPlacesGeomLevel k N data hKr v).ord (R.ι (R.R₂.residue ⟨f, h₂⟩)) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hne₁ (by
      have h : (⟨(0 : modularFunctionFieldBar (N * q)), h₁⟩ : R.R₁.integers) = 0 := rfl
      rw [h, map_zero])
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor
    (self := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)) f hf0
  have hlaw := hO f h₁ h₂ hne₁ hne₂ D hD v hv haff
  rw [residue₁_apply, residue₂_apply] at hlaw
  rw [← hlaw]
  have hDE : -E ≤ D := by
    intro W
    rw [Finsupp.coe_neg, Pi.neg_apply, hD W]
    exact ((mem_riemannRochSpace_iff.mp hfV) W).resolve_left hf0
  have hmono := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := P.reduceFst) hDE) v
  have hneg : Finsupp.mapDomain P.reduceFst (-E) = -Finsupp.mapDomain P.reduceFst E :=
    map_neg (Finsupp.mapDomain.addMonoidHom P.reduceFst) E
  rw [hneg] at hmono
  exact hmono

omit [IsAlgClosed k] [DecidableEq k] in
private theorem exists_orderBox_of_orderLawFixed (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hE : ∀ W, 0 ≤ E W)
    [FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace E)]
    (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (haff : IsAffineGeomPlace k N v) :
    ∃ s : ℤ, -(Finsupp.mapDomain P.reduceFst E v) ≤ s ∧ s ≤ 0 ∧
      ∀ (f : modularFunctionFieldBar (N * q)), f ∈ riemannRochSpace E →
        ∀ (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
          (R.residue₁ ⟨f, h₁⟩ = 0 ∨ s ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
          (R.residue₂ ⟨f, h₂⟩ = 0 ∨
            -(Finsupp.mapDomain P.reduceFst E v) - s ≤
              (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩)) := by
  classical
  haveI : Infinite (ResidueField A) := inferInstance

  letI algk : Algebra (ResidueField A) k := R.redBar.toAlgebra
  letI algC : Algebra (ResidueField A) (modularFunctionFieldC k N) :=
    ((algebraMap k (modularFunctionFieldC k N)).comp R.redBar).toAlgebra
  have halg : ∀ c, algebraMap (ResidueField A) (modularFunctionFieldC k N) c
      = algebraMap k (modularFunctionFieldC k N) (R.redBar c) := fun c => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  have halgk : ∀ c, algebraMap (ResidueField A) k c = R.redBar c := fun c => by
    rw [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower (ResidueField A) k (modularFunctionFieldC k N) :=
    IsScalarTower.of_algebraMap_eq (fun c => by rw [halg, halgk])
  have hι : ∀ c, R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) N) c)
      = algebraMap (ResidueField A) (modularFunctionFieldC k N) c := fun c => by
    rw [halg]
    exact ι_algebraMap_eq R c
  haveI : FiniteDimensional (ResidueField A)
      (AlgebraicCurve.OrderBox.pairSpace R.R₁ R.R₂ R.ι hι (riemannRochSpace E)) :=
    AlgebraicCurve.OrderBox.finiteDimensional_pairSpace R.R₁ R.R₂ R.ι hι (riemannRochSpace E)
  have h1 : (1 : modularFunctionFieldBar (N * q)) ∈ riemannRochSpace E := by
    rw [mem_riemannRochSpace_iff]
    intro W
    right
    rw [Place.ord_one]
    have h := hE W
    omega
  obtain ⟨s, hs₁, hs₂, hall⟩ := AlgebraicCurve.OrderBox.exists_box_of_orderLaw R.R₁ R.R₂ R.ι hι
    (riemannRochSpace E) h1 v (frobOnPlacesGeomLevel k N data hKr v)
    (Finsupp.mapDomain P.reduceFst E v)
    (fun f hfV h₁ h₂ hne₁ hne₂ => neg_mass_le_ord_add_ord R hO E v hv haff f hfV h₁ h₂ hne₁ hne₂)
  refine ⟨s, hs₁, hs₂, fun f hf h₁ h₂ => ?_⟩
  rw [residue₁_apply, residue₂_apply]
  exact hall f hf h₁ h₂

private theorem neg_mapDomain_filter_le {X Y : Type*} (r : X → Y) (D E : X →₀ ℤ) (p : X → Prop)
    {d₁ d₂ : DecidablePred p} (hDE : ∀ W, -E W ≤ D W) (y : Y) :
    -(Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d₂ E) y)
      ≤ Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d₁ D) y := by
  have hd : d₂ = d₁ := Subsingleton.elim _ _
  subst hd
  have hle : -(Finsupp.filter p E) ≤ Finsupp.filter p D := Finsupp.le_def.mpr fun W => by
    rw [Finsupp.coe_neg, Pi.neg_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    split_ifs
    · exact hDE W
    · rw [neg_zero]
  have hm := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := r) hle) y
  have hneg : Finsupp.mapDomain r (-(Finsupp.filter p E)) = -Finsupp.mapDomain r (Finsupp.filter p E) :=
    map_neg (Finsupp.mapDomain.addMonoidHom r) _
  rw [hneg, Finsupp.coe_neg, Pi.neg_apply] at hm
  exact hm

private theorem mapDomain_filter_nonneg {X Y : Type*} (r : X → Y) (E : X →₀ ℤ) (p : X → Prop)
    {d : DecidablePred p} (hE : ∀ W, 0 ≤ E W) (y : Y) :
    0 ≤ Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d E) y := by
  have hle : (0 : X →₀ ℤ) ≤ Finsupp.filter p E := Finsupp.le_def.mpr fun W => by
    rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.filter_apply]
    split_ifs
    · exact hE W
    · exact le_rfl
  have hm := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := r) hle) y
  rw [Finsupp.mapDomain_zero, Finsupp.coe_zero, Pi.zero_apply] at hm
  exact hm

private theorem ord_sub_algebraMap_of_ord_lt_zero {K₀ F₀ : Type*} [Field K₀] [Field F₀]
    [Algebra K₀ F₀] (W : Place K₀ F₀) (g : F₀) (c : K₀) (hg : W.ord g < 0) :
    W.ord (g - algebraMap K₀ F₀ c) = W.ord g := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hg
    exact lt_irrefl _ hg
  have hgc0 : g - algebraMap K₀ F₀ c ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hg
    rcases eq_or_ne c 0 with rfl | hc
    · rw [map_zero, Place.ord_zero] at hg
      exact lt_irrefl _ hg
    · rw [ConstantReduction.ord_algebraMap W hc] at hg
      exact lt_irrefl _ hg
  have hv : W.adicValuation (-(algebraMap K₀ F₀ c)) < W.adicValuation g := by
    rw [Valuation.map_neg, W.adicValuation_eq_exp_neg_ord hg0]
    refine lt_of_le_of_lt (W.adicValuation_algebraMap_le_one c) ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have h1 := Valuation.map_add_eq_of_lt_left _ hv
  rw [← sub_eq_add_neg, W.adicValuation_eq_exp_neg_ord hgc0, W.adicValuation_eq_exp_neg_ord hg0] at h1
  have h2 := WithZero.exp_injective h1
  omega

private theorem algebraMap_mem_riemannRochSpace {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    {E : Divisor K₀ F₀} (hE : ∀ W, 0 ≤ E W) (c : K₀) : algebraMap K₀ F₀ c ∈ riemannRochSpace E := by
  rw [mem_riemannRochSpace_iff]
  intro W
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl (map_zero _)
  · refine Or.inr ?_
    rw [ConstantReduction.ord_algebraMap W hc]
    have h := hE W
    omega

private theorem regProl_residue_sub_algebraMap {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) {f : F} (hf : f ∈ R.integers) (a : A) :
    ∃ h : f - algebraMap L F a ∈ R.integers,
      R.residue ⟨f - algebraMap L F a, h⟩
        = R.residue ⟨f, hf⟩ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
  have ha : algebraMap L F a ∈ R.integers := (R.algebraMap_mem_iff a).mpr a.2
  refine ⟨sub_mem hf ha, ?_⟩
  rw [← R.residue_algebraMap a, ← map_sub]
  rfl

private theorem regProl_exists_residue_sub_algebraMap_ne_zero {L : Type*} [Field L]
    {A : ValuationSubring L} [Infinite (ResidueField A)]
    {F : Type*} [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R₁ R₂ : RegularProlongation A F Fbar) {f : F} (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers) :
    ∃ (a : A) (g₁ : f - algebraMap L F a ∈ R₁.integers) (g₂ : f - algebraMap L F a ∈ R₂.integers),
      R₁.residue ⟨f - algebraMap L F a, g₁⟩ ≠ 0 ∧ R₂.residue ⟨f - algebraMap L F a, g₂⟩ ≠ 0 ∧
      R₁.residue ⟨f - algebraMap L F a, g₁⟩
        = R₁.residue ⟨f, h₁⟩ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∧
      R₂.residue ⟨f - algebraMap L F a, g₂⟩
        = R₂.residue ⟨f, h₂⟩ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
  classical
  have hinj : Function.Injective (algebraMap (ResidueField A) Fbar) :=
    (algebraMap (ResidueField A) Fbar).injective
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (({R₁.residue ⟨f, h₁⟩, R₂.residue ⟨f, h₂⟩} : Finset Fbar).preimage
      (algebraMap (ResidueField A) Fbar) hinj.injOn)
  have hc' : algebraMap (ResidueField A) Fbar c ∉ ({R₁.residue ⟨f, h₁⟩, R₂.residue ⟨f, h₂⟩} : Finset Fbar) :=
    fun h => hc (Finset.mem_preimage.mpr h)
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective c
  subst ha
  obtain ⟨g₁, e₁⟩ := regProl_residue_sub_algebraMap R₁ h₁ a
  obtain ⟨g₂, e₂⟩ := regProl_residue_sub_algebraMap R₂ h₂ a
  refine ⟨a, g₁, g₂, ?_, ?_, e₁, e₂⟩
  · rw [e₁]
    exact sub_ne_zero.mpr fun h => hc'.1 h.symm
  · rw [e₂]
    exact sub_ne_zero.mpr fun h => hc'.2 h.symm

omit [IsAlgClosed k] [DecidableEq k] in
private theorem exists_sub_algebraMap_residue_ne_zero (R : ProlongationTuple P)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers) :
    ∃ (a : A)
      (g₁ : f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a ∈ R.R₁.integers)
      (g₂ : f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a ∈ R.R₂.integers),
      R.R₁.residue ⟨f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a, g₁⟩ ≠ 0 ∧
      R.R₂.residue ⟨f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a, g₂⟩ ≠ 0 ∧
      R.residue₁ ⟨f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a, g₁⟩
        = R.residue₁ ⟨f, h₁⟩ - algebraMap k (modularFunctionFieldC k N) (red a) ∧
      R.residue₂ ⟨f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a, g₂⟩
        = R.residue₂ ⟨f, h₂⟩ - algebraMap k (modularFunctionFieldC k N) (red a) := by
  obtain ⟨a, g₁, g₂, n₁, n₂, e₁, e₂⟩ :=
    regProl_exists_residue_sub_algebraMap_ne_zero R.R₁ R.R₂ h₁ h₂
  refine ⟨a, g₁, g₂, n₁, n₂, ?_, ?_⟩
  · rw [residue₁_apply, residue₁_apply, e₁, map_sub, ι_algebraMap_eq, R.redBar_residue]
  · rw [residue₂_apply, residue₂_apply, e₂, map_sub, ι_algebraMap_eq, R.redBar_residue]

private theorem riemannRochSpace_mono' {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    {E D : Divisor K₀ F₀} (h : ∀ W, E W ≤ D W) : riemannRochSpace E ≤ riemannRochSpace D := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro W
  rcases hf W with h0 | hle
  · exact Or.inl h0
  · exact Or.inr (le_trans (neg_le_neg (h W)) hle)

private theorem aux_finiteDimensional_riemannRochSpace
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace E) := by
  classical
  obtain ⟨⟨V₀⟩, -, γ, D₀, hγ⟩ := stichtenothGenusExists_modularFunctionFieldBar (N * q)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, γ - E.degree ≤ n := ⟨(γ - E.degree).toNat, Int.self_le_toNat _⟩
  set D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) :=
    E + Finsupp.single V₀ (n : ℤ) with hD
  have hdeg : D.degree = E.degree + n := by
    rw [hD, map_add, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar (N * q) V₀,
      Nat.cast_one, mul_one]
  have hmax := hγ.isMax D
  rw [hdeg] at hmax
  have hpos : 0 < Module.finrank (AlgebraicClosure ℚ) (riemannRochSpace D) := by
    have h1 : (0 : ℤ) < (ell D : ℤ) := by linarith
    exact_mod_cast h1
  haveI : FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D) := Module.finite_of_finrank_pos hpos
  have hle : riemannRochSpace E ≤ riemannRochSpace D := riemannRochSpace_mono' fun W => by
    rw [hD, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs
    · exact le_add_of_nonneg_right (Int.natCast_nonneg n)
    · exact (add_zero _).symm.le
  exact Submodule.finiteDimensional_of_le hle

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_image_fst_of_not_fixed (R : ProlongationTuple P) (hDL : R.DivisorLawFst)
    {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hE : ∀ W, 0 ≤ E W)
    {f : modularFunctionFieldBar (N * q)} (hf : f ∈ riemannRochSpace E)
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) ≠ v) :
    R.residue₁ ⟨f, h₁⟩ = 0 ∨
      -(Finsupp.mapDomain P.reduceFst (P.fstDiv E) v) ≤ v.ord (R.residue₁ ⟨f, h₁⟩) := by
  classical
  by_cases h0 : R.residue₁ ⟨f, h₁⟩ = 0
  · exact Or.inl h0
  refine Or.inr ?_
  by_cases hlt : v.ord (R.residue₁ ⟨f, h₁⟩) < 0
  swap
  · push Not at hlt
    refine le_trans ?_ hlt
    rw [neg_nonpos]
    exact mapDomain_filter_nonneg P.reduceFst E P.IsStrictFst hE v
  obtain ⟨a, g₁, g₂, hne₁, hne₂, hr₁, -⟩ := exists_sub_algebraMap_residue_ne_zero R f h₁ h₂
  set g := f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a
  have hg0 : g ≠ 0 := by
    intro h
    apply hne₁
    have e : (⟨g, g₁⟩ : R.R₁.integers) = 0 := Subtype.ext h
    rw [e, map_zero]
  have hgE : g ∈ riemannRochSpace E :=
    sub_mem hf (algebraMap_mem_riemannRochSpace hE (a : AlgebraicClosure ℚ))
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor
    (self := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)) g hg0
  have hlaw := hDL g g₁ g₂ hne₁ hne₂ D hD v hv
  have hDE : ∀ W, -E W ≤ D W := fun W => by
    rw [hD W]
    exact ((mem_riemannRochSpace_iff.mp hgE) W).resolve_left hg0
  have hord : v.ord (R.residue₁ ⟨g, g₁⟩) = v.ord (R.residue₁ ⟨f, h₁⟩) := by
    rw [hr₁]
    exact ord_sub_algebraMap_of_ord_lt_zero v _ _ hlt
  rw [← hord, ← hlaw]
  exact neg_mapDomain_filter_le P.reduceFst D E P.IsStrictFst hDE v

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_image_snd_of_not_fixed (R : ProlongationTuple P) (hDL : R.DivisorLawSnd)
    {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hE : ∀ W, 0 ≤ E W)
    {f : modularFunctionFieldBar (N * q)} (hf : f ∈ riemannRochSpace E)
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (w : Place k (modularFunctionFieldC k N))
    (hw : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w) :
    R.residue₂ ⟨f, h₂⟩ = 0 ∨
      -(Finsupp.mapDomain P.reduceSnd (P.sndDiv E) w) ≤ w.ord (R.residue₂ ⟨f, h₂⟩) := by
  classical
  by_cases h0 : R.residue₂ ⟨f, h₂⟩ = 0
  · exact Or.inl h0
  refine Or.inr ?_
  by_cases hlt : w.ord (R.residue₂ ⟨f, h₂⟩) < 0
  swap
  · push Not at hlt
    refine le_trans ?_ hlt
    rw [neg_nonpos]
    exact mapDomain_filter_nonneg P.reduceSnd E P.IsStrictSnd hE w
  obtain ⟨a, g₁, g₂, hne₁, hne₂, -, hr₂⟩ := exists_sub_algebraMap_residue_ne_zero R f h₁ h₂
  set g := f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a
  have hg0 : g ≠ 0 := by
    intro h
    apply hne₂
    have e : (⟨g, g₂⟩ : R.R₂.integers) = 0 := Subtype.ext h
    rw [e, map_zero]
  have hgE : g ∈ riemannRochSpace E :=
    sub_mem hf (algebraMap_mem_riemannRochSpace hE (a : AlgebraicClosure ℚ))
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor
    (self := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)) g hg0
  have hlaw := hDL g g₁ g₂ hne₁ hne₂ D hD w hw
  have hDE : ∀ W, -E W ≤ D W := fun W => by
    rw [hD W]
    exact ((mem_riemannRochSpace_iff.mp hgE) W).resolve_left hg0
  have hord : w.ord (R.residue₂ ⟨g, g₂⟩) = w.ord (R.residue₂ ⟨f, h₂⟩) := by
    rw [hr₂]
    exact ord_sub_algebraMap_of_ord_lt_zero w _ _ hlt
  rw [← hord, ← hlaw]
  exact neg_mapDomain_filter_le P.reduceSnd D E P.IsStrictSnd hDE w

private theorem ramificationIndexAlong_pos {K₀ F₀ F₁ : Type*} [Field K₀] [Field F₀] [Field F₁]
    [Algebra K₀ F₀] [Algebra K₀ F₁] (ψ : F₀ →ₐ[K₀] F₁) (hψ : ψ.toRingHom.IsIntegral)
    (w : Place K₀ F₁) : 0 < Place.ramificationIndexAlong ψ w := by
  letI := algebraAlong ψ
  haveI := isIntegral_along ψ hψ
  exact w.ramificationIndex_pos (F := F₀)

private theorem mapDomain_filter_congr {X Y : Type*} (r : X → Y) (E : X →₀ ℤ) (p₁ p₂ : X → Prop)
    {d₁ : DecidablePred p₁} {d₂ : DecidablePred p₂} (v : Y) (h : ∀ V, r V = v → (p₁ V ↔ p₂ V)) :
    Finsupp.mapDomain r (E.filter p₁) v = Finsupp.mapDomain r (E.filter p₂) v := by
  classical
  have key : ∀ (p : X → Prop) (d : DecidablePred p) (a : X) (m : ℤ), r a ≠ v →
      Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d (Finsupp.single a m)) v = 0 := by
    intro p d a m hav
    by_cases hp : p a
    · rw [Finsupp.filter_single_of_pos p hp, Finsupp.mapDomain_single, Finsupp.single_apply,
        if_neg hav]
    · rw [Finsupp.filter_single_of_neg p hp, Finsupp.mapDomain_zero, Finsupp.zero_apply]
  induction E using Finsupp.induction_linear with
  | zero => rw [Finsupp.filter_zero, Finsupp.filter_zero]
  | add f₁ f₂ h₁ h₂ =>
    rw [Finsupp.filter_add, Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.mapDomain_add,
      Finsupp.add_apply, Finsupp.add_apply, h₁, h₂]
  | single a m =>
    by_cases hav : r a = v
    · by_cases hp : p₁ a
      · rw [Finsupp.filter_single_of_pos p₁ hp, Finsupp.filter_single_of_pos p₂ ((h a hav).mp hp)]
      · rw [Finsupp.filter_single_of_neg p₁ hp,
          Finsupp.filter_single_of_neg p₂ (fun h2 => hp ((h a hav).mpr h2))]
    · rw [key p₁ d₁ a m hav, key p₂ d₂ a m hav]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem heckeAlphaBar_jN_sub (a : A) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
      = jFun N q
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
              (a : AlgebraicClosure ℚ) := by
  rw [map_sub]
  congr 1

omit [IsAlgClosed k] [DecidableEq k] in
private theorem heckeBetaBar_jN_sub (a : A) :
    heckeBetaBar (AlgebraicClosure ℚ) N q
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
      = jQFun N q
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
              (a : AlgebraicClosure ℚ) := by
  rw [map_sub, AlgHom.commutes]
  congr 1
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  exact (ModularCurve.coeffSemilinearAut.coeffMap_qExpand
    (algebraMap ℚ (AlgebraicClosure ℚ)) q jq).symm

private theorem ord_restrictAlong_nonpos {K₀ F₀ F₁ : Type*} [Field K₀] [Field F₀] [Field F₁]
    [Algebra K₀ F₀] [Algebra K₀ F₁] (ψ : F₀ →ₐ[K₀] F₁) (hψ : ψ.toRingHom.IsIntegral)
    (c : Place K₀ F₁) (x : F₀)
    (hc : c.ord (ψ x) ≤ 0) : (c.restrictAlong ψ hψ).ord x ≤ 0 := by
  have hord := Place.ord_restrictAlong ψ hψ c x
  have he := ramificationIndexAlong_pos ψ hψ c
  by_contra hlt
  push Not at hlt
  have hprod := mul_pos (Int.natCast_pos.mpr he) hlt
  rw [← hord] at hprod
  exact absurd hc (not_le.mpr hprod)

private theorem ord_restrictAlong_pos {K₀ F₀ F₁ : Type*} [Field K₀] [Field F₀] [Field F₁]
    [Algebra K₀ F₀] [Algebra K₀ F₁] (ψ : F₀ →ₐ[K₀] F₁) (hψ : ψ.toRingHom.IsIntegral)
    (c : Place K₀ F₁) (x : F₀)
    (hc : 0 < c.ord (ψ x)) : 0 < (c.restrictAlong ψ hψ).ord x := by
  have hord := Place.ord_restrictAlong ψ hψ c x
  by_contra hle
  push Not at hle
  have hprod := mul_nonpos_of_nonneg_of_nonpos
    (Int.natCast_nonneg (Place.ramificationIndexAlong ψ c)) hle
  rw [← hord] at hprod
  exact absurd hc (not_lt.mpr hprod)

omit [IsAlgClosed k] [DecidableEq k] in
private theorem reduceFst_ord_lt_zero_of_isCuspidal
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hc : IsCuspidal P c) :
    (P.reduceFst c).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
  refine P.d0_j_pole _ (fun a => ?_)
  refine ord_restrictAlong_nonpos (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα c _ ?_
  rw [heckeAlphaBar_jN_sub]
  exact hc a

omit [IsAlgClosed k] [DecidableEq k] in
private theorem reduceSnd_ord_lt_zero_of_isCuspidal'
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hc : IsCuspidal' P c) :
    (P.reduceSnd c).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
  refine P.d0_j_pole _ (fun a => ?_)
  refine ord_restrictAlong_nonpos (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ c _ ?_
  rw [heckeBetaBar_jN_sub]
  exact hc a

omit [IsAlgClosed k] [DecidableEq k] in
private theorem isCuspidal_of_reduceFst_ord_lt_zero
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : (P.reduceFst V).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0) :
    IsCuspidal P V := by
  intro a
  by_contra hpos
  push Not at hpos
  rw [← heckeAlphaBar_jN_sub] at hpos
  have hup := ord_restrictAlong_pos (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V _ hpos
  have hdown : 0 < (P.reduceFst V).ord ((⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      - algebraMap k (modularFunctionFieldC k N) (red a)) := P.d0_j _ a hup
  have hne : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      - algebraMap k (modularFunctionFieldC k N) (red a) ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hdown
    exact lt_irrefl _ hdown
  have hmem := (P.reduceFst V).mem_of_ord_nonneg hne hdown.le
  have hj : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      ∈ (P.reduceFst V).toValuationSubring := by
    have h := add_mem hmem ((P.reduceFst V).algebraMap_mem' (red a))
    rwa [sub_add_cancel] at h
  exact absurd hV (not_lt.mpr ((P.reduceFst V).ord_nonneg_of_mem hj))

omit [DecidableEq k] in
private theorem ord_frob_jGeom_eq (w : Place k (modularFunctionFieldC k N)) :
    (frobOnPlacesGeomLevel k N data hKr w).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      = w.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) := by
  have hperf : ∀ x : k, ∃ d : k, d ^ q = x := fun x =>
    IsAlgClosed.exists_pow_nat_eq x (Fact.out : q.Prime).pos
  exact ord_frobOnPlaces_of_pow_eq k N data hKr hperf (frobeniusGeomLevel_jq k N data hKr) w

omit [IsAlgClosed k] [DecidableEq k] in
open Classical in
private theorem aux_cuspMass_fst_notZero (hqN : ¬ q ∣ N)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hc : IsInftySide P c) :
    Finsupp.mapDomain P.reduceFst (E.filter (fun V => ¬ IsZeroSide P V)) (P.reduceFst c)
      = Finsupp.mapDomain P.reduceFst (E.filter (IsInftySide P)) (P.reduceFst c) := by
  have hpole := reduceFst_ord_lt_zero_of_isCuspidal c hc.1
  refine mapDomain_filter_congr P.reduceFst E _ _ (P.reduceFst c) (fun V hV => ?_)
  have hVc : IsCuspidal P V := isCuspidal_of_reduceFst_ord_lt_zero V (by rw [hV]; exact hpole)
  constructor
  · intro hnz
    rcases isInftySide_or_isZeroSide_of_isCuspidal P hqN V hVc with h | h
    · exact h
    · exact absurd h hnz
  · intro hinf hz
    exact not_isInftySide_of_isZeroSide P V hz hinf

private theorem ord_nonpos_of_ord_restrictAlong_nonpos {K₀ F₀ F₁ : Type*} [Field K₀] [Field F₀]
    [Field F₁] [Algebra K₀ F₀] [Algebra K₀ F₁] (ψ : F₀ →ₐ[K₀] F₁) (hψ : ψ.toRingHom.IsIntegral)
    (c : Place K₀ F₁) (x : F₀) (hc : (c.restrictAlong ψ hψ).ord x ≤ 0) : c.ord (ψ x) ≤ 0 := by
  rw [Place.ord_restrictAlong ψ hψ c x]
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hc

private theorem intPolyRingHom_ext {S : Type*} [Semiring S] {f g : Polynomial ℤ →+* S}
    (h : f Polynomial.X = g Polynomial.X) : f = g :=
  Polynomial.ringHom_ext
    (fun a => DFunLike.congr_fun (RingHom.ext_int (f.comp Polynomial.C) (g.comp Polynomial.C)) a) h

private theorem mem_valuationSubring_of_eval₂_aeval_eq_zero {F : Type*} [Field F]
    (O : ValuationSubring F) {y x : F} (hy : y ∈ O) (Φ : Polynomial (Polynomial ℤ)) (hΦ : Φ.Monic)
    (h : Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x = 0) : x ∈ O := by
  let f : Polynomial ℤ →+* O := (Polynomial.aeval (R := ℤ) (⟨y, hy⟩ : O)).toRingHom
  have hcomp : (algebraMap O F).comp f = (Polynomial.aeval (R := ℤ) y).toRingHom := by
    apply intPolyRingHom_ext
    show algebraMap O F (Polynomial.aeval (R := ℤ) (⟨y, hy⟩ : O) Polynomial.X)
      = Polynomial.aeval (R := ℤ) y Polynomial.X
    rw [Polynomial.aeval_X, Polynomial.aeval_X]
    rfl
  have hint : IsIntegral O x := ⟨Φ.map f, hΦ.map f, by rw [Polynomial.eval₂_map, hcomp]; exact h⟩
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := F)).mp hint
  rw [← hz]
  exact z.2

omit [Fact q.Prime] [IsAlgClosed k] [DecidableEq k] in
private theorem modularPolynomial_eval₂_jGeomGen_jNGeomGen (Φ : ModularPolynomialData N) :
    Φ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jGeomGen k N)).toRingHom (jNGeomGen k N) = 0 := by
  have h := ModularPolynomialData.eval_jqNModC_mul_eq_zero Φ k 1
  have e1 : jqNModC k 1 = jqModC k := qExpand_one_apply _
  rw [e1] at h
  simp only [one_mul] at h
  apply Subtype.val_injective
  have hcomp : (algebraMap (modularFunctionFieldC k N) (LaurentSeries k)).comp
      (Polynomial.aeval (R := ℤ) (jGeomGen k N)).toRingHom
        = (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom := by
    apply intPolyRingHom_ext
    show algebraMap (modularFunctionFieldC k N) (LaurentSeries k)
        (Polynomial.aeval (R := ℤ) (jGeomGen k N) Polynomial.X)
      = Polynomial.aeval (R := ℤ) (jqModC k) Polynomial.X
    rw [Polynomial.aeval_X, Polynomial.aeval_X]
    rfl
  have hval := Polynomial.hom_eval₂ Φ.Φ (Polynomial.aeval (R := ℤ) (jGeomGen k N)).toRingHom
    (algebraMap (modularFunctionFieldC k N) (LaurentSeries k)) (jNGeomGen k N)
  rw [hcomp] at hval
  exact hval.trans h

omit [Fact q.Prime] [IsAlgClosed k] [DecidableEq k] in
private theorem aux_jNGeomGen_mem_of_jGeomGen_mem (v : Place k (modularFunctionFieldC k N))
    (hv : jGeomGen k N ∈ v.toValuationSubring) : jNGeomGen k N ∈ v.toValuationSubring := by
  obtain ⟨Φ⟩ := nonempty_modularPolynomialData N
  exact mem_valuationSubring_of_eval₂_aeval_eq_zero v.toValuationSubring hv Φ.Φ Φ.monic
    (modularPolynomial_eval₂_jGeomGen_jNGeomGen Φ)

omit [IsAlgClosed k] [DecidableEq k] in
private theorem ord_jGeom_lt_zero_of_not_isAffineGeomPlace (v : Place k (modularFunctionFieldC k N))
    (hna : ¬ IsAffineGeomPlace k N v) :
    v.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
  by_contra hge
  push Not at hge
  apply hna
  have hj : jGeomGen k N ∈ v.toValuationSubring := by
    by_cases h0 : jGeomGen k N = 0
    · rw [h0]
      exact zero_mem _
    · exact v.mem_of_ord_nonneg h0 hge
  exact ⟨hj, aux_jNGeomGen_mem_of_jGeomGen_mem v hj⟩

omit [IsAlgClosed k] [DecidableEq k] in
private theorem forall_ord_sub_le_zero_of_sp_ord_lt_zero
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : (P.sp w).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0) :
    ∀ a : A, w.ord
        ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0 := by
  intro a
  by_contra hpos
  push Not at hpos
  have hdown := P.d0_j w a hpos
  have hne : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)
      - algebraMap k (modularFunctionFieldC k N) (red a) ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at hdown
    exact lt_irrefl _ hdown
  have hmem := (P.sp w).mem_of_ord_nonneg hne hdown.le
  have hj : (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) ∈ (P.sp w).toValuationSubring := by
    have h := add_mem hmem ((P.sp w).algebraMap_mem' (red a))
    rwa [sub_add_cancel] at h
  exact absurd hw (not_lt.mpr ((P.sp w).ord_nonneg_of_mem hj))

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_exists_isInftySide_reduceFst_eq (hqN : ¬ q ∣ N) (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (hna : ¬ IsAffineGeomPlace k N v) :
    ∃ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      IsInftySide P c ∧ P.reduceFst c = v := by
  have _ := hv
  have hpole := ord_jGeom_lt_zero_of_not_isAffineGeomPlace v hna
  obtain ⟨w, hw⟩ := P.d4 v
  have hwc := forall_ord_sub_le_zero_of_sp_ord_lt_zero (P := P) w (by rw [hw]; exact hpole)
  obtain ⟨c, hc, τ, hτ, hval⟩ :=
    exists_place_restrictAlong_heckeAlphaBar_eq_and_hasValue_tInfty q A N k red data hKr hα hqN w hwc
  have hrF : P.reduceFst c = v := by
    show P.sp (c.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = v
    rw [hc, hw]
  exact ⟨c, ⟨isCuspidal_of_reduceFst_ord_lt_zero c (by rw [hrF]; exact hpole), τ, hτ, hval⟩, hrF⟩

omit [IsAlgClosed k] [DecidableEq k] in
private theorem isCuspidal'_of_reduceSnd_ord_lt_zero
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : (P.reduceSnd V).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0) :
    IsCuspidal' P V := by
  intro a
  have h := forall_ord_sub_le_zero_of_sp_ord_lt_zero (P := P)
    (V.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) hV a
  rw [← heckeBetaBar_jN_sub]
  exact ord_nonpos_of_ord_restrictAlong_nonpos (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ V _ h

omit [DecidableEq k] in
private theorem aux_exists_isZeroSide_reduceSnd_eq (hqN : ¬ q ∣ N) (w : Place k (modularFunctionFieldC k N))
    (hw : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (hna : ¬ IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr w)) :
    ∃ c : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      IsZeroSide P c ∧ P.reduceSnd c = w := by
  have _ := hw
  have hpole : w.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
    rw [← ord_frob_jGeom_eq (data := data) (hKr := hKr) w]
    exact ord_jGeom_lt_zero_of_not_isAffineGeomPlace _ hna
  obtain ⟨w', hw'⟩ := P.d4 w
  have hwc := forall_ord_sub_le_zero_of_sp_ord_lt_zero (P := P) w' (by rw [hw']; exact hpole)
  obtain ⟨c, hc, τ, hτ, hval⟩ :=
    exists_place_restrictAlong_heckeBetaBar_eq_and_hasValue_tZero q A N k red data hKr hβ hqN w' hwc
  have hrS : P.reduceSnd c = w := by
    show P.sp (c.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) = w
    rw [hc, hw']
  exact ⟨c, ⟨isCuspidal'_of_reduceSnd_ord_lt_zero c (by rw [hrS]; exact hpole), τ, hτ, hval⟩, hrS⟩

omit [IsAlgClosed k] [DecidableEq k] in
open Classical in
private theorem aux_image_fst_cusp (R : ProlongationTuple P) (hCL : R.CuspLawInfty) (hqN : ¬ q ∣ N)
    {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hE : ∀ W, 0 ≤ E W)
    {f : modularFunctionFieldBar (N * q)} (hf : f ∈ riemannRochSpace E)
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (hna : ¬ IsAffineGeomPlace k N v) :
    R.residue₁ ⟨f, h₁⟩ = 0 ∨
      -(Finsupp.mapDomain P.reduceFst (E.filter (fun V => ¬ IsZeroSide P V)) v)
        ≤ v.ord (R.residue₁ ⟨f, h₁⟩) := by
  by_cases h0 : R.residue₁ ⟨f, h₁⟩ = 0
  · exact Or.inl h0
  refine Or.inr ?_
  by_cases hlt : v.ord (R.residue₁ ⟨f, h₁⟩) < 0
  swap
  · push Not at hlt
    refine le_trans ?_ hlt
    rw [neg_nonpos]
    exact mapDomain_filter_nonneg P.reduceFst E _ hE v
  obtain ⟨c, hc, hcv⟩ := aux_exists_isInftySide_reduceFst_eq (P := P) hqN v hv hna
  subst hcv
  rw [aux_cuspMass_fst_notZero hqN E c hc]
  obtain ⟨a, g₁, g₂, hne₁, hne₂, hr₁, -⟩ := exists_sub_algebraMap_residue_ne_zero R f h₁ h₂
  set g := f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a
  have hg0 : g ≠ 0 := by
    intro h
    apply hne₁
    have e : (⟨g, g₁⟩ : R.R₁.integers) = 0 := Subtype.ext h
    rw [e, map_zero]
  have hgE : g ∈ riemannRochSpace E :=
    sub_mem hf (algebraMap_mem_riemannRochSpace hE (a : AlgebraicClosure ℚ))
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor
    (self := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)) g hg0
  have hlaw := hCL g g₁ g₂ hne₁ hne₂ D hD c hc
  have hDE : ∀ W, -E W ≤ D W := fun W => by
    rw [hD W]
    exact ((mem_riemannRochSpace_iff.mp hgE) W).resolve_left hg0
  have hord : (P.reduceFst c).ord (R.residue₁ ⟨g, g₁⟩)
      = (P.reduceFst c).ord (R.residue₁ ⟨f, h₁⟩) := by
    rw [hr₁]
    exact ord_sub_algebraMap_of_ord_lt_zero _ _ _ hlt
  rw [← hord, ← hlaw]
  exact neg_mapDomain_filter_le P.reduceFst D E (IsInftySide P) hDE (P.reduceFst c)

omit [DecidableEq k] in
open Classical in
private theorem aux_image_snd_cusp (R : ProlongationTuple P) (hCL : R.CuspLawZero) (hqN : ¬ q ∣ N)
    {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hE : ∀ W, 0 ≤ E W)
    {f : modularFunctionFieldBar (N * q)} (hf : f ∈ riemannRochSpace E)
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (w : Place k (modularFunctionFieldC k N))
    (hw : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w)
    (hna : ¬ IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr w)) :
    R.residue₂ ⟨f, h₂⟩ = 0 ∨
      -(Finsupp.mapDomain P.reduceSnd (E.filter (IsZeroSide P)) w)
        ≤ w.ord (R.residue₂ ⟨f, h₂⟩) := by
  by_cases h0 : R.residue₂ ⟨f, h₂⟩ = 0
  · exact Or.inl h0
  refine Or.inr ?_
  by_cases hlt : w.ord (R.residue₂ ⟨f, h₂⟩) < 0
  swap
  · push Not at hlt
    refine le_trans ?_ hlt
    rw [neg_nonpos]
    exact mapDomain_filter_nonneg P.reduceSnd E _ hE w
  obtain ⟨c, hc, hcw⟩ := aux_exists_isZeroSide_reduceSnd_eq (P := P) hqN w hw hna
  subst hcw
  obtain ⟨a, g₁, g₂, hne₁, hne₂, -, hr₂⟩ := exists_sub_algebraMap_residue_ne_zero R f h₁ h₂
  set g := f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) a
  have hg0 : g ≠ 0 := by
    intro h
    apply hne₂
    have e : (⟨g, g₂⟩ : R.R₂.integers) = 0 := Subtype.ext h
    rw [e, map_zero]
  have hgE : g ∈ riemannRochSpace E :=
    sub_mem hf (algebraMap_mem_riemannRochSpace hE (a : AlgebraicClosure ℚ))
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor
    (self := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)) g hg0
  have hlaw := hCL g g₁ g₂ hne₁ hne₂ D hD c hc
  have hDE : ∀ W, -E W ≤ D W := fun W => by
    rw [hD W]
    exact ((mem_riemannRochSpace_iff.mp hgE) W).resolve_left hg0
  have hord : (P.reduceSnd c).ord (R.residue₂ ⟨g, g₂⟩)
      = (P.reduceSnd c).ord (R.residue₂ ⟨f, h₂⟩) := by
    rw [hr₂]
    exact ord_sub_algebraMap_of_ord_lt_zero _ _ _ hlt
  rw [← hord, ← hlaw]
  exact neg_mapDomain_filter_le P.reduceSnd D E (IsZeroSide P) hDE (P.reduceSnd c)

private theorem mapDomain_filter_apply_eq_sum_of {X Y : Type*} [DecidableEq Y] (r : X → Y)
    (D : X →₀ ℤ) (p : X → Prop) [DecidablePred p] (a : X) (S : Finset X)
    (hS : ∀ i, r i = r a → D i ≠ 0 → i ∈ S) (hS' : ∀ i ∈ S, r i = r a) :
    Finsupp.mapDomain r (D.filter p) (r a) = ∑ i ∈ S, (if p i then D i else 0) := by
  rw [Finsupp.mapDomain_apply_eq_sum]
  have hsub : (D.filter p).support.filter (fun i => r i = r a) ⊆ S := by
    intro i hi
    rw [Finset.mem_filter, Finsupp.mem_support_iff, Finsupp.filter_apply] at hi
    refine hS i hi.2 (fun h0 => hi.1 ?_)
    rw [h0, ite_self]
  have hsum : ∑ i ∈ (D.filter p).support.filter (fun i => r i = r a), (D.filter p) i
      = ∑ i ∈ S, (D.filter p) i :=
    Finset.sum_subset hsub (fun i hiS hnot => Finsupp.notMem_support_iff.mp
      (fun hmem => hnot (Finset.mem_filter.mpr ⟨hmem, hS' i hiS⟩)))
  rw [hsum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.filter_apply p D i

private theorem residue_mk_congr {L : Type*} [Field L] {A₀ : ValuationSubring L} {F : Type*} [Field F]
    [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A₀) Fbar]
    (R₀ : RegularProlongation A₀ F Fbar) {f g : F} (e : f = g) (hf : f ∈ R₀.integers)
    (hg : g ∈ R₀.integers) : R₀.residue ⟨f, hf⟩ = R₀.residue ⟨g, hg⟩ := by
  subst e
  rfl

private theorem jqModC_ne_zero' (K : Type*) [CommRing K] [Nontrivial K] : jqModC K ≠ 0 := by
  intro h
  have hc : (jqModC K).coeff (-1 : ℤ) = (0 : LaurentSeries K).coeff (-1 : ℤ) := by rw [h]
  rw [coeff_jqModC_neg_one] at hc
  simp at hc

private theorem qExpand_jqModC_ne_zero (K : Type*) [CommRing K] [Nontrivial K] (n : ℕ) [NeZero n] :
    qExpand K n (jqModC K) ≠ 0 := by
  intro h
  have hc : (qExpand K n (jqModC K)).coeff ((n : ℤ) * (-1 : ℤ))
      = (0 : LaurentSeries K).coeff ((n : ℤ) * (-1 : ℤ)) := by
    rw [h]
  rw [qExpand_coeff_mul, coeff_jqModC_neg_one] at hc
  simp at hc

private theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) :=
  map_jqModC (K := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ))

private theorem coe_jFun :
    ((jFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) :=
  coeffEmb_jq

private theorem coe_jQFun :
    ((jQFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ)) := by
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = _
  rw [← coeffEmb_jq]
  exact ModularCurve.coeffSemilinearAut.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq

private theorem atkinLehnerBar_jFun_jQFun :
    (atkinLehnerBar N q (jFun N q) = jQFun N q ∧ atkinLehnerBar N q (jQFun N q) = jFun N q) ∨
    (atkinLehnerBar N q (jFun N q) = jFun N q ∧ atkinLehnerBar N q (jQFun N q) = jQFun N q) := by
  by_cases h : ∃ σ : modularFunctionFieldFull (N * q) ≃ₐ[ℚ] modularFunctionFieldFull (N * q),
      IsAtkinLehnerAutFull N q σ
  · left
    have hw := (isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q h) 1 inferInstance (one_dvd N)
    have e1 : (⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (one_dvd _)⟩ : modularFunctionFieldFull (N * q))
        = ⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ :=
      Subtype.ext (qExpand_one_apply _)
    have e2 : (⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (mul_dvd_mul_right (one_dvd N) q)⟩ :
          modularFunctionFieldFull (N * q))
        = ⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩ :=
      Subtype.ext (by
        show qExpand ℚ (1 * q) jq = qExpand ℚ q jq
        simp only [one_mul])
    have hσ₁ : atkinLehnerInvolutionFull N q ⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩
        = ⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩ := by
      rw [← e1, hw.1, e2]
    have hσ₂ : atkinLehnerInvolutionFull N q ⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩
        = ⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ := by
      rw [← e2, hw.2, e1]
    constructor
    · apply Subtype.ext
      show ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
          ⟨coeffEmb (AlgebraicClosure ℚ)
              ((⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ :
                modularFunctionFieldFull (N * q)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ :
                modularFunctionFieldFull (N * q)).2⟩ : modularFunctionFieldBar (N * q)) :
            LaurentSeries (AlgebraicClosure ℚ))
        = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
      rw [coe_geomAut_coeffEmb, hσ₁]
    · apply Subtype.ext
      show ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
          ⟨coeffEmb (AlgebraicClosure ℚ)
              ((⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩ :
                modularFunctionFieldFull (N * q)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩ :
                modularFunctionFieldFull (N * q)).2⟩ : modularFunctionFieldBar (N * q)) :
            LaurentSeries (AlgebraicClosure ℚ))
        = coeffEmb (AlgebraicClosure ℚ) jq
      rw [coe_geomAut_coeffEmb, hσ₂]
  · right
    have hr := atkinLehnerInvolutionFull_eq_refl N q h
    have hid : atkinLehnerBar N q = 1 := by
      show geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q) = 1
      rw [hr]
      exact map_one (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)))
    rw [hid]
    exact ⟨rfl, rfl⟩

omit [IsAlgClosed k] [DecidableEq k] in
private theorem jFun_mem_integers_residue_ne_zero (R : ProlongationTuple P) :
    ∃ h : jFun N q ∈ R.R₁.integers, R.R₁.residue ⟨jFun N q, h⟩ ≠ 0 := by
  have hval : coeffMap A.subtype (jqModC A) = (jFun N q : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coe_jFun]
    exact map_jqModC A.subtype
  have hy : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar (N * q) := by
    rw [hval]
    exact (jFun N q).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (jqModC A) hy
  have e : (⟨coeffMap A.subtype (jqModC A), hy⟩ : modularFunctionFieldBar (N * q)) = jFun N q :=
    Subtype.ext hval
  have h' : jFun N q ∈ R.R₁.integers := by
    rw [← e]
    exact h
  refine ⟨h', ?_⟩
  rw [← residue_mk_congr R.R₁ e h h']
  intro h0
  have hc : ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) N) :
      LaurentSeries (ResidueField A)) = 0 := by
    rw [h0]
    rfl
  rw [hres] at hc
  exact jqModC_ne_zero' (ResidueField A) ((map_jqModC (IsLocalRing.residue A)).symm.trans hc)

omit [IsAlgClosed k] [DecidableEq k] in
private theorem jQFun_mem_integers_residue_ne_zero (R : ProlongationTuple P) :
    ∃ h : jQFun N q ∈ R.R₁.integers, R.R₁.residue ⟨jQFun N q, h⟩ ≠ 0 := by
  have hval : coeffMap A.subtype (qExpand A q (jqModC A))
      = (jQFun N q : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coe_jQFun, ModularCurve.coeffSemilinearAut.coeffMap_qExpand]
    congr 1
    exact map_jqModC A.subtype
  have hy : coeffMap A.subtype (qExpand A q (jqModC A)) ∈ modularFunctionFieldBar (N * q) := by
    rw [hval]
    exact (jQFun N q).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (qExpand A q (jqModC A)) hy
  have e : (⟨coeffMap A.subtype (qExpand A q (jqModC A)), hy⟩ : modularFunctionFieldBar (N * q))
      = jQFun N q :=
    Subtype.ext hval
  have h' : jQFun N q ∈ R.R₁.integers := by
    rw [← e]
    exact h
  refine ⟨h', ?_⟩
  rw [← residue_mk_congr R.R₁ e h h']
  intro h0
  have hc : ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) N) :
      LaurentSeries (ResidueField A)) = 0 := by
    rw [h0]
    rfl
  rw [hres, ModularCurve.coeffSemilinearAut.coeffMap_qExpand] at hc
  refine qExpand_jqModC_ne_zero (ResidueField A) q ?_
  rw [← hc]
  congr 1
  exact (map_jqModC (IsLocalRing.residue A)).symm

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_jFun_commonUnit (R : ProlongationTuple P) :
    ∃ (h₁ : jFun N q ∈ R.R₁.integers) (h₂ : jFun N q ∈ R.R₂.integers),
      R.R₁.residue ⟨jFun N q, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨jFun N q, h₂⟩ ≠ 0 := by
  obtain ⟨h₁, hr₁⟩ := jFun_mem_integers_residue_ne_zero R
  obtain ⟨g₁, gr₁⟩ := jQFun_mem_integers_residue_ne_zero R
  rcases atkinLehnerBar_jFun_jQFun (N := N) (q := q) with ⟨hJ, -⟩ | ⟨hJ, -⟩
  · have h₂ : jFun N q ∈ R.R₂.integers := by
      rw [R.mem_integers₂_iff, hJ]
      exact g₁
    refine ⟨h₁, h₂, hr₁, ?_⟩
    rw [R.residue₂_eq, residue_mk_congr R.R₁ hJ _ g₁]
    exact gr₁
  · have h₂ : jFun N q ∈ R.R₂.integers := by
      rw [R.mem_integers₂_iff, hJ]
      exact h₁
    refine ⟨h₁, h₂, hr₁, ?_⟩
    rw [R.residue₂_eq, residue_mk_congr R.R₁ hJ _ h₁]
    exact hr₁

private theorem mem_image_of_mapDomain_ne_zero {X Y : Type*} [DecidableEq Y] {E D : X →₀ ℤ}
    (hD : D.support ⊆ E.support) (r : X → Y) {v : Y} (hv : Finsupp.mapDomain r D v ≠ 0) :
    v ∈ E.support.image r :=
  Finset.image_subset_image hD (Finsupp.mapDomain_support (Finsupp.mem_support_iff.mpr hv))

private theorem support_filter_subset {X : Type*} (E : X →₀ ℤ) (p : X → Prop) [DecidablePred p] :
    (E.filter p).support ⊆ E.support := by
  rw [Finsupp.support_filter]
  exact Finset.filter_subset _ _

section Eval

variable {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
  {s : Place k (modularFunctionFieldC k N) → ℤ}
  {hs : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
    IsAffineGeomPlace k N v → -(Finsupp.mapDomain P.reduceFst E v) ≤ s v ∧ s v ≤ 0}

end Eval

section Bookkeeping

private def tmass {X : Type*} (D : X →₀ ℤ) : ℤ := D.sum fun _ m => m

private theorem tmass_add {X : Type*} (D₁ D₂ : X →₀ ℤ) : tmass (D₁ + D₂) = tmass D₁ + tmass D₂ :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private theorem tmass_mapDomain {X Y : Type*} (r : X → Y) (D : X →₀ ℤ) :
    tmass (Finsupp.mapDomain r D) = tmass D :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

private theorem degree_eq_tmass {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    (h : ∀ v : Place K₀ F₀, v.deg = 1) (D : Divisor K₀ F₀) : D.degree = tmass D := by
  induction D using Finsupp.induction_linear with
  | zero =>
    unfold tmass
    rw [map_zero, Finsupp.sum_zero_index]
  | add f g hf hg => rw [map_add, tmass_add, hf, hg]
  | single v n =>
    unfold tmass
    rw [Divisor.degree_single, h v, Nat.cast_one, mul_one, Finsupp.sum_single_index rfl]

private theorem mapDomain_filter_eq_zero {X Y : Type*} (r : X → Y) (E : X →₀ ℤ) (p₁ : X → Prop)
    {d₁ : DecidablePred p₁} (v : Y) (h : ∀ V, r V = v → ¬ p₁ V) :
    Finsupp.mapDomain r (E.filter p₁) v = 0 := by
  classical
  induction E using Finsupp.induction_linear with
  | zero => rw [Finsupp.filter_zero, Finsupp.mapDomain_zero, Finsupp.zero_apply]
  | add f₁ f₂ h₁ h₂ =>
    rw [Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.add_apply, h₁, h₂, add_zero]
  | single a m =>
    by_cases hp : p₁ a
    · have hav : ¬ r a = v := fun hav => h a hav hp
      rw [Finsupp.filter_single_of_pos p₁ hp, Finsupp.mapDomain_single, Finsupp.single_apply,
        if_neg hav]
    · rw [Finsupp.filter_single_of_neg p₁ hp, Finsupp.mapDomain_zero, Finsupp.zero_apply]

section BoxEval

variable {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
  {s : Place k (modularFunctionFieldC k N) → ℤ}
  {hs : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
    IsAffineGeomPlace k N v → -(Finsupp.mapDomain P.reduceFst E v) ≤ s v ∧ s v ≤ 0}

end BoxEval

omit [DecidableEq k] in
private theorem deg_eq_one_downstairs (v : Place k (modularFunctionFieldC k N)) : v.deg = 1 := by
  haveI : IsCurveOver k (modularFunctionFieldC k N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField k N
  exact deg_eq_one_modularFunctionFieldC k N v

end Bookkeeping

section LatticeRoad

private def IsGoodAux (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) : Prop :=
  (∀ V, 0 ≤ E V) ∧ P.IsGoodDiv E

open Classical in
private noncomputable def fibreDivFst (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor k (modularFunctionFieldC k N) :=
  Finsupp.mapDomain P.reduceFst (E.filter P.IsStrictFst)

open Classical in
private noncomputable def fibreDivSnd (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor k (modularFunctionFieldC k N) :=
  Finsupp.mapDomain P.reduceSnd (E.filter P.IsStrictSnd)

private def PairCond (D₁ D₂ : Divisor k (modularFunctionFieldC k N)) (W : Finset (Place k (modularFunctionFieldC k N)))
    (g : ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N)) : Prop :=
  (∀ w, g.1 = 0 ∨ -D₁ w ≤ w.ord g.1) ∧ (∀ w, g.2 = 0 ∨ -D₂ w ≤ w.ord g.2) ∧
    ∀ nd ∈ nodePairsOfPlaces (arithFrobC q k N) W, ∃ c : k, nd.1.HasValue g.1 c ∧ nd.2.HasValue g.2 c

private theorem residue_mk_congr' {L : Type*} [Field L] {A₀ : ValuationSubring L} {F : Type*} [Field F]
    [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A₀) Fbar]
    (R₀ : RegularProlongation A₀ F Fbar) {f g : F} (e : f = g) (hf : f ∈ R₀.integers)
    (hg : g ∈ R₀.integers) : R₀.residue ⟨f, hf⟩ = R₀.residue ⟨g, hg⟩ := by
  subst e
  rfl

private theorem coeffEmb_jq' : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) :=
  map_jqModC (K := ℚ) (algebraMap ℚ (AlgebraicClosure ℚ))

private theorem coe_jFun' :
    ((jFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) :=
  coeffEmb_jq'

private theorem coe_jQFun' :
    ((jQFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ)) := by
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = _
  rw [← coeffEmb_jq']
  exact ModularCurve.coeffSemilinearAut.coeffMap_qExpand (algebraMap ℚ (AlgebraicClosure ℚ)) q jq

private theorem atkinLehnerBar_jFun_eq_jQFun_of_not_dvd (hqN : ¬ q ∣ N) :
    atkinLehnerBar N q (jFun N q) = jQFun N q := by
  have h : ∃ σ : modularFunctionFieldFull (N * q) ≃ₐ[ℚ] modularFunctionFieldFull (N * q),
      IsAtkinLehnerAutFull N q σ :=
    exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN
  have hw := (isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q h) 1 inferInstance (one_dvd N)
  have e1 : (⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (one_dvd _)⟩ : modularFunctionFieldFull (N * q))
      = ⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ :=
    Subtype.ext (qExpand_one_apply _)
  have e2 : (⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (mul_dvd_mul_right (one_dvd N) q)⟩ :
        modularFunctionFieldFull (N * q))
      = ⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩ :=
    Subtype.ext (by
      show qExpand ℚ (1 * q) jq = qExpand ℚ q jq
      simp only [one_mul])
  have hσ₁ : atkinLehnerInvolutionFull N q ⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩
      = ⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩ := by
    rw [← e1, hw.1, e2]
  apply Subtype.ext
  show ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
      ⟨coeffEmb (AlgebraicClosure ℚ)
          ((⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ :
            modularFunctionFieldFull (N * q)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ :
            modularFunctionFieldFull (N * q)).2⟩ : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ))
    = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq)
  rw [coe_geomAut_coeffEmb, hσ₁]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem residue₁_jFun_eq (R : ProlongationTuple P) (h₁ : jFun N q ∈ R.R₁.integers) :
    R.R₁.residue ⟨jFun N q, h₁⟩
      = (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ :
          modularFunctionFieldFullC (ResidueField A) N) := by
  have hval : coeffMap A.subtype (jqModC A) = (jFun N q : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coe_jFun']
    exact map_jqModC A.subtype
  have hy : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar (N * q) := by
    rw [hval]
    exact (jFun N q).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (jqModC A) hy
  have e : (⟨coeffMap A.subtype (jqModC A), hy⟩ : modularFunctionFieldBar (N * q)) = jFun N q :=
    Subtype.ext hval
  rw [← residue_mk_congr' R.R₁ e h h₁]
  apply Subtype.ext
  rw [hres]
  exact map_jqModC (IsLocalRing.residue A)

omit [IsAlgClosed k] [DecidableEq k] in
private theorem jQFun_mem_integersFst (R : ProlongationTuple P) : jQFun N q ∈ R.R₁.integers := by
  have hval : coeffMap A.subtype (qExpand A q (jqModC A))
      = (jQFun N q : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coe_jQFun', ModularCurve.coeffSemilinearAut.coeffMap_qExpand]
    congr 1
    exact map_jqModC A.subtype
  have hy : coeffMap A.subtype (qExpand A q (jqModC A)) ∈ modularFunctionFieldBar (N * q) := by
    rw [hval]
    exact (jQFun N q).2
  obtain ⟨h, -⟩ := R.residue₁_coeffMap (qExpand A q (jqModC A)) hy
  have e : (⟨coeffMap A.subtype (qExpand A q (jqModC A)), hy⟩ : modularFunctionFieldBar (N * q))
      = jQFun N q :=
    Subtype.ext hval
  rw [← e]
  exact h

omit [IsAlgClosed k] [DecidableEq k] in
private theorem residue₁_jQFun_eq (R : ProlongationTuple P) (h : jQFun N q ∈ R.R₁.integers) :
    R.R₁.residue ⟨jQFun N q, h⟩
      = (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ :
          modularFunctionFieldFullC (ResidueField A) N) ^ q := by
  haveI : CharP (ResidueField A) q := R.redBar.charP R.redBar.injective q
  have hval : coeffMap A.subtype (qExpand A q (jqModC A))
      = (jQFun N q : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coe_jQFun', ModularCurve.coeffSemilinearAut.coeffMap_qExpand]
    congr 1
    exact map_jqModC A.subtype
  have hy : coeffMap A.subtype (qExpand A q (jqModC A)) ∈ modularFunctionFieldBar (N * q) := by
    rw [hval]
    exact (jQFun N q).2
  obtain ⟨h', hres⟩ := R.residue₁_coeffMap (qExpand A q (jqModC A)) hy
  have e : (⟨coeffMap A.subtype (qExpand A q (jqModC A)), hy⟩ : modularFunctionFieldBar (N * q))
      = jQFun N q :=
    Subtype.ext hval
  rw [← residue_mk_congr' R.R₁ e h' h]
  apply Subtype.ext
  rw [hres, ModularCurve.coeffSemilinearAut.coeffMap_qExpand, IntermediateField.coe_pow]
  have hm : coeffMap (IsLocalRing.residue A) (jqModC A) = jqModC (ResidueField A) :=
    map_jqModC (IsLocalRing.residue A)
  rw [hm]
  show qExpand (ResidueField A) q (jqModC (ResidueField A)) = jqModC (ResidueField A) ^ q
  rw [jqModC_eq_map_intCast (ResidueField A)]
  exact (map_intCast_pow_char_eq_qExpand q (jqModC ℤ)).symm

omit [IsAlgClosed k] [DecidableEq k] in
private theorem residue₂_jFun_eq (R : ProlongationTuple P) (hqN : ¬ q ∣ N) (h₂ : jFun N q ∈ R.R₂.integers) :
    R.R₂.residue ⟨jFun N q, h₂⟩
      = (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ :
          modularFunctionFieldFullC (ResidueField A) N) ^ q := by
  rw [R.residue₂_eq,
    residue_mk_congr' R.R₁ (atkinLehnerBar_jFun_eq_jQFun_of_not_dvd hqN) _ (jQFun_mem_integersFst R),
    residue₁_jQFun_eq]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_residue_jFun_transcendental (R : ProlongationTuple P) (hqN : ¬ q ∣ N) :
    (∀ h₁ : jFun N q ∈ R.R₁.integers, Transcendental (ResidueField A) (R.R₁.residue ⟨jFun N q, h₁⟩)) ∧
    (∀ h₂ : jFun N q ∈ R.R₂.integers, Transcendental (ResidueField A) (R.R₂.residue ⟨jFun N q, h₂⟩)) := by
  refine ⟨fun h₁ => ?_, fun h₂ => ?_⟩
  · rw [residue₁_jFun_eq R h₁]
    exact AuxNS.transcendental_jqModC_full (ResidueField A) N
  · rw [residue₂_jFun_eq R hqN h₂]
    exact (AuxNS.transcendental_jqModC_full (ResidueField A) N).pow (Fact.out : q.Prime).pos

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_finiteDimensional_adjoin_jFun :
    FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jFun N q} : Set (modularFunctionFieldBar (N * q)))) (modularFunctionFieldBar (N * q)) := by
  have hj : jFun N q = jBar (N * q) := rfl
  rw [hj]
  refine Module.finite_of_finrank_pos ?_
  rw [CompEq.finrank_adjoin_jBar_eq_dedekindPsi (N * q)]
  exact AuxNS.dedekindPsi_pos (N * q)

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_defect_identity (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (h₁ : jFun N q ∈ R.R₁.integers) (h₂ : jFun N q ∈ R.R₂.integers) :
    Module.finrank ↥(IntermediateField.adjoin (ResidueField A)
        ({R.R₁.residue ⟨jFun N q, h₁⟩} : Set (modularFunctionFieldFullC (ResidueField A) N)))
        (modularFunctionFieldFullC (ResidueField A) N) +
      Module.finrank ↥(IntermediateField.adjoin (ResidueField A)
        ({R.R₂.residue ⟨jFun N q, h₂⟩} : Set (modularFunctionFieldFullC (ResidueField A) N)))
        (modularFunctionFieldFullC (ResidueField A) N) =
      Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jFun N q} : Set (modularFunctionFieldBar (N * q)))) (modularFunctionFieldBar (N * q)) := by
  have hq : q.Prime := Fact.out
  haveI : CharP (ResidueField A) q := R.redBar.charP R.redBar.injective q
  have hN : (N : ResidueField A) ≠ 0 := fun h0 =>
    hqN ((CharP.cast_eq_zero_iff (ResidueField A) q N).mp h0)
  have hj : jFun N q = jBar (N * q) := rfl
  have hcop : Nat.Coprime N q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm
  rw [residue₁_jFun_eq R h₁, residue₂_jFun_eq R hqN h₂,
    AuxNS.finrank_adjoin_pow_char q hq (AuxNS.transcendental_jqModC_full (ResidueField A) N),
    finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi (ResidueField A) N hN, hj,
    CompEq.finrank_adjoin_jBar_eq_dedekindPsi (N * q), dedekindPsi_mul_of_coprime N q hcop,
    dedekindPsi_prime hq]
  ring

private theorem atkinLehnerBar_jQFun_eq_jFun_of_not_dvd (hqN : ¬ q ∣ N) :
    atkinLehnerBar N q (jQFun N q) = jFun N q := by
  have h : ∃ σ : modularFunctionFieldFull (N * q) ≃ₐ[ℚ] modularFunctionFieldFull (N * q),
      IsAtkinLehnerAutFull N q σ :=
    exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN
  have hw := (isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q h) 1 inferInstance (one_dvd N)
  have e1 : (⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (one_dvd _)⟩ : modularFunctionFieldFull (N * q))
      = ⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ :=
    Subtype.ext (qExpand_one_apply _)
  have e2 : (⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (mul_dvd_mul_right (one_dvd N) q)⟩ :
        modularFunctionFieldFull (N * q))
      = ⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩ :=
    Subtype.ext (by
      show qExpand ℚ (1 * q) jq = qExpand ℚ q jq
      simp only [one_mul])
  have hσ₂ : atkinLehnerInvolutionFull N q ⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩
      = ⟨jq, modularFunctionField_le_full (N * q) (jq_mem (N * q))⟩ := by
    rw [← e2, hw.2, e1]
  apply Subtype.ext
  show ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
      ⟨coeffEmb (AlgebraicClosure ℚ)
          ((⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩ :
            modularFunctionFieldFull (N * q)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (⟨qExpand ℚ q jq, jqd_mem_full (N * q) (dvd_mul_left q N)⟩ :
            modularFunctionFieldFull (N * q)).2⟩ : modularFunctionFieldBar (N * q)) :
        LaurentSeries (AlgebraicClosure ℚ))
    = coeffEmb (AlgebraicClosure ℚ) jq
  rw [coe_geomAut_coeffEmb, hσ₂]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem jFun_mem_integersFst (R : ProlongationTuple P) : jFun N q ∈ R.R₁.integers := by
  have hval : coeffMap A.subtype (jqModC A) = (jFun N q : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coe_jFun']
    exact map_jqModC A.subtype
  have hy : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar (N * q) := by
    rw [hval]
    exact (jFun N q).2
  obtain ⟨h, -⟩ := R.residue₁_coeffMap (jqModC A) hy
  have e : (⟨coeffMap A.subtype (jqModC A), hy⟩ : modularFunctionFieldBar (N * q)) = jFun N q :=
    Subtype.ext hval
  rw [← e]
  exact h

omit [IsAlgClosed k] [DecidableEq k] in
private theorem frobWitness_mem_integersFst (R : ProlongationTuple P) :
    (jQFun N q - jFun N q ^ q) / (q : modularFunctionFieldBar (N * q)) ∈ R.R₁.integers := by
  have hq : q.Prime := Fact.out
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  haveI : CharZero (LaurentSeries (AlgebraicClosure ℚ)) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective
  have hq0 : (q : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hcoe : ((((jQFun N q - jFun N q ^ q) / (q : modularFunctionFieldBar (N * q))) :
        modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = (((jQFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
          - ((jFun N q : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ^ q)
        / (q : LaurentSeries (AlgebraicClosure ℚ)) := by
    simp
  have hval : coeffMap A.subtype (coeffMap (Int.castRingHom A) (AuxNS.frobQuotZ q))
      = ((((jQFun N q - jFun N q ^ q) / (q : modularFunctionFieldBar (N * q))) :
          modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hcoe, coe_jQFun', coe_jFun', coeffMap_coeffMap,
      coeffMap_congr (Subsingleton.elim (A.subtype.comp (Int.castRingHom A))
        (Int.castRingHom (AlgebraicClosure ℚ))),
      eq_div_iff hq0, mul_comm, AuxNS.natCast_mul_coeffMap_frobQuotZ q]
  have hy : coeffMap A.subtype (coeffMap (Int.castRingHom A) (AuxNS.frobQuotZ q))
      ∈ modularFunctionFieldBar (N * q) := by
    rw [hval]
    exact ((jQFun N q - jFun N q ^ q) / (q : modularFunctionFieldBar (N * q))).2
  obtain ⟨h, -⟩ := R.residue₁_coeffMap _ hy
  have e : (⟨_, hy⟩ : modularFunctionFieldBar (N * q))
      = (jQFun N q - jFun N q ^ q) / (q : modularFunctionFieldBar (N * q)) :=
    Subtype.ext hval
  rw [← e]
  exact h

omit [IsAlgClosed k] [DecidableEq k] in
private theorem frobWitness_swap_not_mem_integersFst (R : ProlongationTuple P) :
    (jFun N q - jQFun N q ^ q) / (q : modularFunctionFieldBar (N * q)) ∉ R.R₁.integers := by
  intro hg
  have hq : q.Prime := Fact.out
  haveI : CharP (ResidueField A) q := R.redBar.charP R.redBar.injective q
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective
  haveI : CharZero (modularFunctionFieldBar (N * q)) :=
    charZero_of_injective_algebraMap
      (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).injective
  have hq0 : (q : modularFunctionFieldBar (N * q)) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero

  have hqmem : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((q : A) : AlgebraicClosure ℚ)
      ∈ R.R₁.integers :=
    (R.R₁.algebraMap_mem_iff _).mpr (q : A).2
  have hres_q : R.R₁.residue ⟨_, hqmem⟩ = 0 := by
    rw [R.R₁.residue_algebraMap (q : A), map_natCast, CharP.cast_eq_zero (ResidueField A) q, map_zero]
  have hc : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((q : A) : AlgebraicClosure ℚ)
      = (q : modularFunctionFieldBar (N * q)) := by
    simp

  have hJ : jFun N q ∈ R.R₁.integers := jFun_mem_integersFst R
  have hQ : jQFun N q ∈ R.R₁.integers := jQFun_mem_integersFst R
  have hdiff : jFun N q - jQFun N q ^ q ∈ R.R₁.integers := sub_mem hJ (pow_mem hQ q)
  obtain ⟨jx, hjx⟩ : ∃ jx : modularFunctionFieldFullC (ResidueField A) N,
      jx = ⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) N⟩ := ⟨_, rfl⟩
  have h1 : R.R₁.residue ⟨_, hdiff⟩ = jx - (jx ^ q) ^ q := by
    have e : (⟨_, hdiff⟩ : R.R₁.integers) = ⟨jFun N q, hJ⟩ - ⟨jQFun N q, hQ⟩ ^ q := Subtype.ext (by simp)
    rw [e, map_sub, map_pow, residue₁_jFun_eq R hJ, residue₁_jQFun_eq R hQ, hjx]
  have h2 : R.R₁.residue ⟨_, hdiff⟩ = 0 := by
    have key : (jFun N q - jQFun N q ^ q) / (q : modularFunctionFieldBar (N * q))
        * algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) ((q : A) : AlgebraicClosure ℚ)
        = jFun N q - jQFun N q ^ q := by
      rw [hc]
      exact (eq_div_iff hq0).mp rfl
    have e : (⟨_, hdiff⟩ : R.R₁.integers) = ⟨_, hg⟩ * ⟨_, hqmem⟩ :=
      Subtype.ext (by rw [MulMemClass.coe_mul]; exact key.symm)
    rw [e, map_mul, hres_q, mul_zero]
  have h3 : jx ^ (q * q) = jx := by
    rw [pow_mul]
    exact (sub_eq_zero.mp (h1.symm.trans h2)).symm

  have hroot : Polynomial.aeval jx (Polynomial.X ^ (q * q) - Polynomial.X : Polynomial (ResidueField A)) = 0 := by
    simp [h3]
  have hp : (Polynomial.X ^ (q * q) - Polynomial.X : Polynomial (ResidueField A)) ≠ 0 := by
    intro h0
    have hc1 := congrArg (fun p : Polynomial (ResidueField A) => p.coeff 1) h0
    have h4 : 2 * 2 ≤ q * q := Nat.mul_le_mul hq.two_le hq.two_le
    have hne : (1 : ℕ) ≠ q * q := fun h => by
      rw [← h] at h4
      exact absurd h4 (by decide)
    simp [Polynomial.coeff_X_pow, hne] at hc1
  subst hjx
  exact (AuxNS.transcendental_jqModC_full (ResidueField A) N) ⟨_, hp, hroot⟩

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_integers_ne (R : ProlongationTuple P) (hqN : ¬ q ∣ N) : R.R₁.integers ≠ R.R₂.integers := by
  intro heq
  have h1 := frobWitness_mem_integersFst R
  rw [heq] at h1
  have h2 : atkinLehnerBar N q ((jQFun N q - jFun N q ^ q) / (q : modularFunctionFieldBar (N * q)))
      ∈ R.R₁.integers :=
    (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff _).mp h1)
  rw [map_div₀, map_sub, map_pow, map_natCast, atkinLehnerBar_jQFun_eq_jFun_of_not_dvd hqN,
    atkinLehnerBar_jFun_eq_jQFun_of_not_dvd hqN] at h2
  exact frobWitness_swap_not_mem_integersFst R h2

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_transfer (R : ProlongationTuple P) {I : Type*}
    (x y : I → modularFunctionFieldFullC (ResidueField A) N)
    (h : LinearIndependent (ResidueField A) (fun i => (x i, y i))) :
    LinearIndependent k (fun i => (R.ι (x i), R.ι (y i))) := by
  classical
  rw [linearIndependent_iff'] at h ⊢
  intro s c hrel i hi
  letI : Algebra (ResidueField A) k := R.redBar.toAlgebra
  let Bk := Module.Basis.ofVectorSpace (ResidueField A) k

  have key : ∀ z : I → modularFunctionFieldFullC (ResidueField A) N,
      ∑ j ∈ s, c j • R.ι (z j) = 0 → ∀ (b : Module.Basis.ofVectorSpaceIndex (ResidueField A) k) (m : ℤ),
        ∑ j ∈ s, Bk.repr (c j) b * ((z j : modularFunctionFieldFullC (ResidueField A) N) :
          LaurentSeries (ResidueField A)).coeff m = 0 := by
    intro z hz b m
    have h1 : ∑ j ∈ s, c j * R.redBar (((z j : modularFunctionFieldFullC (ResidueField A) N) :
        LaurentSeries (ResidueField A)).coeff m) = 0 := by
      have := congrArg (fun f : modularFunctionFieldC k N => (f : LaurentSeries k).coeff m) hz
      simp only [AddSubmonoidClass.coe_finsetSum, IntermediateField.coe_smul, R.ι_coe, HahnSeries.coeff_sum,
        ZeroMemClass.coe_zero, HahnSeries.coeff_zero] at this
      simpa only [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
        coeffMap_coeff] using this
    have h2 : ∑ j ∈ s, (((z j : modularFunctionFieldFullC (ResidueField A) N) :
        LaurentSeries (ResidueField A)).coeff m) • c j = 0 := by
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
      rfl
    have h3 := congrArg (fun t : k => Bk.repr t b) h2
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero,
      Finsupp.zero_apply] at h3
    rw [← h3]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hx0 : ∑ j ∈ s, c j • R.ι (x j) = 0 := by
    have := congrArg Prod.fst hrel
    simpa only [Prod.fst_sum, Prod.smul_fst, Prod.fst_zero] using this
  have hy0 : ∑ j ∈ s, c j • R.ι (y j) = 0 := by
    have := congrArg Prod.snd hrel
    simpa only [Prod.snd_sum, Prod.smul_snd, Prod.snd_zero] using this

  have hb : ∀ b : Module.Basis.ofVectorSpaceIndex (ResidueField A) k, ∀ j ∈ s, Bk.repr (c j) b = 0 := by
    intro b
    refine h s (fun j => Bk.repr (c j) b) (Prod.ext ?_ ?_)
    · rw [Prod.fst_sum, Prod.fst_zero]
      simp only [Prod.smul_fst]
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
      ext m
      simp only [IntermediateField.coe_smul, HahnSeries.coeff_sum, HahnSeries.coeff_zero]
      simp only [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
      exact key x hx0 b m
    · rw [Prod.snd_sum, Prod.snd_zero]
      simp only [Prod.smul_snd]
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
      ext m
      simp only [IntermediateField.coe_smul, HahnSeries.coeff_sum, HahnSeries.coeff_zero]
      simp only [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
      exact key y hy0 b m
  have hci : Bk.repr (c i) = 0 := Finsupp.ext fun b => hb b i hi
  exact (LinearEquiv.map_eq_zero_iff Bk.repr).mp hci

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_lattice (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    ∃ (u : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → modularFunctionFieldBar (N * q))
      (h₁ : ∀ a, u a ∈ R.R₁.integers) (h₂ : ∀ a, u a ∈ R.R₂.integers),
      (∀ a, u a ∈ riemannRochSpace E) ∧
      LinearIndependent k (fun a => (R.residue₁ ⟨u a, h₁ a⟩, R.residue₂ ⟨u a, h₂ a⟩)) := by
  classical
  haveI := aux_finiteDimensional_riemannRochSpace (N := N) (q := q) E
  obtain ⟨hj₁, hj₂, -, -⟩ := aux_jFun_commonUnit R
  let RR : Fin 2 → RegularProlongation A (modularFunctionFieldBar (N * q))
      (modularFunctionFieldFullC (ResidueField A) N) := ![R.R₁, R.R₂]
  have hne := aux_integers_ne R hqN
  have hinj : Function.Injective fun i => (RR i).integers := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd h hne
    · exact absurd h.symm hne
    · rfl
  have hf : ∀ i, jFun N q ∈ (RR i).integers := by
    intro i
    fin_cases i
    · exact hj₁
    · exact hj₂
  have htr : ∀ i, Transcendental (ResidueField A) ((RR i).residue ⟨jFun N q, hf i⟩) := by
    intro i
    fin_cases i
    · exact (aux_residue_jFun_transcendental R hqN).1 hj₁
    · exact (aux_residue_jFun_transcendental R hqN).2 hj₂
  haveI := aux_finiteDimensional_adjoin_jFun (N := N) (q := q)
  have heq : ∑ i, Module.finrank ↥(IntermediateField.adjoin (ResidueField A)
      ({(RR i).residue ⟨jFun N q, hf i⟩} : Set (modularFunctionFieldFullC (ResidueField A) N)))
      (modularFunctionFieldFullC (ResidueField A) N) =
      Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jFun N q} : Set (modularFunctionFieldBar (N * q)))) (modularFunctionFieldBar (N * q)) := by
    rw [Fin.sum_univ_two]
    exact aux_defect_identity R hqN hj₁ hj₂
  obtain ⟨w, hwO, hwV, hli, -⟩ :=
    AlgebraicCurve.RegularProlongation.exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq
      A (fun _ : Fin 2 => ↥(modularFunctionFieldFullC (ResidueField A) N)) RR hinj (jFun N q) hf htr heq
      (riemannRochSpace E)
  have hli2 : LinearIndependent (ResidueField A)
      (fun a => ((RR 0).residue ⟨w a, hwO a 0⟩, (RR 1).residue ⟨w a, hwO a 1⟩)) := by
    have h := hli.map'
      (LinearEquiv.finTwoArrow (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) N)).toLinearMap
      (LinearEquiv.ker _)
    have hcomp : (⇑(LinearEquiv.finTwoArrow (ResidueField A)
          ↥(modularFunctionFieldFullC (ResidueField A) N)).toLinearMap ∘
          fun a i => (RR i).residue ⟨w a, hwO a i⟩)
        = fun a => ((RR 0).residue ⟨w a, hwO a 0⟩, (RR 1).residue ⟨w a, hwO a 1⟩) := by
      funext a
      simp only [Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.finTwoArrow_apply]
    rw [hcomp] at h
    exact h
  have hk := aux_transfer R (fun a => (RR 0).residue ⟨w a, hwO a 0⟩) (fun a => (RR 1).residue ⟨w a, hwO a 1⟩)
    hli2
  refine ⟨w, fun a => hwO a 0, fun a => hwO a 1, hwV, ?_⟩
  have e : (fun a => (R.residue₁ ⟨w a, hwO a 0⟩, R.residue₂ ⟨w a, hwO a 1⟩))
      = fun a => (R.ι ((RR 0).residue ⟨w a, hwO a 0⟩), R.ι ((RR 1).residue ⟨w a, hwO a 1⟩)) := rfl
  rw [e]
  exact hk

private theorem aux_nodeValue (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed) (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    {nd : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)}
    (hnd : nd ∈ nodePairsOfPlaces (arithFrobC q k N) W)
    (hreg : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst V = nd.1 → 0 ≤ V.ord f) :
    ∃ c : k, nd.1.HasValue (R.residue₁ ⟨f, h₁⟩) c ∧ nd.2.HasValue (R.residue₂ ⟨f, h₂⟩) c :=
  hRL.2 f h₁ h₂ nd hnd hreg

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_not_fixed_reduceFst_of_isStrictSnd
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hs : P.IsStrictSnd V) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V))
      ≠ P.reduceFst V := by
  intro hfix
  apply hs.2
  apply frobOnPlacesGeomLevel_injective k N data hKr
  rw [← hs.1]
  exact hfix

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_not_fixed_reduceSnd_of_isStrictFst
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hs : P.IsStrictFst V) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceSnd V))
      ≠ P.reduceSnd V := by
  intro hfix
  apply hs.2
  apply frobOnPlacesGeomLevel_injective k N data hKr
  rw [hs.1]
  exact hfix

private theorem aux_not_isStrictFst_of_sndKind (hqN : ¬ q ∣ N)
    {V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hV₀ : IsZeroSide P V₀ ∨ P.IsStrictSnd V₀) : ¬ P.IsStrictFst V₀ := by
  intro hs
  rcases hV₀ with hz | hss
  · apply hs.2
    rw [hs.1]
    exact (reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide P hqN V₀ hz).symm
  · apply hs.2
    rw [hs.1]
    exact hss.1.symm

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_not_isAffineGeomPlace_of_ord_lt_zero (v : Place k (modularFunctionFieldC k N))
    (hv : v.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0) :
    ¬ IsAffineGeomPlace k N v :=
  fun haff => absurd hv (not_lt.mpr (v.ord_nonneg_of_mem haff.1))

private theorem aux_reduceFst_ne_of_sndKind (hqN : ¬ q ∣ N)
    {V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hV₀ : IsZeroSide P V₀ ∨ P.IsStrictSnd V₀) (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (haff : IsAffineGeomPlace k N v) : P.reduceFst V₀ ≠ v := by
  intro h
  rcases hV₀ with hz | hss
  · have hpole : (P.reduceFst V₀).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 := by
      rw [reduceFst_eq_frobOnPlacesGeomLevel_reduceSnd_of_isZeroSide P hqN V₀ hz, ord_frob_jGeom_eq]
      exact reduceSnd_ord_lt_zero_of_isCuspidal' V₀ hz.1
    refine aux_not_isAffineGeomPlace_of_ord_lt_zero _ hpole ?_
    rw [h]
    exact haff
  · apply aux_not_fixed_reduceFst_of_isStrictSnd hss
    rw [h]
    exact hv

private theorem aux_apply_eq_zero_of_isGoodDiv
    {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hE : P.IsGoodDiv E)
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.reduceFst V))
      = P.reduceFst V) : E V = 0 := by
  by_contra hne
  rcases hE V (Finsupp.mem_support_iff.mpr hne) with hs | hs
  · exact hs.2 hfix
  · exact aux_not_fixed_reduceFst_of_isStrictSnd hs hfix

private theorem aux_mapDomain_reduceFst_eq_zero
    {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hE : P.IsGoodDiv E)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hD : D.support ⊆ E.support)
    (v : Place k (modularFunctionFieldC k N))
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) :
    Finsupp.mapDomain P.reduceFst D v = 0 := by
  classical
  by_contra hne
  obtain ⟨V, hV, hVv⟩ := Finset.mem_image.mp (mem_image_of_mapDomain_ne_zero hD P.reduceFst hne)
  rcases hE V hV with hs | hs
  · exact hs.2 (by rw [hVv]; exact hv)
  · exact aux_not_fixed_reduceFst_of_isStrictSnd hs (by rw [hVv]; exact hv)

private theorem aux_mapDomain_reduceSnd_eq_zero
    {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hE : P.IsGoodDiv E)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hD : D.support ⊆ E.support)
    (w : Place k (modularFunctionFieldC k N))
    (hw : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w) :
    Finsupp.mapDomain P.reduceSnd D w = 0 := by
  classical
  by_contra hne
  obtain ⟨V, hV, hVw⟩ := Finset.mem_image.mp (mem_image_of_mapDomain_ne_zero hD P.reduceSnd hne)
  rcases hE V hV with hs | hs
  · exact aux_not_fixed_reduceSnd_of_isStrictFst hs (by rw [hVw]; exact hw)
  · exact hs.2 (by rw [hVw]; exact hw)

private theorem aux_mapDomain_filter_add_single_le {X Y : Type*} (r : X → Y) (E : X →₀ ℤ) (p : X → Prop)
    {d : DecidablePred p} (V₀ : X) (y : Y) :
    Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d (E + Finsupp.single V₀ 1)) y
      ≤ Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d E) y + Finsupp.single (r V₀) (1 : ℤ) y := by
  classical
  rw [Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.add_apply]
  refine add_le_add le_rfl ?_
  by_cases hp : p V₀
  · rw [Finsupp.filter_single_of_pos p hp, Finsupp.mapDomain_single]
  · rw [Finsupp.filter_single_of_neg p hp, Finsupp.mapDomain_zero, Finsupp.zero_apply, Finsupp.single_apply]
    split_ifs <;> omega

private theorem aux_mapDomain_filter_add_single_of_not {X Y : Type*} (r : X → Y) (E : X →₀ ℤ) (p : X → Prop)
    {d : DecidablePred p} {V₀ : X} (hp : ¬ p V₀) (y : Y) :
    Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d (E + Finsupp.single V₀ 1)) y
      = Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d E) y := by
  rw [Finsupp.filter_add, Finsupp.filter_single_of_neg p hp, add_zero]

private theorem aux_mapDomain_add_single_apply {X Y : Type*} (r : X → Y) (E : X →₀ ℤ) (V₀ : X) (y : Y) :
    Finsupp.mapDomain r (E + Finsupp.single V₀ 1) y
      = Finsupp.mapDomain r E y + Finsupp.single (r V₀) (1 : ℤ) y := by
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.add_apply]

private theorem aux_add_single_nonneg {X : Type*} (E : X →₀ ℤ) (hE : ∀ V, 0 ≤ E V) (V₀ : X) (V : X) :
    0 ≤ (E + Finsupp.single V₀ 1 : X →₀ ℤ) V := by
  classical
  rw [Finsupp.add_apply, Finsupp.single_apply]
  have := hE V
  split_ifs <;> omega

private theorem aux_add_single_apply_eq_zero {X : Type*} (E : X →₀ ℤ) {V₀ V : X} (hEV : E V = 0) (hne : V₀ ≠ V) :
    (E + Finsupp.single V₀ 1 : X →₀ ℤ) V = 0 := by
  classical
  rw [Finsupp.add_apply, hEV, Finsupp.single_apply, if_neg hne, zero_add]

private theorem aux_mapDomain_add_single_eq_zero
    {E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hE : P.IsGoodDiv E)
    {V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} {v : Place k (modularFunctionFieldC k N)}
    (hne : P.reduceFst V₀ ≠ v)
    (hv : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v) :
    Finsupp.mapDomain P.reduceFst (E + Finsupp.single V₀ 1) v = 0 := by
  classical
  rw [aux_mapDomain_add_single_apply, aux_mapDomain_reduceFst_eq_zero hE (subset_refl _) v hv,
    Finsupp.single_apply, if_neg hne, add_zero]

private theorem aux_fixed_and_affine_of_mem (hqN : ¬ q ∣ N)
    {W : Finset (Place k (modularFunctionFieldC k N))} (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) :
    frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w ∧
      IsAffineGeomPlace k N w := by
  have hss : w ∈ ssPlaces q N k := (hW w).mp hw
  refine ⟨?_, ?_⟩
  · have h := arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd q N hqN k w hss
    rwa [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr,
      arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr] at h
  · have h := hss
    rw [mem_ssPlaces_iff, isSupersingularPlace_iff] at h
    exact h.2.1

private theorem aux_ord_nonneg_of_mem {E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    {f : modularFunctionFieldBar (N * q)} (hf : f ∈ riemannRochSpace E')
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hV : E' V = 0) : 0 ≤ V.ord f := by
  rcases (mem_riemannRochSpace_iff.mp hf) V with h0 | h
  · rw [h0, Place.ord_zero]
  · rw [hV, neg_zero] at h
    exact h

omit [IsAlgClosed k] [DecidableEq k] in
open Classical in
private theorem aux_fst_bound (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed) (hqN : ¬ q ∣ N)
    {E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hE' : ∀ V, 0 ≤ E' V)
    {f : modularFunctionFieldBar (N * q)} (hf : f ∈ riemannRochSpace E')
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (D₁ : Divisor k (modularFunctionFieldC k N)) (hD₁ : ∀ w, 0 ≤ D₁ w)
    (hstrict : ∀ w, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w →
      Finsupp.mapDomain P.reduceFst (P.fstDiv E') w ≤ D₁ w)
    (hcusp : ∀ w, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w →
      ¬ IsAffineGeomPlace k N w →
      Finsupp.mapDomain P.reduceFst (E'.filter (fun V => ¬ IsZeroSide P V)) w ≤ D₁ w)
    (haffmass : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v → Finsupp.mapDomain P.reduceFst E' v = 0)
    (w : Place k (modularFunctionFieldC k N)) :
    R.residue₁ ⟨f, h₁⟩ = 0 ∨ -D₁ w ≤ w.ord (R.residue₁ ⟨f, h₁⟩) := by
  classical
  by_cases hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w
  · by_cases haff : IsAffineGeomPlace k N w
    · haveI := aux_finiteDimensional_riemannRochSpace E'
      obtain ⟨s, hs₁, hs₂, hs⟩ := exists_orderBox_of_orderLawFixed R hO E' hE' w hfix haff
      rw [haffmass w hfix haff] at hs₁
      rcases (hs f hf h₁ h₂).1 with h0 | hb
      · exact Or.inl h0
      · right
        have := hD₁ w
        omega
    · rcases aux_image_fst_cusp R hR.2.2.1 hqN hE' hf h₁ h₂ w hfix haff with h0 | hb
      · exact Or.inl h0
      · right
        have := hcusp w hfix haff
        omega
  · rcases aux_image_fst_of_not_fixed R hR.1 hE' hf h₁ h₂ w hfix with h0 | hb
    · exact Or.inl h0
    · right
      have := hstrict w hfix
      omega

omit [DecidableEq k] in
open Classical in
private theorem aux_snd_bound (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed) (hqN : ¬ q ∣ N)
    {E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (hE' : ∀ V, 0 ≤ E' V)
    {f : modularFunctionFieldBar (N * q)} (hf : f ∈ riemannRochSpace E')
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (D₂ : Divisor k (modularFunctionFieldC k N)) (hD₂ : ∀ w, 0 ≤ D₂ w)
    (hstrict : ∀ w, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) ≠ w →
      Finsupp.mapDomain P.reduceSnd (P.sndDiv E') w ≤ D₂ w)
    (hcusp : ∀ w, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w →
      ¬ IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr w) →
      Finsupp.mapDomain P.reduceSnd (E'.filter (IsZeroSide P)) w ≤ D₂ w)
    (haffmass : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v → Finsupp.mapDomain P.reduceFst E' v = 0)
    (w : Place k (modularFunctionFieldC k N)) :
    R.residue₂ ⟨f, h₂⟩ = 0 ∨ -D₂ w ≤ w.ord (R.residue₂ ⟨f, h₂⟩) := by
  classical
  by_cases hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w
  · by_cases haff : IsAffineGeomPlace k N (frobOnPlacesGeomLevel k N data hKr w)
    ·
      have hvfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
          (frobOnPlacesGeomLevel k N data hKr w)) = frobOnPlacesGeomLevel k N data hKr w := by
        rw [hfix]
      haveI := aux_finiteDimensional_riemannRochSpace E'
      obtain ⟨s, hs₁, hs₂, hs⟩ :=
        exists_orderBox_of_orderLawFixed R hO E' hE' (frobOnPlacesGeomLevel k N data hKr w) hvfix haff
      have hm := haffmass _ hvfix haff
      rw [hm] at hs₁
      rcases (hs f hf h₁ h₂).2 with h0 | hb
      · exact Or.inl h0
      · right
        rw [hm, hfix] at hb
        have := hD₂ w
        omega
    · rcases aux_image_snd_cusp R hR.2.2.2 hqN hE' hf h₁ h₂ w hfix haff with h0 | hb
      · exact Or.inl h0
      · right
        have := hcusp w hfix haff
        omega
  · rcases aux_image_snd_of_not_fixed R hR.2.1 hE' hf h₁ h₂ w hfix with h0 | hb
    · exact Or.inl h0
    · right
      have := hstrict w hfix
      omega

private theorem aux_node_clause (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed) (hqN : ¬ q ∣ N)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W) {E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hE'W : ∀ V, ∀ w ∈ W, P.reduceFst V = w → E' V = 0)
    {f : modularFunctionFieldBar (N * q)} (hf : f ∈ riemannRochSpace E')
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    {nd : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)}
    (hnd : nd ∈ nodePairsOfPlaces (arithFrobC q k N) W) :
    ∃ c : k, nd.1.HasValue (R.residue₁ ⟨f, h₁⟩) c ∧ nd.2.HasValue (R.residue₂ ⟨f, h₂⟩) c :=
  aux_nodeValue R hR hO hqN W hW hRL f h₁ h₂ hnd fun V hV =>
    aux_ord_nonneg_of_mem hf (hE'W V nd.1 (fst_mem_of_mem_nodePairsOfPlaces hnd) hV)

private theorem aux_pairCond_residue_add_snd (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hqN : ¬ q ∣ N) (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hRL : R.RegularityLaw W)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hE : IsGoodAux P E)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV₀ : IsZeroSide P V₀ ∨ P.IsStrictSnd V₀) (hEV₀ : ∀ V ∈ E.support, P.reduceSnd V ≠ P.reduceSnd V₀)
    (f : modularFunctionFieldBar (N * q)) (hf : f ∈ riemannRochSpace (E + Finsupp.single V₀ 1))
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers) :
    PairCond (fibreDivFst P E) (fibreDivSnd P E + Finsupp.single (P.reduceSnd V₀) 1) W
      (R.residue₁ ⟨f, h₁⟩, R.residue₂ ⟨f, h₂⟩) := by
  classical
  have hE' := aux_add_single_nonneg E hE.1 V₀
  have hne : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v → P.reduceFst V₀ ≠ v :=
    fun v hv haff => aux_reduceFst_ne_of_sndKind hqN hV₀ v hv haff
  have haffmass : ∀ v, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v → Finsupp.mapDomain P.reduceFst (E + Finsupp.single V₀ 1) v = 0 :=
    fun v hv haff => aux_mapDomain_add_single_eq_zero hE.2 (hne v hv haff) hv
  have hD₁ : ∀ u, 0 ≤ fibreDivFst P E u := fun u => by
    unfold fibreDivFst
    exact mapDomain_filter_nonneg _ _ _ hE.1 u
  have hD₂ : ∀ u, 0 ≤ fibreDivSnd P E u := fun u => by
    unfold fibreDivSnd
    exact mapDomain_filter_nonneg _ _ _ hE.1 u
  have hsingle : ∀ u, 0 ≤ Finsupp.single (P.reduceSnd V₀) (1 : ℤ) u := fun u => by
    rw [Finsupp.single_apply]
    split_ifs <;> omega
  unfold PairCond
  refine ⟨fun w => ?_, fun w => ?_, fun nd hnd => ?_⟩
  · refine aux_fst_bound R hR hO hqN hE' hf h₁ h₂ (fibreDivFst P E) hD₁ ?_ ?_ haffmass w
    · intro u _
      exact le_of_eq (aux_mapDomain_filter_add_single_of_not P.reduceFst E P.IsStrictFst
        (aux_not_isStrictFst_of_sndKind hqN hV₀) u)
    · intro u hu _
      have h0 := aux_mapDomain_reduceFst_eq_zero hE.2
        (support_filter_subset E (fun V => ¬ IsZeroSide P V)) u hu
      rcases hV₀ with hz | hss
      · refine le_trans (le_of_eq (aux_mapDomain_filter_add_single_of_not P.reduceFst E
          (fun V => ¬ IsZeroSide P V) (fun h => h hz) u)) ?_
        exact le_trans (le_of_eq h0) (hD₁ u)
      · have hneq : P.reduceFst V₀ ≠ u := fun h =>
          aux_not_fixed_reduceFst_of_isStrictSnd hss (by rw [h]; exact hu)
        have h1 : Finsupp.single (P.reduceFst V₀) (1 : ℤ) u = 0 := by
          rw [Finsupp.single_apply, if_neg hneq]
        refine le_trans (aux_mapDomain_filter_add_single_le P.reduceFst E (fun V => ¬ IsZeroSide P V) V₀ u) ?_
        refine le_trans (add_le_add (le_of_eq h0) (le_of_eq h1)) ?_
        rw [add_zero]
        exact hD₁ u
  · refine aux_snd_bound R hR hO hqN hE' hf h₁ h₂ _ ?_ ?_ ?_ haffmass w
    · intro u
      rw [Finsupp.add_apply]
      have := hD₂ u
      have := hsingle u
      omega
    · intro u _
      rw [Finsupp.add_apply]
      unfold fibreDivSnd
      exact aux_mapDomain_filter_add_single_le _ _ _ V₀ u
    · intro u hu _
      rw [Finsupp.add_apply]
      exact le_trans (aux_mapDomain_filter_add_single_le P.reduceSnd E (IsZeroSide P) V₀ u)
        (add_le_add (le_trans (le_of_eq (aux_mapDomain_reduceSnd_eq_zero hE.2
          (support_filter_subset E (IsZeroSide P)) u hu)) (hD₂ u)) le_rfl)
  · refine aux_node_clause R hR hO hqN W hW hRL (E' := E + Finsupp.single V₀ 1) ?_ hf h₁ h₂ hnd
    intro V w hw hVw
    obtain ⟨hfix, haff⟩ := aux_fixed_and_affine_of_mem hqN hW hw
    refine aux_add_single_apply_eq_zero E (aux_apply_eq_zero_of_isGoodDiv hE.2 ?_) ?_
    · rw [hVw]
      exact hfix
    · intro h
      apply hne w hfix haff
      rw [h]
      exact hVw

private noncomputable def nodeDiv (W : Finset (Place k (modularFunctionFieldC k N))) :
    Divisor k (modularFunctionFieldC k N) :=
  ∑ w ∈ W, Finsupp.single w 1

omit [IsAlgClosed k] [DecidableEq k] in
private theorem nodeDiv_apply_of_mem {W : Finset (Place k (modularFunctionFieldC k N))}
    {v : Place k (modularFunctionFieldC k N)} (hv : v ∈ W) : nodeDiv W v = 1 := by
  classical
  simp [nodeDiv, Finsupp.single_apply, hv]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem nodeDiv_apply_of_not_mem {W : Finset (Place k (modularFunctionFieldC k N))}
    {v : Place k (modularFunctionFieldC k N)} (hv : v ∉ W) : nodeDiv W v = 0 := by
  classical
  simp [nodeDiv, Finsupp.single_apply, hv]

omit [DecidableEq k] in
private theorem degree_nodeDiv (W : Finset (Place k (modularFunctionFieldC k N))) :
    Divisor.degree (nodeDiv W) = W.card := by
  unfold nodeDiv
  rw [map_sum]
  simp [Divisor.degree_single, deg_eq_one_downstairs]

omit [IsAlgClosed k] [DecidableEq k] in
private theorem not_isStrictSnd_of_isStrictFst
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (h : P.IsStrictFst V) :
    ¬ P.IsStrictSnd V := fun h' =>
  h.2 (by rw [h.1, ← h'.1])

omit [IsAlgClosed k] [DecidableEq k] in
private theorem not_isStrictFst_of_isStrictSnd
    {V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))} (h' : P.IsStrictSnd V) :
    ¬ P.IsStrictFst V := fun h =>
  h'.2 (by rw [← h'.1]; exact h.1)

omit [DecidableEq k] in
private theorem degree_fibreDivFst_add_degree_fibreDivSnd
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hE : P.IsGoodDiv E) :
    (fibreDivFst P E).degree + (fibreDivSnd P E).degree = E.degree := by
  rw [degree_eq_tmass deg_eq_one_downstairs, degree_eq_tmass deg_eq_one_downstairs,
    degree_eq_tmass (deg_eq_one_modularFunctionFieldBar (N * q))]
  unfold fibreDivFst fibreDivSnd
  rw [tmass_mapDomain, tmass_mapDomain, ← tmass_add]
  congr 1
  ext V
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.filter_apply]
  by_cases hV : E V = 0
  · simp [hV]
  · rcases hE V (Finsupp.mem_support_iff.mpr hV) with h | h
    · rw [if_pos h, if_neg (not_isStrictSnd_of_isStrictFst h), add_zero]
    · rw [if_neg (not_isStrictFst_of_isStrictSnd h), if_pos h, zero_add]

private theorem fibreDivFst_apply_eq_zero_of_mem {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) (hqN : ¬ q ∣ N)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) : fibreDivFst P E w = 0 := by
  unfold fibreDivFst
  refine mapDomain_filter_eq_zero P.reduceFst E P.IsStrictFst w ?_
  intro V hV hs
  apply hs.2
  have hfix := arithFrobC_smul_arithFrobC_smul_of_mem_ssPlaces_of_not_dvd q N hqN k w ((hW w).mp hw)
  rw [arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr,
    arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr] at hfix
  rw [hV]
  exact hfix

private theorem fst_mem_riemannRochSpace_sub_nodeDiv {W : Finset (Place k (modularFunctionFieldC k N))}
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) (hqN : ¬ q ∣ N)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {x : ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N)}
    (hx : PairCond (fibreDivFst P E) (fibreDivSnd P E) W x) (hx2 : x.2 = 0) :
    x.1 ∈ riemannRochSpace (fibreDivFst P E - nodeDiv W) := by
  rw [mem_riemannRochSpace_iff]
  intro v
  by_cases h0 : x.1 = 0
  · exact Or.inl h0
  right
  rw [Finsupp.sub_apply]
  by_cases hv : v ∈ W
  · rw [fibreDivFst_apply_eq_zero_of_mem hW hqN E hv, nodeDiv_apply_of_mem hv]
    have hval : v.HasValue x.1 0 := by
      obtain ⟨c, hc₁, hc₂⟩ := hx.2.2 _ (smulNodePair_mem_nodePairsOfPlaces (arithFrobC q k N) hv)
      rw [hx2] at hc₂
      have hc0 : c = 0 := Place.HasValue.unique hc₂ (AuxNS.hasValue_zero _)
      rw [hc0] at hc₁
      exact hc₁
    have hpos := AuxNS.ord_pos_of_hasValue_zero h0 hval
    omega
  · rw [nodeDiv_apply_of_not_mem hv, sub_zero]
    exact (hx.1 v).resolve_left h0

private def pairCondSpace (D₁ D₂ : Divisor k (modularFunctionFieldC k N))
    (W : Finset (Place k (modularFunctionFieldC k N))) :
    Submodule k (↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N)) where
  carrier := {x | PairCond D₁ D₂ W x}
  zero_mem' := by
    refine ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, fun nd _ => ⟨0, ?_, ?_⟩⟩
    · exact AuxNS.hasValue_zero _
    · exact AuxNS.hasValue_zero _
  add_mem' := by
    intro a b ha hb
    have ha' : PairCond D₁ D₂ W a := ha
    have hb' : PairCond D₁ D₂ W b := hb
    refine ⟨?_, ?_, ?_⟩
    · exact mem_riemannRochSpace_iff.mp
        (add_mem (mem_riemannRochSpace_iff.mpr ha'.1) (mem_riemannRochSpace_iff.mpr hb'.1))
    · exact mem_riemannRochSpace_iff.mp
        (add_mem (mem_riemannRochSpace_iff.mpr ha'.2.1) (mem_riemannRochSpace_iff.mpr hb'.2.1))
    · intro nd hnd
      obtain ⟨c, hc₁, hc₂⟩ := ha'.2.2 nd hnd
      obtain ⟨d, hd₁, hd₂⟩ := hb'.2.2 nd hnd
      exact ⟨c + d, AuxNS.hasValue_add hc₁ hd₁, AuxNS.hasValue_add hc₂ hd₂⟩
  smul_mem' := by
    intro r a ha
    have ha' : PairCond D₁ D₂ W a := ha
    refine ⟨?_, ?_, ?_⟩
    · exact mem_riemannRochSpace_iff.mp (Submodule.smul_mem _ r (mem_riemannRochSpace_iff.mpr ha'.1))
    · exact mem_riemannRochSpace_iff.mp (Submodule.smul_mem _ r (mem_riemannRochSpace_iff.mpr ha'.2.1))
    · intro nd hnd
      obtain ⟨c, hc₁, hc₂⟩ := ha'.2.2 nd hnd
      exact ⟨r * c, AuxNS.hasValue_smul r hc₁, AuxNS.hasValue_smul r hc₂⟩

private theorem aux_count (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k)
    (hqN : ¬ q ∣ N) (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hE : IsGoodAux P E)
    (hdeg₁ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤ (fibreDivFst P E).degree)
    (hdeg₂ : 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card ≤ (fibreDivSnd P E).degree)
    {m : ℕ} (g : Fin m → ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N))
    (hg : ∀ a, PairCond (fibreDivFst P E) (fibreDivSnd P E) W (g a)) (hli : LinearIndependent k g) :
    (m : ℤ) ≤ E.degree + 2 - 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - W.card := by
  classical
  have hRR : ∀ D : Divisor k (modularFunctionFieldC k N),
      2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 ≤ D.degree →
        (ell D : ℤ) = D.degree + 1 - genusFF k ↥(modularFunctionFieldC k N) :=
    fun D hD => AuxNS.ell_eq_of_eq_fullC k N (modularFunctionFieldC k N)
      (modularFunctionFieldC_eq_modularFunctionFieldFullC k q N hqN) D hD
  haveI : IsCurveOver k (modularFunctionFieldC k N) := isCurveOver_modularFunctionFieldC_of_perfectField k N
  haveI hL0 : FiniteDimensional k (LSpace (0 : Divisor k (modularFunctionFieldC k N))) := by
    refine Module.finite_of_finrank_pos ?_
    have h1 : ell (0 : Divisor k (modularFunctionFieldC k N)) = 1 :=
      ell_zero_eq_one_of_constantsAreBase (constantsAreBase_modularFunctionFieldC_of_perfectField k N)
    show 0 < ell (0 : Divisor k (modularFunctionFieldC k N))
    omega
  haveI hF₁ : FiniteDimensional k (riemannRochSpace (fibreDivFst P E - nodeDiv W)) :=
    finiteDimensional_lSpace (fibreDivFst P E - nodeDiv W)
  haveI hF₂ : FiniteDimensional k (riemannRochSpace (fibreDivSnd P E)) :=
    finiteDimensional_lSpace (fibreDivSnd P E)

  haveI : FiniteDimensional k (Submodule.span k (Set.range g)) :=
    FiniteDimensional.span_of_finite k (Set.finite_range g)
  have hU : Module.finrank k (Submodule.span k (Set.range g)) = m := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hUV : Submodule.span k (Set.range g) ≤ pairCondSpace (fibreDivFst P E) (fibreDivSnd P E) W := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact hg a
  obtain ⟨φ, hφ⟩ : ∃ φ : Submodule.span k (Set.range g) →ₗ[k] ↥(modularFunctionFieldC k N),
      φ = (LinearMap.snd k ↥(modularFunctionFieldC k N) ↥(modularFunctionFieldC k N)).comp
        (Submodule.span k (Set.range g)).subtype := ⟨_, rfl⟩

  have hrange : LinearMap.range φ ≤ riemannRochSpace (fibreDivSnd P E) := by
    rw [hφ, LinearMap.range_comp, Submodule.range_subtype, Submodule.map_span_le]
    rintro _ ⟨a, rfl⟩
    exact mem_riemannRochSpace_iff.mpr (hg a).2.1
  have h₂ : Module.finrank k (LinearMap.range φ) ≤ ell (fibreDivSnd P E) := Submodule.finrank_mono hrange

  have hsnd : ∀ x : LinearMap.ker φ, ((x.1 : ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N))).2 = 0 := by
    intro x

    have h' : φ x.1 = 0 := LinearMap.mem_ker.mp x.2
    have h3 := congrArg (fun ψ : ↥(Submodule.span k (Set.range g)) →ₗ[k] ↥(modularFunctionFieldC k N) => ψ x.1) hφ
    have h4 : ((LinearMap.snd k ↥(modularFunctionFieldC k N) ↥(modularFunctionFieldC k N)).comp (Submodule.span k (Set.range g)).subtype) x.1 = 0 :=
      h3.symm.trans h'
    exact h4
  have h₁ : Module.finrank k (LinearMap.ker φ) ≤ ell (fibreDivFst P E - nodeDiv W) := by
    refine LinearMap.finrank_le_finrank_of_injective (f := LinearMap.codRestrict
      (riemannRochSpace (fibreDivFst P E - nodeDiv W))
      ((LinearMap.fst k ↥(modularFunctionFieldC k N) ↥(modularFunctionFieldC k N)).comp
        ((Submodule.span k (Set.range g)).subtype.comp (LinearMap.ker φ).subtype)) ?hmem) ?hinj
    case hmem =>
      intro x
      exact fst_mem_riemannRochSpace_sub_nodeDiv hW hqN E (hUV x.1.2) (hsnd x)
    case hinj =>
      intro x y hxy
      have hx1 : ((x.1 : ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N))).1 = ((y.1 : ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N))).1 := congrArg Subtype.val hxy
      have hx2 : ((x.1 : ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N))).2 = ((y.1 : ↥(modularFunctionFieldC k N) × ↥(modularFunctionFieldC k N))).2 := (hsnd x).trans (hsnd y).symm
      exact Subtype.ext (Subtype.ext (Prod.ext hx1 hx2))
  have hle : Module.finrank k (Submodule.span k (Set.range g))
      ≤ ell (fibreDivSnd P E) + ell (fibreDivFst P E - nodeDiv W) :=
    calc Module.finrank k (Submodule.span k (Set.range g))
        = Module.finrank k (LinearMap.range φ) + Module.finrank k (LinearMap.ker φ) :=
          (LinearMap.finrank_range_add_finrank_ker φ).symm
      _ ≤ ell (fibreDivSnd P E) + ell (fibreDivFst P E - nodeDiv W) := add_le_add h₂ h₁

  have hdeg₁' : Divisor.degree (fibreDivFst P E - nodeDiv W) = (fibreDivFst P E).degree - W.card := by
    rw [map_sub, degree_nodeDiv]
  have hRR₁ := hRR (fibreDivFst P E - nodeDiv W) (by rw [hdeg₁']; omega)
  have hRR₂ := hRR (fibreDivSnd P E) (by omega)
  have hsum := degree_fibreDivFst_add_degree_fibreDivSnd (P := P) E hE.2
  rw [hdeg₁'] at hRR₁
  omega

private theorem aux_genus_le (P : PlaceSpecialization A q N data hKr k red hα hβ) (hqN : ¬ q ∣ N) :
    ∃ W : Finset (Place k (modularFunctionFieldC k N)), (∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) ∧
      (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) : ℤ) + 1
        ≤ 2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) + W.card := by
  obtain ⟨W, hW⟩ : ∃ W : Finset (Place k (modularFunctionFieldC k N)), ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k :=
    ⟨(ssPlaces_finite q N k).toFinset, fun w => (ssPlaces_finite q N k).mem_toFinset⟩
  refine ⟨W, hW, le_of_eq ?_⟩
  exact_mod_cast genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces q N hqN k W hW

private noncomputable def jBarN (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩

omit [IsAlgClosed k] [DecidableEq k] in
private theorem aux_aux_jFun_value (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {c : k × k} (hc : IsCentreOf k N c (P.reduceFst V)) :
    ∃ a : A, 0 < V.ord (jFun N q - algebraMap (AlgebraicClosure ℚ)
        (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧ red a = c.1 := by
  have hex : ∃ a : A, 0 < (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
      (jBarN N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) := by
    by_contra hno
    have hle : ∀ a : A, (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
        (jBarN N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
          ≤ 0 := fun a => not_lt.mp fun hlt => hno ⟨a, hlt⟩
    have hlt : (P.reduceFst V).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 :=
      P.d0_j_pole _ hle
    exact absurd hlt (not_lt.mpr ((P.reduceFst V).ord_nonneg_of_mem hc.jGeomGen_mem))
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_, ?_⟩
  · have htrans : heckeAlphaBar (AlgebraicClosure ℚ) N q
        (jBarN N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
        = jFun N q
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := by
      rw [map_sub]
      congr 1
    have hord := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V
      (jBarN N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
    rw [htrans] at hord
    rw [hord]
    exact mul_pos
      (Int.natCast_pos.mpr (ramificationIndexAlong_pos (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα V)) ha
  · have h1 : IsCentreOf k N (red a, c.2) (P.reduceFst V) := ⟨P.d0_j _ a ha, hc.2⟩
    exact congrArg Prod.fst (h1.eq hc)

omit [Fact q.Prime] [CharP k q] [IsAlgClosed k] [DecidableEq k] in
open scoped IntermediateField.algebraAdjoinAdjoin in
private theorem essFiniteType_modularFunctionFieldC :
    Algebra.EssFiniteType k (modularFunctionFieldC k N) := by
  change Algebra.EssFiniteType k (IntermediateField.adjoin k ({jqModC k, jqNModC k N} : Set (LaurentSeries k)))
  have hfin : ({jqModC k, jqNModC k N} : Set (LaurentSeries k)).Finite := (Set.finite_singleton _).insert _
  haveI : Algebra.FiniteType k (Algebra.adjoin k ({jqModC k, jqNModC k N} : Set (LaurentSeries k))) :=
    .adjoin_of_finite hfin
  haveI : Algebra.EssFiniteType (Algebra.adjoin k ({jqModC k, jqNModC k N} : Set (LaurentSeries k)))
      (IntermediateField.adjoin k ({jqModC k, jqNModC k N} : Set (LaurentSeries k))) :=
    .of_isLocalization _ (nonZeroDivisors _)
  exact .comp _ (Algebra.adjoin k ({jqModC k, jqNModC k N} : Set (LaurentSeries k))) _

private theorem aux_aux_exists_strictFst (hqN : ¬ q ∣ N)
    (Bd : Finset (Place k (modularFunctionFieldC k N))) (w₀ : Place k (modularFunctionFieldC k N)) :
    ∃ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.IsStrictFst V ∧ P.reduceFst V ∉ Bd ∧ ∃ c : k × k, IsCentreOf k N c (P.reduceFst V) := by
  classical
  haveI : IsCurveOver k (modularFunctionFieldC k N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField k N
  haveI : Algebra.EssFiniteType k (modularFunctionFieldC k N) := essFiniteType_modularFunctionFieldC
  obtain ⟨Kc, g₀, hRR⟩ := exists_canonicalDivisor_genus_riemannRoch k (modularFunctionFieldC k N)
  obtain ⟨d₁', d₂', Q₁', Q₂', T₁', T₂', Qs, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQs, -, -,
      -⟩ :=
    P.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq hqN {w₀}
      (Finset.singleton_nonempty w₀) ∅ Kc g₀ hRR
  have hne : P.reduceFst Qs ≠ frobOnPlacesGeomLevel k N data hKr (P.reduceFst Qs) := by
    intro h
    exact hQs.2 (by rw [← h, ← h])
  obtain ⟨d₁, d₂, Q₁, Q₂, T₁, T₂, Qs', hd₁, -, hQ₁, -, -, -, hT₁, -, -, hTB, -, -, -, hcen, -, -, -, -, -, -,
      -⟩ :=
    P.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq hqN
      {P.reduceFst Qs, frobOnPlacesGeomLevel k N data hKr (P.reduceFst Qs)} (Finset.insert_nonempty _ _)
      Bd Kc g₀ hRR
  rw [Finset.card_pair hne] at hd₁
  have hd : 0 < d₁ := by omega
  have hmem : P.reduceFst (Q₁ ⟨0, hd⟩) ∈ T₁ := (hT₁ _).mpr ⟨⟨0, hd⟩, rfl⟩
  refine ⟨Q₁ ⟨0, hd⟩, hQ₁ _, fun hB => Finset.disjoint_left.mp hTB hmem hB, ?_⟩
  obtain ⟨c, hc, -, -⟩ := hcen _ hmem
  exact ⟨c, hc⟩

omit [Fact q.Prime] [CharP k q] [IsAlgClosed k] [DecidableEq k] in
private theorem aux_aux_exists_finset_zeros [IsCurveOver k (modularFunctionFieldC k N)] (c : k) :
    ∃ Z : Finset (Place k (modularFunctionFieldC k N)),
      ∀ v : Place k (modularFunctionFieldC k N), 0 < v.ord (jGeomGen k N - algebraMap k _ c) → v ∈ Z := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := k)
    (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) c) (jGeomGen_sub_algebraMap_ne_zero k N c)
  exact ⟨D.support, fun v hv => Finsupp.mem_support_iff.mpr (by rw [hD v]; exact hv.ne')⟩

private theorem aux_exists_goodAux (hqN : ¬ q ∣ N) (S : Finset k) (B : Finset (Place k (modularFunctionFieldC k N)))
    (t₁ t₂ : Place k (modularFunctionFieldC k N)) (n : ℤ) :
    ∃ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)), IsGoodAux P E ∧
      (∀ V ∈ E.support,
        (∃ a : A, 0 < V.ord (jFun N q - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧ red a ∉ S) ∧
          P.reduceFst V ∉ B ∧ P.reduceSnd V ∉ B ∧ P.reduceFst V ≠ t₁ ∧ P.reduceSnd V ≠ t₂) ∧
      n ≤ (fibreDivFst P E).degree ∧ n ≤ (fibreDivSnd P E).degree := by
  classical
  haveI hCO : IsCurveOver k (modularFunctionFieldC k N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField k N
  have hq : 0 < q := (Fact.out : q.Prime).pos

  choose Z hZ using fun c : k => aux_aux_exists_finset_zeros (k := k) (N := N) c
  choose rt hrt using fun s : k => IsAlgClosed.exists_pow_nat_eq s hq
  set B₀ : Finset (Place k (modularFunctionFieldC k N)) := insert t₁ (insert t₂ B) with hB₀
  have hinj := frobOnPlacesGeomLevel_injective k N data hKr
  set Bd : Finset (Place k (modularFunctionFieldC k N)) :=
    B₀ ∪ B₀.preimage (frobOnPlacesGeomLevel k N data hKr) hinj.injOn ∪ S.biUnion Z
      ∪ S.biUnion (fun s => Z (rt s)) with hBd

  obtain ⟨V, hVs, hVBd, c, hc⟩ := aux_aux_exists_strictFst (P := P) hqN Bd t₁
  simp only [hBd, Finset.mem_union, Finset.mem_preimage, Finset.mem_biUnion, not_or, not_exists, not_and]
    at hVBd
  obtain ⟨⟨⟨hvB₀, hvφ⟩, hvZ⟩, hvZ'⟩ := hVBd
  have hB₀t₁ : t₁ ∈ B₀ := by rw [hB₀]; exact Finset.mem_insert_self _ _
  have hB₀t₂ : t₂ ∈ B₀ := by rw [hB₀]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hB₀B : ∀ w ∈ B, w ∈ B₀ := fun w hw => by
    rw [hB₀]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)

  obtain ⟨a₁, ha₁, hred₁⟩ := aux_aux_jFun_value (P := P) V hc
  have hS₁ : red a₁ ∉ S := by
    intro hs
    rw [hred₁] at hs
    exact hvZ c.1 hs (hZ c.1 _ hc.1)

  set V₂ := atkinLehnerBar N q • V with hV₂
  have hV₂s : P.IsStrictSnd V₂ := (P.isStrictSnd_atkinLehnerBar_smul_iff hqN V).mpr hVs
  have hrS : P.reduceSnd V₂ = P.reduceFst V := P.reduceSnd_atkinLehnerBar_smul hqN V
  have hrF : P.reduceFst V₂ = frobOnPlacesGeomLevel k N data hKr (P.reduceFst V) := by
    rw [hV₂, P.reduceFst_atkinLehnerBar_smul hqN V]
    exact hVs.1.symm
  have hcφ : IsCentreOf k N (c.1 ^ q, c.2 ^ q) (P.reduceFst V₂) := by
    rw [hrF]
    exact hc.frobOnPlacesGeomLevel data hKr
  obtain ⟨a₂, ha₂, hred₂⟩ := aux_aux_jFun_value (P := P) V₂ hcφ
  have hred₂' : red a₂ = c.1 ^ q := hred₂
  have hS₂ : red a₂ ∉ S := by
    intro hs
    have hroot : c.1 = rt (red a₂) := by
      have h0 : (c.1 - rt (red a₂)) ^ q = 0 := by
        rw [sub_pow_char, hrt, ← hred₂']
        exact sub_self _
      exact sub_eq_zero.mp (pow_eq_zero_iff hq.ne' |>.mp h0)
    refine hvZ' (red a₂) hs (hZ (rt (red a₂)) _ ?_)
    rw [← hroot]
    exact hc.1

  set m : ℕ := n.toNat with hm
  refine ⟨Finsupp.single V (m : ℤ) + Finsupp.single V₂ (m : ℤ), ⟨fun W => ?_, fun W hW => ?_⟩, fun W hW => ?_,
    ?_, ?_⟩
  · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
    refine add_nonneg ?_ ?_ <;> split_ifs <;> first | exact Int.natCast_nonneg m | exact le_rfl
  · rcases Finset.mem_union.mp (Finsupp.support_add hW) with h | h
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; exact Or.inl hVs
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; exact Or.inr hV₂s
  · rcases Finset.mem_union.mp (Finsupp.support_add hW) with h | h
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]
      refine ⟨⟨a₁, ha₁, hS₁⟩, fun hB => hvB₀ (hB₀B _ hB), fun hB => hvφ (hB₀B _ ?_),
        fun ht => hvB₀ (ht ▸ hB₀t₁), fun ht => hvφ ?_⟩
      · rwa [hVs.1]
      · rw [hVs.1, ht]; exact hB₀t₂
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]
      refine ⟨⟨a₂, ha₂, hS₂⟩, fun hB => hvφ (hB₀B _ (hrF ▸ hB)), fun hB => hvB₀ (hB₀B _ (hrS ▸ hB)),
        fun ht => hvφ ?_, fun ht => hvB₀ ?_⟩
      · rw [← hrF, ht]; exact hB₀t₁
      · rw [← hrS, ht]; exact hB₀t₂
  ·
    have hdeg : (1 : ℤ) ≤ (P.reduceFst V).deg := by
      haveI := IsCurveOver.finiteResidue (K := k) (P.reduceFst V)
      exact_mod_cast (Module.finrank_pos : 0 < (P.reduceFst V).deg)
    have hE : fibreDivFst P (Finsupp.single V (m : ℤ) + Finsupp.single V₂ (m : ℤ))
        = Finsupp.single (P.reduceFst V) (m : ℤ) := by
      rw [fibreDivFst, Finsupp.filter_add, Finsupp.filter_single_of_pos _ hVs,
        Finsupp.filter_single_of_neg _ (not_isStrictFst_of_isStrictSnd hV₂s), add_zero,
        Finsupp.mapDomain_single]
    rw [hE, Divisor.degree_single]
    calc n ≤ (m : ℤ) := Int.self_le_toNat n
      _ ≤ (m : ℤ) * (P.reduceFst V).deg := le_mul_of_one_le_right (Int.natCast_nonneg m) hdeg
  · have hdeg : (1 : ℤ) ≤ (P.reduceSnd V₂).deg := by
      haveI := IsCurveOver.finiteResidue (K := k) (P.reduceSnd V₂)
      exact_mod_cast (Module.finrank_pos : 0 < (P.reduceSnd V₂).deg)
    have hns : ¬ P.IsStrictSnd V := fun h => not_isStrictFst_of_isStrictSnd h hVs
    have hE : fibreDivSnd P (Finsupp.single V (m : ℤ) + Finsupp.single V₂ (m : ℤ))
        = Finsupp.single (P.reduceSnd V₂) (m : ℤ) := by
      rw [fibreDivSnd, Finsupp.filter_add, Finsupp.filter_single_of_neg _ hns,
        Finsupp.filter_single_of_pos _ hV₂s, zero_add, Finsupp.mapDomain_single]
    rw [hE, Divisor.degree_single]
    calc n ≤ (m : ℤ) := Int.self_le_toNat n
      _ ≤ (m : ℤ) * (P.reduceSnd V₂).deg := le_mul_of_one_le_right (Int.natCast_nonneg m) hdeg

private theorem exists_neg_of_mapDomain_filter_neg {X Y : Type*} (r : X → Y) (D : X →₀ ℤ) (p : X → Prop)
    [DecidablePred p] (y : Y) (h : Finsupp.mapDomain r (D.filter p) y < 0) :
    ∃ V, p V ∧ r V = y ∧ D V < 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hge : 0 ≤ Finsupp.mapDomain r (D.filter p) y := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
    refine Finset.sum_nonneg fun x hx => ?_
    simp only [Finsupp.single_apply]
    split_ifs with hr
    · rw [Finsupp.filter_apply]
      split_ifs with hp
      · exact hcon x hp hr
      · exact le_rfl
    · exact le_rfl
  exact absurd h (not_lt.mpr hge)

omit [IsAlgClosed k] [DecidableEq k] in
private theorem degree_add_single_bar (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (n : ℤ) :
    (E + Finsupp.single V n).degree = E.degree + n := by
  rw [map_add, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar (N * q) V, Nat.cast_one, mul_one]

private theorem aux_commonUnit_pole_reduceSnd (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hRL : R.RegularityLaw W)
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) (hqN : ¬ q ∣ N)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV₀ : IsZeroSide P V₀ ∨ P.IsStrictSnd V₀) (S : Finset k)
    (B : Finset (Place k (modularFunctionFieldC k N))) :
    ∃ (g : modularFunctionFieldBar (N * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
      (∀ V, V ≠ V₀ → V.ord g < 0 →
        (∃ a : A, 0 < V.ord (jFun N q - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧ red a ∉ S) ∧
          P.reduceFst V ∉ B ∧ P.reduceSnd V ∉ B) ∧
      (P.reduceSnd V₀).ord (R.residue₂ ⟨g, h₂⟩) = -1 := by
  classical

  obtain ⟨W', hW', hgen⟩ := aux_genus_le P hqN
  rw [Finset.ext fun w => (hW' w).trans (hW w).symm] at hgen

  obtain ⟨E', hE', hgood, hdeg₁, hdeg₂⟩ := aux_exists_goodAux (P := P) hqN S B (P.reduceFst V₀) (P.reduceSnd V₀)
    (2 * (genusFF k ↥(modularFunctionFieldC k N) : ℤ) - 1 + W.card)
  have hE'V₀ : ∀ V ∈ E'.support, P.reduceSnd V ≠ P.reduceSnd V₀ := fun V hV => (hgood V hV).2.2.2.2
  have hE'0 : E' V₀ = 0 := by
    by_contra hne
    exact hE'V₀ V₀ (Finsupp.mem_support_iff.mpr hne) rfl
  set E := E' + Finsupp.single V₀ 1 with hEdef
  have hEeff : ∀ V, 0 ≤ E V := fun V => by
    rw [hEdef, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs
    · exact add_nonneg (hE'.1 V) zero_le_one
    · rw [add_zero]; exact hE'.1 V
  obtain ⟨u, hu₁, hu₂, huE, hli⟩ := aux_lattice R hqN E

  have hnot : ∃ a, ¬ PairCond (fibreDivFst P E') (fibreDivSnd P E') W
      (R.residue₁ ⟨u a, hu₁ a⟩, R.residue₂ ⟨u a, hu₂ a⟩) := by
    by_contra hall
    push Not at hall
    have hcount := aux_count (P := P) W hW hqN E' hE' hdeg₁ hdeg₂ _ hall hli
    have hlow := degree_add_one_sub_genusFF_le_finrank_riemannRochSpace (N * q) E
    have hdegE : E.degree = E'.degree + 1 := by rw [hEdef, degree_add_single_bar]
    rw [hdegE] at hlow
    omega
  obtain ⟨a, ha⟩ := hnot
  have hplus := aux_pairCond_residue_add_snd R hR hO hqN W hW hRL E' hE' V₀ hV₀ hE'V₀ (u a) (huE a) (hu₁ a)
    (hu₂ a)

  have hE't : fibreDivSnd P E' (P.reduceSnd V₀) = 0 := by
    rw [fibreDivSnd, mapDomain_filter_apply_eq_sum_of P.reduceSnd E' P.IsStrictSnd V₀ ∅
      (fun i hi hne => absurd hi (hE'V₀ i (Finsupp.mem_support_iff.mpr hne)))
      (fun i hi => absurd hi (Finset.notMem_empty i)), Finset.sum_empty]
  have hres₂ : R.residue₂ ⟨u a, hu₂ a⟩ ≠ 0 ∧ (P.reduceSnd V₀).ord (R.residue₂ ⟨u a, hu₂ a⟩) = -1 := by
    obtain ⟨hp1, hp2, hp3⟩ := hplus
    by_contra hcon
    apply ha
    refine ⟨hp1, fun w => ?_, hp3⟩
    by_cases h0 : R.residue₂ ⟨u a, hu₂ a⟩ = 0
    · exact Or.inl h0
    right
    have hle := (hp2 w).resolve_left h0
    by_cases hw : w = P.reduceSnd V₀
    · subst hw
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hE't, zero_add] at hle
      rw [hE't, neg_zero]
      have hne : (P.reduceSnd V₀).ord (R.residue₂ ⟨u a, hu₂ a⟩) ≠ -1 := fun h => hcon ⟨h0, h⟩
      dsimp only at hle ⊢
      omega
    · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hw, add_zero] at hle
      exact hle
  obtain ⟨hne₂, hord₂⟩ := hres₂

  obtain ⟨c, g₁, g₂, hg₁, hg₂, -, hr₂⟩ := exists_sub_algebraMap_residue_ne_zero R (u a) (hu₁ a) (hu₂ a)
  set g := u a - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c with hgdef
  have hordg : (P.reduceSnd V₀).ord (R.residue₂ ⟨g, g₂⟩) = -1 := by
    rw [hr₂, ord_sub_algebraMap_of_ord_lt_zero _ _ _ (by omega), hord₂]
  have hgE : g ∈ riemannRochSpace E := sub_mem (huE a) (algebraMap_mem_riemannRochSpace hEeff _)
  have hg0 : g ≠ 0 := by
    intro h
    apply hg₁
    have e : (⟨g, g₁⟩ : R.R₁.integers) = 0 := Subtype.ext h
    rw [e, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor
    (self := hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)) g hg0
  have hDE : ∀ V, -E V ≤ D V := fun V => by
    rw [hD V]
    exact ((mem_riemannRochSpace_iff.mp hgE) V).resolve_left hg0

  have hV₀ord : V₀.ord g = -1 := by
    have hge : -1 ≤ V₀.ord g := by
      have h := hDE V₀
      rw [hD V₀, hEdef, Finsupp.add_apply, Finsupp.single_eq_same, hE'0, zero_add] at h
      exact h
    rcases hV₀ with hzero | hstr
    ·
      have hlaw := hR.2.2.2 g g₁ g₂ hg₁ hg₂ D hD V₀ hzero
      rw [hordg] at hlaw
      obtain ⟨V, hVinf, hVt, hVneg⟩ := exists_neg_of_mapDomain_filter_neg _ _ _ _ (by rw [hlaw]; decide)
      have hVE : V ∈ E.support := by
        rw [Finsupp.mem_support_iff]
        intro h0
        have h := hDE V
        rw [h0, neg_zero] at h
        exact absurd h (not_le.mpr hVneg)
      have hVV₀ : V = V₀ := by
        by_contra hne
        have hVE' : V ∈ E'.support := by
          rw [hEdef, Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_of_ne hne, add_zero] at hVE
          exact Finsupp.mem_support_iff.mpr hVE
        exact hE'V₀ V hVE' hVt
      subst hVV₀
      have h := hDE V
      rw [hD V] at hVneg
      omega
    ·
      have hlaw := hR.2.1 g g₁ g₂ hg₁ hg₂ D hD (P.reduceSnd V₀) hstr.2
      rw [hordg] at hlaw
      obtain ⟨V, hVstr, hVt, hVneg⟩ := exists_neg_of_mapDomain_filter_neg _ _ _ _ (by rw [hlaw]; decide)
      have hVE : V ∈ E.support := by
        rw [Finsupp.mem_support_iff]
        intro h0
        have h := hDE V
        rw [h0, neg_zero] at h
        exact absurd h (not_le.mpr hVneg)
      have hVV₀ : V = V₀ := by
        by_contra hne
        have hVE' : V ∈ E'.support := by
          rw [hEdef, Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_of_ne hne, add_zero] at hVE
          exact Finsupp.mem_support_iff.mpr hVE
        exact hE'V₀ V hVE' hVt
      subst hVV₀
      rw [hD V] at hVneg
      omega
  refine ⟨g, g₁, g₂, hg₁, hg₂, hV₀ord, fun V hVne hVlt => ?_, hordg⟩

  have hVE' : V ∈ E'.support := by
    have h := hDE V
    rw [hD V, hEdef, Finsupp.add_apply, Finsupp.single_eq_of_ne hVne, add_zero] at h
    rw [Finsupp.mem_support_iff]
    omega
  obtain ⟨hj, hB₁, hB₂, -, -⟩ := hgood V hVE'
  obtain ⟨a', ha', haS⟩ := hj
  refine ⟨⟨a', ?_, haS⟩, hB₁, hB₂⟩

  exact ha'

end LatticeRoad

end ModularCurve.PlaceSpecialization.ProlongationTuple

theorem solution
    (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (k : Type) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hRL : R.RegularityLaw W)
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N k) (hqN : ¬ q ∣ N)
    (V₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV₀ : IsZeroSide P V₀ ∨ P.IsStrictSnd V₀) (S : Finset k)
    (B : Finset (Place k (modularFunctionFieldC k N))) :
    ∃ (g : modularFunctionFieldBar (N * q)) (h₁ : g ∈ R.R₁.integers) (h₂ : g ∈ R.R₂.integers),
      R.R₁.residue ⟨g, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨g, h₂⟩ ≠ 0 ∧ V₀.ord g = -1 ∧
      (∀ V, V ≠ V₀ → V.ord g < 0 →
        (∃ a : A, 0 < V.ord (jFun N q - algebraMap (AlgebraicClosure ℚ)
            (modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ)) ∧ red a ∉ S) ∧
          P.reduceFst V ∉ B ∧ P.reduceSnd V ∉ B) ∧
      (P.reduceSnd V₀).ord (R.residue₂ ⟨g, h₂⟩) = -1 := by
  exact ModularCurve.PlaceSpecialization.ProlongationTuple.aux_commonUnit_pole_reduceSnd R hR hO W hRL hW hqN V₀ hV₀ S B

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_commonUnit_pole_reduceSnd_of_regularityLaw (solution)
