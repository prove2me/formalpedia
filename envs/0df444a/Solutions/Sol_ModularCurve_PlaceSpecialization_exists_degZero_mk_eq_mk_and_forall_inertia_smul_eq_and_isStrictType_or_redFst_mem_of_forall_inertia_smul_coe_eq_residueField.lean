-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_degZero_mk_eq_mk_and_forall_inertia_smul_eq_and_isStrictType_or_redFst_mem_of_forall_inertia_smul_coe_eq_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b6a35999-1698-5d93-a59a-952412817fb3

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_inertiaStable_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_nodeValueLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo_iff_ne
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_arithmeticGalois_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceSnd_arithmeticGalois_smul
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw_level_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_finite_setOf_ord_jGeomGen_sub_pos
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Definitions.Def_AlgebraicCurve_RatFuncPlaceClassification
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_fixedStrict_kernelGood_principal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_degZero_mk_eq_mk_and_forall_inertia_smul_eq_and_isStrictType_or_redFst_mem_of_forall_inertia_smul_coe_eq_residueField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.LevelOnePhi.instAddCommGroup ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.numberField_of_finiteDimensional ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.GaussReduction.isLocalHom_constToGauss"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.symPoly_zero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatumQ.mk.injEq ModularCurve.crossingCoord_apply ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatum.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVector.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.TwistVector.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.AnnulusDatum.mk.sizeOf_spec AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.ComponentChart.ofConstantReduction_integers"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_integers ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_dom ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_placeMap ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace GENF

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

def Good (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Finset (Place k (modularFunctionFieldC k 1))) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  P.IsStrictTypeOne V ∨ P.IsStrictTypeTwo V ∨ P.redFst V ∈ W

def Fixed (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V

def NotFixed (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  ¬ Fixed A q V

theorem exists_finset_mem_iff_mem_ssJSet (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (W : Finset (Place k ↥(modularFunctionFieldC k 1))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) :
    ∃ S₀ : Finset k, ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k := by
  classical
  refine ⟨W.preimage (charLGeomPlaceOfPoint k) (charLGeomPlaceOfPoint_injective k).injOn, fun a => ?_⟩
  rw [Finset.mem_preimage, hW, ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq]
  constructor
  · rintro ⟨a', ha', h⟩
    rwa [← charLGeomPlaceOfPoint_injective k h]
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem exists_finset_frob_frob_fixed_not_mem_ssPlaces (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k]
    [DecidableEq k] (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data) :
    ∃ T : Finset (Place k ↥(modularFunctionFieldC k 1)),
      (∀ t ∈ T, t ∉ ssPlaces q 1 k) ∧
      ∀ v : Place k ↥(modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v → v ∉ ssPlaces q 1 k → v ∈ T := by
  classical
  set rts : Finset k := ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots).toFinset with hrts
  refine ⟨(rts.filter (fun a => a ∉ ssJSet q k)).image (charLGeomPlaceOfPoint k) ∪
      {charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k)}, ?_, ?_⟩
  · intro t ht hss
    rw [ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq] at hss
    obtain ⟨a', ha', rfl⟩ := hss
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at ht
    rcases ht with ⟨a, ha, h⟩ | h
    · rw [Finset.mem_filter] at ha
      exact ha.2 (charLGeomPlaceOfPoint_injective k h ▸ ha')
    · exact AlgebraicCurve.RationalFunctionField.placeOfPoint_ne_placeInfty k a' ((charLGeomPlaceEquiv k).injective h)
  · intro v hfix hss
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
    rcases AlgebraicCurve.RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty k ((charLGeomPlaceEquiv k).symm v) with ⟨a, ha⟩ | ha
    · left
      have hv : v = charLGeomPlaceOfPoint k a := by
        rw [← (charLGeomPlaceEquiv k).apply_symm_apply v, ha]; rfl
      refine ⟨a, Finset.mem_filter.mpr ⟨?_, fun hass => hss ?_⟩, hv.symm⟩
      · have hq2 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
        rw [hrts, Multiset.mem_toFinset, Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero k hq2), Polynomial.IsRoot.def,
          Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
        rw [hv, ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint] at hfix
        have := charLGeomPlaceOfPoint_injective k hfix
        rw [← pow_mul, ← sq] at this
        exact this
      · rw [hv, ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq]
        exact ⟨a, hass, rfl⟩
    · right
      rw [← (charLGeomPlaceEquiv k).apply_symm_apply v, ha]

theorem isStrictFst_smul_iff (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) ↔ P.IsStrictFst V := by
  unfold PlaceSpecialization.IsStrictFst
  rw [P.reduceFst_arithmeticGalois_smul σ hσ V, P.reduceSnd_arithmeticGalois_smul σ hσ V]

theorem isStrictSnd_smul_iff (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) ↔ P.IsStrictSnd V := by
  unfold PlaceSpecialization.IsStrictSnd
  rw [P.reduceFst_arithmeticGalois_smul σ hσ V, P.reduceSnd_arithmeticGalois_smul σ hσ V]

theorem good_iff (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Finset (Place k (modularFunctionFieldC k 1))) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) ↔ (P.IsStrictTypeOne V ∨ P.IsStrictTypeTwo V ∨ P.redFst V ∈ W) :=
  Iff.rfl

theorem good_smul_iff (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Finset (Place k (modularFunctionFieldC k 1)))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    (P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) ∨ P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) ∨ P.reduceFst (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V) ∈ W) ↔
      (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W) := by
  rw [isStrictFst_smul_iff P hσ, isStrictSnd_smul_iff P hσ, P.reduceFst_arithmeticGalois_smul σ hσ V]

theorem not_isStrictFst_of_isStrictSnd (P : PlaceSpecialization A q 1 data hKr k red hα hβ) {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h2 : P.IsStrictSnd V) : ¬ P.IsStrictFst V := by
  intro h1; apply h1.2; rw [h1.1, ← h2.1]

theorem exists_eq_of_sum_single_apply_ne_zero {d : ℕ} (Q : Fin d → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hV : (∑ i, Finsupp.single (Q i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V ≠ 0) : ∃ i, Q i = V := by
  classical
  rw [Finsupp.finset_sum_apply] at hV
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
  rw [Finsupp.single_apply] at hi
  split_ifs at hi with h
  · exact ⟨i, h⟩
  · exact absurd rfl hi

theorem one_le_sum_single_apply_self {d : ℕ} (Q : Fin d → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (i : Fin d) :
    (1 : ℤ) ≤ (∑ i', Finsupp.single (Q i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (Q i) := by
  classical
  rw [Finsupp.finset_sum_apply]
  have h : ∀ i' ∈ (Finset.univ : Finset (Fin d)), (0 : ℤ) ≤ (Finsupp.single (Q i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (Q i) := by
    intro i' _; rw [Finsupp.single_apply]; split_ifs <;> norm_num
  refine le_trans ?_ (Finset.single_le_sum h (Finset.mem_univ i))
  rw [Finsupp.single_eq_same]

theorem sum_single_apply_nonneg {d : ℕ} (Q : Fin d → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    (0 : ℤ) ≤ (∑ i', Finsupp.single (Q i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V := by
  classical
  rw [Finsupp.finset_sum_apply]
  exact Finset.sum_nonneg fun i' _ => by rw [Finsupp.single_apply]; split_ifs <;> norm_num

theorem degree_finset_sum_single (O : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) :
    Divisor.degree (∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) = O.card := by
  rw [map_sum]
  simp only [Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar (1 * q), Nat.cast_one, mul_one,
    Finset.sum_const, nsmul_eq_mul]

theorem smul_sum_single_of_orbit {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (O : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) (hO : ∀ V', V' ∈ O ↔ ∃ τ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) τ • V = V') :
    arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) = ∑ V' ∈ O, Finsupp.single V' (1 : ℤ) := by
  classical
  rw [Finset.smul_sum]
  simp only [SemilinearAut.smul_single]
  refine Finset.sum_nbij (fun V' => arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V') (fun V' hV' => ?_) (fun a _ b _ h => smul_left_cancel _ h)
    (fun V' hV' => ?_) (fun _ _ => rfl)
  · rw [hO] at hV' ⊢
    obtain ⟨τ, hτ, rfl⟩ := hV'
    exact ⟨σ * τ, mul_mem hσ hτ, by rw [map_mul, mul_smul]⟩
  · rw [Finset.mem_coe, hO] at hV'
    obtain ⟨τ, hτ, rfl⟩ := hV'
    refine ⟨(arithmeticGalois (modularFunctionFieldFull (1 * q)) σ)⁻¹ • (arithmeticGalois (modularFunctionFieldFull (1 * q)) τ • V), ?_, ?_⟩
    · rw [Finset.mem_coe, hO]
      exact ⟨σ⁻¹ * τ, mul_mem (inv_mem hσ) hτ, by rw [map_mul, map_inv, mul_smul]⟩
    · dsimp only
      rw [smul_inv_smul]

set_option maxHeartbeats 12800000 in

theorem exists_fixed_good_rep_of_orbit [IsAlgClosed k] [DecidableEq k]
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (Rp : P.LevelOneProlongationPair) (hRp : Rp.IsModel) (hOp : Rp.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hV : P.IsStrictTypeOne V ∨ P.IsStrictTypeTwo V ∨ P.redFst V ∈ W)
    (O : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))))
    (hO : ∀ V', V' ∈ O ↔ ∃ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V') :
    ∃ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      (∀ V' ∈ D.support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V' = V') ∧
          (P.IsStrictTypeOne V' ∨ P.IsStrictTypeTwo V' ∨ P.redFst V' ∈ W)) ∧
      ((∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) - D) ∈
          Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) ∧
      ((∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) - D) ∈
          Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  classical

  obtain ⟨R, hR, hRL, hNV, hOL⟩ :=
    ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_regularityLaw_nodeValueLaw_level_one P W hW

  haveI hIC : IsCurveOver k ↥(modularFunctionFieldC k 1) :=
    ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k 1
  haveI hEFT : Algebra.EssFiniteType k ↥(modularFunctionFieldC k 1) := by
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q 1 hqN]
    exact ModularCurve.essFiniteType_modularFunctionFieldFullC k 1
  obtain ⟨w₀, hw₀⟩ := ModularCurve.ssPlaces_nonempty q 1 hqN k
  have hWne : W.Nonempty := ⟨w₀, (hW w₀).mpr hw₀⟩
  have hC : ConstantsAreBase k ↥(modularFunctionFieldC k 1) :=
    AlgebraicCurve.constantsAreBase_of_deg_eq_one w₀ (IsCurveOver.deg_eq_one_of_isAlgClosed w₀)
  obtain ⟨Kc, hRR⟩ :=
    AlgebraicCurve.exists_weilCanonical_riemannRoch k ↥(modularFunctionFieldC k 1) hC

  have hNk : ((1 : ℕ) : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q 1).mp h)
  have hsep := ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero k 1 hNk
  have hfin0 := ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k 1 hsep 0
  have hfin1728 := ModularCurve.finite_setOf_ord_jGeomGen_sub_pos k 1 hsep 1728
  obtain ⟨d₁, d₂, Q₁, Q₂, T₁, T₂, Qs, hd₁, hd₂, hQ₁, hQ₂, hinj₁, hinj₂, hT₁, hT₂, hT₁W, hT₁B, hT₂B,
      hT₁aff, hT₂aff, hT₁sm, hT₂sm, hgp₁, hgp₂, hQs, hQs', hI₁, hI₂⟩ :=
    ModularCurve.PlaceSpecialization.exists_isStrictFst_isStrictSnd_general_position_disjoint_forall_inertia_smul_eq
      P hqN W hWne (hfin0.toFinset ∪ hfin1728.toFinset) Kc (genusFF k ↥(modularFunctionFieldC k 1)) hRR
  have hjB : ∀ (v : Place k ↥(modularFunctionFieldC k 1)) (c : k × k), IsCentreOf k 1 c v →
      v ∉ hfin0.toFinset ∪ hfin1728.toFinset →
      v.evalAt (jGeomGen k 1) ≠ 0 ∧ v.evalAt (jGeomGen k 1) ≠ 1728 := by
    intro v c hc hvB
    rw [hc.evalAt_jGeomGen]
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hvB
    refine ⟨fun h0 => hvB.1 ?_, fun h1 => hvB.2 ?_⟩
    · have h := hc.1; rw [h0] at h; exact h
    · have h := hc.1; rw [h1] at h; exact h
  have hj₁ : ∀ i, (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ≠ 0 ∧
      (P.reduceFst (Q₁ i)).evalAt (jGeomGen k 1) ≠ 1728 := fun i => by
    have hv : P.reduceFst (Q₁ i) ∈ T₁ := (hT₁ _).mpr ⟨i, rfl⟩
    obtain ⟨c, hc, -, -⟩ := hT₁sm _ hv
    exact hjB _ c hc (fun hB => Finset.disjoint_left.mp hT₁B hv hB)
  have hj₂ : ∀ j, (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ≠ 0 ∧
      (P.reduceSnd (Q₂ j)).evalAt (jGeomGen k 1) ≠ 1728 := fun j => by
    have hv : P.reduceSnd (Q₂ j) ∈ T₂ := (hT₂ _).mpr ⟨j, rfl⟩
    obtain ⟨c, hc, -, -⟩ := hT₂sm _ hv
    exact hjB _ c hc (fun hB => Finset.disjoint_left.mp hT₂B hv hB)

  have hgen := ModularCurve.genusFF_modularFunctionFieldBar_mul_add_one_eq_of_ssPlaces q 1 hqN k W hW
  have hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := by
    omega

  obtain ⟨Qb, Qb₂, hQb, -, -, -, -, -, hQbfix, -⟩ :=
    ModularCurve.PlaceSpecialization.exists_families_isStrictTypeOne_isStrictTypeTwo_notMem_forall_inertia_smul_eq P ∅ 1 0

  set Osum : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := ∑ V' ∈ O, Finsupp.single V' (1 : ℤ) with hOsum
  set X : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := Osum - (O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) with hX
  have hXdeg : X ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by
    rw [Divisor.mem_degZero, hX, map_sub, map_zsmul, hOsum, degree_finset_sum_single, Divisor.degree_single,
      ModularCurve.deg_eq_one_modularFunctionFieldBar (1 * q)]
    simp
  have hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • X = X := by
    intro σ hσ
    rw [hX, smul_sub, hOsum, smul_sum_single_of_orbit hσ V O hO, smul_comm, SemilinearAut.smul_single, hQbfix 0 σ hσ]
  have hVgood : P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W := (good_iff P W V).mpr hV
  have hXgood : ∀ V' ∈ X.support, P.IsStrictFst V' ∨ P.IsStrictSnd V' ∨ P.reduceFst V' ∈ W := by
    intro V' hV'
    rw [Finsupp.mem_support_iff, hX, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] at hV'
    by_cases h1 : Osum V' = 0
    · rw [h1, zero_sub, neg_ne_zero, mul_ne_zero_iff, Finsupp.single_apply_ne_zero] at hV'
      rw [hV'.2.1]
      exact Or.inl (hQb 0)
    · rw [hOsum, Finsupp.finset_sum_apply] at h1
      obtain ⟨V'', hV''O, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      rw [Finsupp.single_apply_ne_zero] at hne
      rw [hne.1]
      obtain ⟨τ, hτ, rfl⟩ := (hO V'').mp hV''O
      exact (good_smul_iff P W hτ V).mpr hVgood

  obtain ⟨D₁, D₂, hD₁, hD₂good, ⟨hadm, hmk⟩, hprin⟩ :=
    ModularCurve.PlaceSpecialization.exists_fixedStrict_kernelGood_principal P Rp hRp hOp W hW ⟨X, hXdeg⟩ hXst hXgood

  obtain ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, hdeg0, hx'⟩ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_levelOne
      hR hW hRL hNV hOL Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hgp₁ hgp₂ hdeg D₂ hD₂good hadm hmk

  have hD₁st : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) = D₁ := by
    intro σ hσ
    rw [SemilinearAut.divisor_smul_def, Finsupp.mapDomain_congr (g := id) (fun V' hV' => (hD₁ V' hV').1 σ hσ), Finsupp.mapDomain_id]
  have hD₂cls : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by
    intro σ hσ
    have hC := SemilinearAut.smul_mem_principal (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ) hprin
    have : arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) - D₂ = -((arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (X - D₁ - D₂)) - (X - D₁ - D₂)) := by
      rw [smul_sub, smul_sub, hXst σ hσ, hD₁st σ hσ]; abel
    rw [this]
    exact neg_mem (sub_mem hC hprin)

  set E0 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE0
  set E1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := ∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) with hE1
  have hE0st : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E0 = E0 := by
    intro σ hσ
    rw [hE0, smul_add, Finset.smul_sum, Finset.smul_sum]
    simp only [SemilinearAut.smul_single, hI₁ _ σ hσ, hI₂ _ σ hσ]
  have hfixE' : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ i, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i = Q₁' i) ∧ (∀ j, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j = Q₂' j) := by
    intro σ hσ

    have hQ₁'' : ∀ i, P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i) := fun i => (isStrictFst_smul_iff P hσ _).mpr (hQ₁' i)
    have hQ₂'' : ∀ j, P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j) := fun j => (isStrictSnd_smul_iff P hσ _).mpr (hQ₂' j)
    have hred₁'' : ∀ i, P.reduceFst (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i) = P.reduceFst (Q₁' i) := fun i =>
      P.reduceFst_arithmeticGalois_smul σ hσ _
    have hred₂'' : ∀ j, P.reduceSnd (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j) = P.reduceSnd (Q₂' j) := fun j =>
      P.reduceSnd_arithmeticGalois_smul σ hσ _

    have hinj₁' : Function.Injective fun i => P.reduceFst (Q₁' i) := by
      intro i j h; apply hinj₁; simp only [hred₁] at h; exact h
    have hinj₂' : Function.Injective fun j => P.reduceSnd (Q₂' j) := by
      intro i j h; apply hinj₂; simp only [hred₂] at h; exact h
    have hT₁' : ∀ v, v ∈ T₁ ↔ ∃ i, P.reduceFst (Q₁' i) = v := fun v => by
      rw [hT₁]; simp only [hred₁]
    have hT₂' : ∀ v, v ∈ T₂ ↔ ∃ j, P.reduceSnd (Q₂' j) = v := fun v => by
      rw [hT₂]; simp only [hred₂]
    have hj₁' : ∀ i, (P.reduceFst (Q₁' i)).evalAt (jGeomGen k 1) ≠ 0 ∧ (P.reduceFst (Q₁' i)).evalAt (jGeomGen k 1) ≠ 1728 :=
      fun i => by rw [hred₁]; exact hj₁ i
    have hj₂' : ∀ j, (P.reduceSnd (Q₂' j)).evalAt (jGeomGen k 1) ≠ 0 ∧ (P.reduceSnd (Q₂' j)).evalAt (jGeomGen k 1) ≠ 1728 :=
      fun j => by rw [hred₂]; exact hj₂ j
    have hQs'' : ∀ i, P.reduceFst Qs ≠ P.reduceFst (Q₁' i) := fun i => by rw [hred₁]; exact hQs' i

    have hsE1 : arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E1 = ∑ i, Finsupp.single (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j) (1 : ℤ) := by
      rw [hE1, smul_add, Finset.smul_sum, Finset.smul_sum]; simp only [SemilinearAut.smul_single]
    have hprinE : (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E1 - E1) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by

      have h1 : ((E1 - E0) - (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by
        have := (QuotientAddGroup.eq (s := (Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))).addSubgroupOf _)).mp hx'.symm
        rw [AddSubgroup.mem_addSubgroupOf] at this

        have hcoe : ((-D₂ + ⟨E1 - E0, hdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))))) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) = -(D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) + (E1 - E0) := rfl
        rw [hcoe, neg_add_eq_sub] at this
        exact this
      have h2 := SemilinearAut.smul_mem_principal (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ) h1
      have : arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E1 - E1 = (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • ((E1 - E0) - (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) - ((E1 - E0) - D₂)) + (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) - D₂) := by
        rw [smul_sub, smul_sub, hE0st σ hσ]; abel
      rw [this]
      exact add_mem (sub_mem h2 h1) (hD₂cls σ hσ)
    obtain ⟨f, hf, hford⟩ := hprinE
    have hE := ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_evalAt_ne_levelOne
      hR hW hNV hRL Q₁' (fun i => arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i) Q₂' (fun j => arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j) hQ₁' hQ₁'' hQ₂' hQ₂'' hinj₁' hinj₂'
      (fun i => hred₁'' i) (fun j => hred₂'' j) hT₁' hT₂' hT₁W hT₁aff hT₂aff hj₁' hj₂' hgp₁ hgp₂ Qs hQs hQs'' 1 (by norm_num) f hf
      (fun U => by rw [← hford U, ← hsE1, Finsupp.sub_apply]; push_cast; ring)

    rw [← hsE1] at hE
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hle := one_le_sum_single_apply_self (fun i => arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i) i
      have hmem : (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E1) (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i) ≠ 0 := by
        rw [hsE1, Finsupp.add_apply]
        have := sum_single_apply_nonneg (fun j => arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j) (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i)
        omega
      rw [hE, Finsupp.add_apply] at hmem
      by_cases hA : (∑ i', Finsupp.single (Q₁' i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i) = 0
      · rw [hA, zero_add] at hmem
        obtain ⟨j, hj⟩ := exists_eq_of_sum_single_apply_ne_zero Q₂' _ hmem
        exact absurd ((hj ▸ hQ₂' j : P.IsStrictSnd (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i))) (fun h => not_isStrictFst_of_isStrictSnd P h (hQ₁'' i))
      · obtain ⟨i', hi'⟩ := exists_eq_of_sum_single_apply_ne_zero Q₁' _ hA
        have : i' = i := hinj₁' (by simp only []; rw [← hred₁'' i, ← hi'])
        rw [← hi', this]
    · have hmem : (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E1) (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j) ≠ 0 := by
        rw [hsE1, Finsupp.add_apply]
        have h1 := sum_single_apply_nonneg (fun i => arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₁' i) (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j)
        have h2 := one_le_sum_single_apply_self (fun j => arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j) j
        omega
      rw [hE, Finsupp.add_apply] at hmem
      by_cases hB : (∑ j', Finsupp.single (Q₂' j') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j) = 0
      · rw [hB, add_zero] at hmem
        obtain ⟨i, hi⟩ := exists_eq_of_sum_single_apply_ne_zero Q₁' _ hmem
        exact absurd ((hi ▸ hQ₁' i : P.IsStrictFst (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • Q₂' j))) (not_isStrictFst_of_isStrictSnd P (hQ₂'' j))
      · obtain ⟨j', hj'⟩ := exists_eq_of_sum_single_apply_ne_zero Q₂' _ hB
        have : j' = j := hinj₂' (by simp only []; rw [← hred₂'' j, ← hj'])
        rw [← hj', this]

  refine ⟨(O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) + (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) + (E1 - E0), ?_, ?_, ?_⟩
  ·
    intro V' hV'
    have hcases : (Finsupp.single (Qb 0) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V' ≠ 0 ∨ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V' ≠ 0 ∨ E1 V' ≠ 0 ∨ E0 V' ≠ 0 := by
      by_contra h; push_neg at h; obtain ⟨a1, a2, a3, a4⟩ := h
      apply Finsupp.mem_support_iff.mp hV'
      rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, a1, a2, a3, a4]; simp
    rcases hcases with h | h | h | h
    · rw [Finsupp.single_apply_ne_zero] at h
      rw [h.1]
      exact ⟨hQbfix 0, Or.inl (hQb 0)⟩
    · exact ⟨(hD₁ V' (Finsupp.mem_support_iff.mpr h)).1, (good_iff P W V').mp (by rcases (hD₁ V' (Finsupp.mem_support_iff.mpr h)).2 with h' | h'; exact Or.inl h'; exact Or.inr (Or.inl h'))⟩
    · rw [hE1, Finsupp.add_apply] at h
      by_cases h1 : (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V' = 0
      · rw [h1, zero_add] at h
        obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₂' V' h
        exact ⟨fun σ hσ => (hfixE' σ hσ).2 j, (good_iff P W _).mp (Or.inr (Or.inl (hQ₂' j)))⟩
      · obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₁' V' h1
        exact ⟨fun σ hσ => (hfixE' σ hσ).1 i, (good_iff P W _).mp (Or.inl (hQ₁' i))⟩
    · rw [hE0, Finsupp.add_apply] at h
      by_cases h1 : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) V' = 0
      · rw [h1, zero_add] at h
        obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₂ V' h
        exact ⟨hI₂ j, (good_iff P W _).mp (Or.inr (Or.inl (hQ₂ j)))⟩
      · obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero Q₁ V' h1
        exact ⟨hI₁ i, (good_iff P W _).mp (Or.inl (hQ₁ i))⟩
  ·
    have h1 : ((E1 - E0) - (D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) := by
      have := (QuotientAddGroup.eq (s := (Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))).addSubgroupOf _)).mp hx'.symm
      rw [AddSubgroup.mem_addSubgroupOf] at this
      have hcoe : ((-D₂ + ⟨E1 - E0, hdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))))) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) = -(D₂ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) + (E1 - E0) := rfl
      rw [hcoe, neg_add_eq_sub] at this
      exact this
    have : Osum - ((O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) + (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) + (E1 - E0)) = (X - D₁ - D₂) - ((E1 - E0) - D₂) := by
      rw [hX]; abel
    rw [this]
    exact sub_mem hprin h1
  ·
    have : Osum - ((O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) + (D₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) + (E1 - E0)) = X - D₁ - (E1 - E0) := by
      rw [hX]; abel
    rw [this]
    exact sub_mem (sub_mem hXdeg D₁.2) hdeg0

def orbit (A : ValuationSubring (AlgebraicClosure ℚ)) (q : ℕ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :=
  {V' | ∃ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V'}

theorem self_mem_orbit (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : V ∈ orbit A q V := ⟨1, one_mem _, by rw [map_one, one_smul]⟩

theorem orbit_subset_support {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E = E)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hV : V ∈ E.support) : orbit A q V ⊆ ↑E.support := by
  rintro V' ⟨σ, hσ, rfl⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hst σ hσ, SemilinearAut.divisor_smul_apply, inv_smul_smul]
  exact Finsupp.mem_support_iff.mp hV

theorem orbit_finite {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E = E)
    {V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hV : V ∈ E.support) : (orbit A q V).Finite :=
  (E.support.finite_toSet).subset (orbit_subset_support hst hV)

theorem apply_eq_of_mem_orbit {E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E = E)
    {V V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hV' : V' ∈ orbit A q V) : E V' = E V := by
  obtain ⟨σ, hσ, rfl⟩ := hV'
  conv_lhs => rw [← hst σ hσ]
  exact SemilinearAut.divisor_smul_apply_smul _ _ _

theorem not_fixed_of_mem_orbit {V V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hV : ¬ Fixed A q V) (hV' : V' ∈ orbit A q V) : ¬ Fixed A q V' := by
  obtain ⟨τ, hτ, rfl⟩ := hV'
  intro hfix
  apply hV
  intro σ hσ
  have h := hfix (τ * σ * τ⁻¹) (mul_mem (mul_mem hτ hσ) (inv_mem hτ))
  rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, inv_smul_smul] at h
  exact smul_left_cancel _ h

theorem smul_orbitSum {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hfin : (orbit A q V).Finite) :
    arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (∑ V' ∈ hfin.toFinset, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) =
      ∑ V' ∈ hfin.toFinset, Finsupp.single V' (1 : ℤ) := by
  classical
  rw [Finset.smul_sum]
  simp only [SemilinearAut.smul_single]
  refine Finset.sum_nbij (fun V' => arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V') (fun V' hV' => ?_) (fun a _ b _ h => smul_left_cancel _ h)
    (fun V' hV' => ?_) (fun _ _ => rfl)
  · rw [Set.Finite.mem_toFinset] at hV' ⊢
    obtain ⟨τ, hτ, rfl⟩ := hV'
    exact ⟨σ * τ, mul_mem hσ hτ, by rw [map_mul, mul_smul]⟩
  · rw [Set.Finite.coe_toFinset] at hV' ⊢
    obtain ⟨τ, hτ, rfl⟩ := hV'
    refine ⟨(arithmeticGalois (modularFunctionFieldFull (1 * q)) σ)⁻¹ • (arithmeticGalois (modularFunctionFieldFull (1 * q)) τ • V), ⟨σ⁻¹ * τ, mul_mem (inv_mem hσ) hτ, ?_⟩, ?_⟩
    · rw [map_mul, map_inv, mul_smul]
    · dsimp only
      rw [smul_inv_smul]

open Classical in

theorem exists_fixing_corrector [IsAlgClosed k] [DecidableEq k]
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (Rp : P.LevelOneProlongationPair) (hRp : Rp.IsModel) (hOp : Rp.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) :
    ∀ (n : ℕ) (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      (E.support.filter (NotFixed A q)).card ≤ n →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E = E) →
      (∀ V ∈ E.support, Good P W V) →
      ∃ C : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        C ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) ∧
        C ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))) ∧
        ∀ V ∈ (E - C).support, Fixed A q V ∧ Good P W V := by
  intro n
  induction n with
  | zero =>
    intro E hcard _ hgood
    refine ⟨0, zero_mem _, zero_mem _, fun V hV => ?_⟩
    rw [sub_zero] at hV
    refine ⟨?_, hgood V hV⟩
    by_contra hnf
    have : V ∈ E.support.filter (NotFixed A q) := Finset.mem_filter.mpr ⟨hV, hnf⟩
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    rw [hcard] at this
    exact absurd this (Finset.notMem_empty V)
  | succ n ih =>
    intro E hcard hst hgood
    by_cases hex : ∃ V ∈ E.support, ¬ Fixed A q V
    swap
    · push_neg at hex
      exact ⟨0, zero_mem _, zero_mem _, fun V hV => by rw [sub_zero] at hV; exact ⟨hex V hV, hgood V hV⟩⟩
    obtain ⟨V, hVE, hVnf⟩ := hex
    have hfin := orbit_finite hst hVE

    obtain ⟨D, hDfg, hprin, hdeg⟩ := exists_fixed_good_rep_of_orbit P Rp hRp hOp W hW V (hgood V hVE) hfin.toFinset
      (fun V' => by rw [Set.Finite.mem_toFinset]; rfl)
    set Orb : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := ∑ V' ∈ hfin.toFinset, Finsupp.single V' (1 : ℤ) with hOrb
    have hOrb_apply : ∀ V', Orb V' = if V' ∈ orbit A q V then 1 else 0 := by
      intro V'
      rw [hOrb, Finsupp.finset_sum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_ite_eq' hfin.toFinset V' (fun _ => (1 : ℤ))]
      simp only [Set.Finite.mem_toFinset]

    have hDst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • D = D := by
      intro σ hσ
      rw [SemilinearAut.divisor_smul_def, Finsupp.mapDomain_congr (g := id) (fun V' hV' => (hDfg V' hV').1 σ hσ),
        Finsupp.mapDomain_id]
    set E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := E - E V • (Orb - D) with hE₁
    have hst₁ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • E₁ = E₁ := by
      intro σ hσ
      rw [hE₁, smul_sub, smul_comm, smul_sub, hst σ hσ, hOrb, smul_orbitSum hσ V hfin, ← hOrb, hDst σ hσ]

    have hsub : E₁.support.filter (NotFixed A q) ⊆ (E.support.filter (NotFixed A q)).erase V := by
      intro V' hV'
      obtain ⟨hV'E₁, hV'nf⟩ := Finset.mem_filter.mp hV'
      have hDV' : D V' = 0 := by
        by_contra h
        exact hV'nf ((hDfg V' (Finsupp.mem_support_iff.mpr h)).1)
      rw [Finsupp.mem_support_iff, hE₁, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.sub_apply, hDV', sub_zero,
        hOrb_apply, smul_eq_mul] at hV'E₁
      by_cases hVo : V' ∈ orbit A q V
      · exfalso; apply hV'E₁
        rw [if_pos hVo, mul_one, apply_eq_of_mem_orbit hst hVo, sub_self]
      · rw [if_neg hVo, mul_zero, sub_zero] at hV'E₁
        refine Finset.mem_erase.mpr ⟨fun h => hVo ?_, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hV'E₁, hV'nf⟩⟩
        rw [h]; exact self_mem_orbit V
    have hcard₁ : (E₁.support.filter (NotFixed A q)).card ≤ n := by
      have h1 := Finset.card_le_card hsub
      have hVmem : V ∈ E.support.filter (NotFixed A q) := Finset.mem_filter.mpr ⟨hVE, hVnf⟩
      have h2 := Finset.card_erase_of_mem hVmem
      omega
    have hgood₁ : ∀ V' ∈ E₁.support, Good P W V' := by
      intro V' hV'
      by_cases h1 : V' ∈ E.support
      · exact hgood V' h1
      · by_cases h2 : V' ∈ D.support
        · exact (hDfg V' h2).2
        · exfalso
          apply Finsupp.mem_support_iff.mp hV'
          have hEV' : E V' = 0 := Finsupp.notMem_support_iff.mp h1
          have hVo : V' ∉ orbit A q V := fun h => h1 (orbit_subset_support hst hVE h)
          rw [hE₁, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.notMem_support_iff.mp h2, hEV',
            hOrb_apply, if_neg hVo]
          simp
    obtain ⟨C', hC'p, hC'd, hC'fg⟩ := ih E₁ hcard₁ hst₁ hgood₁
    refine ⟨E V • (Orb - D) + C', add_mem (zsmul_mem hprin _) hC'p, add_mem (zsmul_mem hdeg _) hC'd, fun V' hV' => ?_⟩
    apply hC'fg V'
    rwa [hE₁, sub_sub]

end GENF

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (IsLocalRing.ResidueField A) q] [DecidableEq (IsLocalRing.ResidueField A)]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr (IsLocalRing.ResidueField A) (IsLocalRing.residue A) hα hβ)
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place (IsLocalRing.ResidueField A) (modularFunctionFieldC (IsLocalRing.ResidueField A) 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 (IsLocalRing.ResidueField A))
    (D₀ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))))
    (hD₀ : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ •
            (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
          = (D₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))) :
    ∃ D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q)))),
      Pic0.mk D = Pic0.mk D₀ ∧
      ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ,
            arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧
          (P.IsStrictTypeOne V ∨ P.IsStrictTypeTwo V ∨ P.redFst V ∈ W) := by
  classical
  haveI := ValuationSubring.isAlgClosed_residueField A

  have hval : LevelOneProlongationPair.NodeValueLaw q (IsLocalRing.residue A) :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.nodeValueLaw q (IsLocalRing.residue A)
  obtain ⟨S₀, hS₀⟩ := GENF.exists_finset_mem_iff_mem_ssJSet q (IsLocalRing.ResidueField A) W hW
  have hNR : R.RegularityLaw S₀ :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.regularityLaw R (fun a ha => (hS₀ a).mp ha)

  obtain ⟨T, hT, hTcompl⟩ := GENF.exists_finset_frob_frob_fixed_not_mem_ssPlaces q (IsLocalRing.ResidueField A) data hKr

  have hx : Pic0.mk D₀ ∈ inertiaInvariants A (1 * q) := by
    rw [mem_inertiaInvariants]
    intro σ hσ
    rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by rw [SemilinearAut.coe_degZeroSMulHom]; exact hD₀ σ hσ))

  obtain ⟨E₁, hE₁x, hE₁st, hE₁T⟩ :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_inertiaStable_rep_redFst_redSnd_notMem_of_forall_notMem_ssPlaces
      R hR hO hval S₀ hS₀ hNR T hT ⟨Pic0.mk D₀, hx⟩

  have hgood : ∀ V ∈ (E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).support, GENF.Good P W V := by
    intro V hV
    by_cases hfix : frobOnPlacesGeomLevel (IsLocalRing.ResidueField A) 1 data hKr (frobOnPlacesGeomLevel (IsLocalRing.ResidueField A) 1 data hKr (P.redFst V)) = P.redFst V
    ·
      right; right
      rw [hW]
      by_contra hss
      exact (hE₁T V hV).1 (hTcompl _ hfix hss)
    · rcases (ModularCurve.PlaceSpecialization.isStrictTypeOne_or_isStrictTypeTwo_iff_ne P V).mpr hfix with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

  obtain ⟨C, hCp, hCd, hCfg⟩ := GENF.exists_fixing_corrector P R hR hO W hW _ (E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) le_rfl hE₁st hgood
  refine ⟨⟨(E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) - C, sub_mem E₁.2 hCd⟩, ?_, ?_⟩
  · have hE₁x' : Pic0.mk E₁ = Pic0.mk D₀ := hE₁x
    rw [← hE₁x']
    show (QuotientAddGroup.mk _ : Pic0 _ _) = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have hcoe : ((-(⟨(E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) - C, sub_mem E₁.2 hCd⟩ :
        ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))))) + E₁ :
          ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (1 * q))))) : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) =
          -((E₁ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) - C) + E₁ := rfl
    rw [hcoe, neg_sub, sub_add_cancel]
    exact hCp
  · intro V hV
    exact hCfg V hV

end S_ModularCurve_PlaceSpecialization_exists_degZero_mk_eq_mk_and_forall_inertia_smul_eq_and_isStrictType_or_redFst_mem_of_forall_inertia_smul_coe_eq_residueField
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_degZero_mk_eq_mk_and_forall_inertia_smul_eq_and_isStrictType_or_redFst_mem_of_forall_inertia_smul_coe_eq_residueField (solution)
