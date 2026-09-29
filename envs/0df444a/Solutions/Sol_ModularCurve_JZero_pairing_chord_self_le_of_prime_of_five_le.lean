-- Prove2me | solution 1 for ModularCurve.JZero.pairing_chord_self_le_of_prime_of_five_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/31cc7d77-8dac-511c-b46e-615023935ef4

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_ModularCurve_constantsAreBase_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_finiteDimensional_lSpace_zero_of_constantsAreBase
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero
import Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_add_pointHt_le
import Theorems.Thm_AlgebraicCurve_pointHt_mul_eq_add
import Theorems.Thm_ModularCurve_JZero_absLogHeight_chordVec_eq_evalAt_of_ne
import Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_JZero_exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le
import Theorems.Thm_ModularCurve_JZero_sum_pairHt_twoLine_ledger_of_nonCuspidal_of_prime_of_five_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.MultCovering.instAlgebraFbar ModularCurve.MultCovering.instFieldFbar ValuationSubring.instIsAlgClosedResidueField instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.LevelOnePhi.instAddCommGroup instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.baseChangeHom_tmul AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.MultCovering.ssValue_edgeOf ModularCurve.MultCovering.ChartCtx.mk.sizeOf_spec ModularCurve.MultCovering.ChartCtx.mk.injEq ModularCurve.MultCovering.chart_one ModularCurve.MultCovering.chart_zero AlgebraicCurve.ComponentChart.comap_placeMap AlgebraicCurve.ComponentChart.comap_residue_apply AlgebraicCurve.ComponentChart.coe_comapIntegersEquiv AlgebraicCurve.ComponentChart.comapResidue_apply AlgebraicCurve.ComponentChart.comap_integers AlgebraicCurve.ComponentChart.comap_dom AlgebraicCurve.ComponentChart.mem_comapIntegers AlgebraicCurve.Annulus.comap_param AlgebraicCurve.Annulus.comap_dom AlgebraicCurve.Annulus.comap_modulus AlgebraicCurve.ComponentChart.mem_comap_integers AlgebraicCurve.ComponentChart.comap_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_integers ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_nodes ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_dom ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_placeMap ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd"
p2m_attr_erase "simp" "ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.MultCovering.AnnCtx.mk.sizeOf_spec ModularCurve.MultCovering.AnnCtx.mk.injEq ModularCurve.MultCovering.FamData.mk.sizeOf_spec ModularCurve.MultCovering.FamCtx.mk.injEq ModularCurve.MultCovering.FamData.mk.injEq ModularCurve.MultCovering.FamCtx.mk.sizeOf_spec ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.coe_nodeConst ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue₁_apply AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of AlgebraicCurve.chowForm_zero AlgebraicCurve.secProd_zero ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve KaehlerDifferential

noncomputable section

namespace P2MW

section Eval

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem evalAt_zero (Q : Place K F) : Q.evalAt (0 : F) = 0 := by
  have h := Q.evalAt_algebraMap_eq (0 : K)
  rwa [map_zero] at h

private theorem ord_nonneg_of_mem (Q : Place K F) {f : F} (hf0 : f ≠ 0) (hf : f ∈ Q.toValuationSubring) :
    0 ≤ Q.ord f := by
  have h1 : Q.adicValuation f ≤ 1 := by
    have := Q.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : Q.toValuationSubring) : F) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := Q.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (Q.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (Q.adicValuation f))
  omega

private theorem mem_of_eq_zero_or_ord_nonneg (Q : Place K F) {f : F} (h : f = 0 ∨ 0 ≤ Q.ord f) :
    f ∈ Q.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · exact Q.mem_toValuationSubring_of_ord_nonneg_alt hf0 (h.resolve_left hf0)

private theorem ord_eq_zero_of_evalAt_ne_zero (Q : Place K F) (hQ : Q.IsRational) {f : F}
    (hf : f ∈ Q.toValuationSubring) (h : Q.evalAt f ≠ 0) : Q.ord f = 0 := by
  have hres : IsLocalRing.residue Q.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0; apply h
    apply Q.algebraMap_residueField_injective
    rw [Q.algebraMap_evalAt hQ hf, h0, map_zero]
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have := Q.ord_coe_unit u
  rwa [hu] at this

private theorem ne_zero_of_evalAt_ne_zero (Q : Place K F) {f : F} (h : Q.evalAt f ≠ 0) : f ≠ 0 := by
  rintro rfl; exact h (evalAt_zero Q)

private theorem evalAt_eq_zero_of_ord_pos (Q : Place K F) (hQ : Q.IsRational) {f : F}
    (hf : f ∈ Q.toValuationSubring) (h : 0 < Q.ord f) : Q.evalAt f = 0 := by
  by_contra hne
  have := ord_eq_zero_of_evalAt_ne_zero Q hQ hf hne
  omega

private theorem ord_pos_of_evalAt_eq_zero (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ Q.toValuationSubring) (h : Q.evalAt f = 0) : 0 < Q.ord f := by
  rcases (ord_nonneg_of_mem Q hf0 hf).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd h (Q.evalAt_ne_zero_of_ord_eq_zero hQ hf0 heq.symm)

private theorem evalAt_add_of_mem (Q : Place K F) (hQ : Q.IsRational) {f g : F}
    (hf : f ∈ Q.toValuationSubring) (hg : g ∈ Q.toValuationSubring) :
    Q.evalAt (f + g) = Q.evalAt f + Q.evalAt g := by
  apply Q.algebraMap_residueField_injective
  rw [map_add, Q.algebraMap_evalAt hQ (add_mem hf hg), Q.algebraMap_evalAt hQ hf, Q.algebraMap_evalAt hQ hg,
    ← map_add]
  rfl

private theorem evalAt_neg_of_mem (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf : f ∈ Q.toValuationSubring) :
    Q.evalAt (-f) = -Q.evalAt f := by
  apply Q.algebraMap_residueField_injective
  rw [map_neg, Q.algebraMap_evalAt hQ (neg_mem hf), Q.algebraMap_evalAt hQ hf, ← map_neg]
  rfl

private theorem evalAt_sub_of_mem (Q : Place K F) (hQ : Q.IsRational) {f g : F}
    (hf : f ∈ Q.toValuationSubring) (hg : g ∈ Q.toValuationSubring) :
    Q.evalAt (f - g) = Q.evalAt f - Q.evalAt g := by
  rw [sub_eq_add_neg, evalAt_add_of_mem Q hQ hf (neg_mem hg), evalAt_neg_of_mem Q hQ hg, ← sub_eq_add_neg]

private theorem smul_mem_of_mem (Q : Place K F) (a : K) {f : F} (hf : f ∈ Q.toValuationSubring) :
    a • f ∈ Q.toValuationSubring := by
  rw [Algebra.smul_def]; exact mul_mem (Q.algebraMap_mem' a) hf

private theorem evalAt_smul_of_mem (Q : Place K F) (hQ : Q.IsRational) (a : K) {f : F}
    (hf : f ∈ Q.toValuationSubring) : Q.evalAt (a • f) = a * Q.evalAt f := by
  rw [Algebra.smul_def, Q.evalAt_mul_of_mem hQ (Q.algebraMap_mem' a) hf, Q.evalAt_algebraMap_eq]

private theorem evalAt_sum_smul_of_mem {ι : Type*} (S : Finset ι) (Q : Place K F) (hQ : Q.IsRational)
    (c : ι → K) {f : ι → F} (hf : ∀ i, f i ∈ Q.toValuationSubring) :
    Q.evalAt (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i * Q.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact evalAt_zero Q
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add_of_mem Q hQ (smul_mem_of_mem Q _ (hf a)) (sum_mem fun i _ => smul_mem_of_mem Q _ (hf i)),
      evalAt_smul_of_mem Q hQ _ (hf a), ih]

private theorem inv_mem_of_ord_eq_zero (Q : Place K F) {f : F} (hf0 : f ≠ 0) (h : Q.ord f = 0) :
    f⁻¹ ∈ Q.toValuationSubring :=
  Q.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf0) (by rw [Q.ord_inv, h, neg_zero])

private theorem evalAt_mul_evalAt_inv (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf0 : f ≠ 0) (h : Q.ord f = 0) :
    Q.evalAt f * Q.evalAt f⁻¹ = 1 := by
  rw [← Q.evalAt_mul_of_mem hQ (Q.mem_toValuationSubring_of_ord_nonneg_alt hf0 h.ge) (inv_mem_of_ord_eq_zero Q hf0 h),
    mul_inv_cancel₀ hf0, Q.evalAt_one]

private theorem exists_ord_eq_one (Q : Place K F) : ∃ t : F, Q.ord t = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q.toValuationSubring
  exact ⟨(π : F), Q.ord_coe_irreducible hπ⟩

end Eval

end P2MW

end

namespace P2MW

open AlgebraicCurve ModularCurve KaehlerDifferential

section Generic2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem ne_zero_of_notMem {D : Divisor K F} {f : F} (hf : f ∉ riemannRochSpace D) : f ≠ 0 := by
  rintro rfl; exact hf (zero_mem _)

private theorem ord_eq_of_mem_notMem {D : Divisor K F} {f : F} (w : Place K F)
    (hf : f ∈ riemannRochSpace D) (hf' : f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    w.ord f + D w = 0 := by
  classical
  have hf0 := ne_zero_of_notMem hf'
  have hge : -D w ≤ w.ord f := ((mem_riemannRochSpace_iff.mp hf) w).resolve_left hf0
  have hlt : w.ord f < -D w + 1 := by
    by_contra hge'
    push Not at hge'
    apply hf'
    rw [mem_riemannRochSpace_iff]
    intro v
    by_cases hv : v = w
    · subst hv; right
      rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl]; linarith
    · rcases (mem_riemannRochSpace_iff.mp hf) v with h | h
      · exact Or.inl h
      · right
        rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hv), sub_zero]; exact h
  omega

private theorem mem_of_span_eq {ι : Type*} (x : ι → F) {D : Divisor K F}
    (hspan : Submodule.span K (Set.range x) = riemannRochSpace D) (i : ι) : x i ∈ riemannRochSpace D :=
  hspan ▸ Submodule.subset_span ⟨i, rfl⟩

private theorem exists_mem_notMem_of_finrank_ne (D : Divisor K F) (w : Place K F)
    (h : Module.finrank K (riemannRochSpace D) ≠
      Module.finrank K (riemannRochSpace (D - Finsupp.single w 1))) :
    ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  classical
  have hle : riemannRochSpace (D - Finsupp.single w 1) ≤ riemannRochSpace D := by
    refine lSpace_mono (Finsupp.le_def.mpr fun v => ?_)
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hne : riemannRochSpace (D - Finsupp.single w 1) ≠ riemannRochSpace D := by
    intro heq; exact h (by rw [heq])
  obtain ⟨f, hf, hnf⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  exact ⟨f, hf, hnf⟩

private theorem exists_forall_ord_le {r : ℕ} (hr : 0 < r) (s : Fin r → F) (v : Place K F) :
    ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

private theorem ord_eq_neg_of_forall_le {r : ℕ} (s : Fin r → F) (hs0 : ∀ i, s i ≠ 0) {D : Divisor K F}
    (hsD : ∀ i, s i ∈ riemannRochSpace D) (w : Place K F) (hbpf : ∃ i, w.ord (s i) + D w = 0)
    (p : Fin r) (hp : ∀ j, w.ord (s p) ≤ w.ord (s j)) : w.ord (s p) = -D w := by
  obtain ⟨i, hi⟩ := hbpf
  have h1 := hp i
  have h2 : -D w ≤ w.ord (s p) := ((mem_riemannRochSpace_iff.mp (hsD p)) w).resolve_left (hs0 p)
  omega

end Generic2

section Bar

variable (N : ℕ) [NeZero N]

private theorem ell_eq_bar [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 1 ≤ Divisor.degree D) :
    (ell D : ℤ) = Divisor.degree D + 1 - (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := essFiniteType_modularFunctionFieldBar N
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  haveI hDCG : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    functionFieldRiemannRoch_modularFunctionFieldBar N
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)])
  have hdegK := degree_canonicalDivisorOf_modularFunctionFieldBar N hω
  have hgen := genus_eq_genusFF_modularFunctionFieldBar N
  have h1 := hRR hω D
  have hneg : Divisor.degree (canonicalDivisorOf hω - D) < 0 := by
    rw [map_sub, hdegK, hgen]; linarith
  have hell : ell (canonicalDivisorOf hω - D) = 0 := by
    show Module.finrank _ (LSpace _) = 0
    rw [AlgebraicCurve.lSpace_eq_bot_of_degree_neg hneg, finrank_bot]
  rw [hell, hgen] at h1
  push_cast at h1
  linarith

private scoped instance finiteDimensional_lSpace_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D) := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : FiniteDimensional (AlgebraicClosure ℚ) (LSpace (0 : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase _ _
      (constantsAreBase_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N)
  exact finiteDimensional_lSpace D

private theorem isRational_bar (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (deg_eq_one_modularFunctionFieldBar N v)

private theorem exists_mem_notMem_bar [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ f ∈ riemannRochSpace D, f ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  apply exists_mem_notMem_of_finrank_ne
  have e1 := ell_eq_bar N D (by omega)
  have hdeg' : Divisor.degree (D - Finsupp.single w 1) = Divisor.degree D - 1 := by
    rw [map_sub, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N w]; push_cast; ring
  have e2 := ell_eq_bar N (D - Finsupp.single w 1) (by rw [hdeg']; omega)
  rw [hdeg'] at e2
  intro heq
  have : (ell D : ℤ) = (ell (D - Finsupp.single w 1) : ℤ) := by
    unfold ell LSpace; exact_mod_cast heq
  omega

private theorem bpf_of_span_eq [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]
    {ι : Type*} (x : ι → modularFunctionFieldBar N)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range x) = riemannRochSpace D)
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D) :
    ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), ∃ i, w.ord (x i) + D w = 0 := by
  intro w
  obtain ⟨f, hf, hf'⟩ := exists_mem_notMem_bar N D hD w
  have : ∃ i, x i ∉ riemannRochSpace (D - Finsupp.single w 1) := by
    by_contra hall
    push Not at hall
    apply hf'
    have hle : Submodule.span (AlgebraicClosure ℚ) (Set.range x) ≤ riemannRochSpace (D - Finsupp.single w 1) :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
    exact hle (hspan ▸ hf)
  obtain ⟨i, hi⟩ := this
  exact ⟨i, ord_eq_of_mem_notMem w (mem_of_span_eq x hspan i) hi⟩

private theorem pos_of_span_eq [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]
    {a : ℕ} (x : Fin a → modularFunctionFieldBar N)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hspan : Submodule.span (AlgebraicClosure ℚ) (Set.range x) = riemannRochSpace D)
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ Divisor.degree D) : 0 < a := by
  by_contra ha
  have ha0 : a = 0 := by omega
  subst ha0
  obtain ⟨f, hf, hf'⟩ := exists_mem_notMem_bar N D hD (cuspInftyBar N)
  have : f ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range x) := hspan ▸ hf
  rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at this
  exact ne_zero_of_notMem hf' this

end Bar

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

namespace P2MW

open AlgebraicCurve ModularCurve KaehlerDifferential

section BarW

variable (N : ℕ) [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]

omit [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)] in
private theorem ratio_mem {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs0 : ∀ i, s i ≠ 0)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (p : Fin r) (hp : ∀ j, w.ord (s p) ≤ w.ord (s j))
    (i : Fin r) : s i * (s p)⁻¹ ∈ w.toValuationSubring :=
  w.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 i) (inv_ne_zero (hs0 p)))
    (by rw [w.ord_mul (hs0 i) (inv_ne_zero (hs0 p)), w.ord_inv]; linarith [hp i])

omit [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)] in
private theorem nsmul_two_add_apply (D K₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : (2 • D + K₀) w = 2 * D w + K₀ w := by
  rw [two_nsmul, Finsupp.add_apply, Finsupp.add_apply]; ring

end BarW
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

namespace P2MW

open AlgebraicCurve ModularCurve

section BarPiv

variable (N : ℕ) [NeZero N]

private theorem regVal_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (o : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) (k e : ℕ)
    (u : modularFunctionFieldBar N) :
    regVal s o t k e u = o.evalAt (u * ((s (pivotIndex s o hr))⁻¹) ^ k * (t⁻¹) ^ e) := by
  rw [regVal]; simp only [dif_pos hr]

private theorem evalVec_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r) :
    evalVec s v i = v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) := by
  rw [evalVec]; simp only [dif_pos hr]

private theorem ord_pivot_le {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  classical
  have hex := exists_forall_ord_le hr s v
  have : pivotIndex s v hr = Classical.choose hex := by rw [pivotIndex, dif_pos hex]
  rw [this]
  exact Classical.choose_spec hex j

private theorem exists_family_span_eq (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    [FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace D)] :
    ∃ (c : ℕ) (t : Fin c → modularFunctionFieldBar N), (∀ i, t i ≠ 0) ∧
      Submodule.span (AlgebraicClosure ℚ) (Set.range t) = riemannRochSpace D := by
  let bs := Module.finBasis (AlgebraicClosure ℚ) (riemannRochSpace D)
  refine ⟨_, fun i => (bs i : modularFunctionFieldBar N), fun i => ?_, ?_⟩
  · intro h0
    apply bs.ne_zero i
    exact Subtype.ext h0
  · have hr : Set.range (fun i => (bs i : modularFunctionFieldBar N)) = (riemannRochSpace D).subtype '' Set.range bs := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, bs.span_eq, Submodule.map_top, Submodule.range_subtype]

end BarPiv
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

namespace P2MW

open AlgebraicCurve

section AbsHeight

private theorem normLogHeight_eq_of_le (E E' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : E ≤ E')
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ E'] {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (hx : ∀ i, x i ∈ E) :
    (Module.finrank ℚ E : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : E))
      = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h (hx i)⟩ : E')) :=
  (Height.inv_finrank_mul_logHeight_inclusion (K := E) (L := E') h (fun i => (⟨x i, hx i⟩ : E))).symm

private theorem absLogHeight_eq_of_mem {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (E' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E'] (h : ∀ i, x i ∈ E') :
    absLogHeight x = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h i⟩ : E')) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  haveI := finiteDimensional_adjoin_range x
  exact normLogHeight_eq_of_le _ E' hle x (fun i => IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)

private theorem absLogHeight_smul {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    {c : AlgebraicClosure ℚ} (hc : c ≠ 0) : absLogHeight (c • x) = absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (insert c (Set.range x)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun y _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic y).isIntegral
  have hcE : c ∈ E' := IntermediateField.subset_adjoin ℚ _ (Set.mem_insert c _)
  have hx' : ∀ i, x i ∈ E' := fun i =>
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem c ⟨i, rfl⟩)
  have hcx : ∀ i, (c • x) i ∈ E' := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]; exact mul_mem hcE (hx' i)
  rw [absLogHeight_eq_of_mem (c • x) E' hcx, absLogHeight_eq_of_mem x E' hx']
  congr 1
  convert Height.logHeight_smul_eq_logHeight (fun i => (⟨x i, hx' i⟩ : E')) (c := ⟨c, hcE⟩) ?_ using 2
  all_goals first
    | exact fun h0 => hc (by simpa using congrArg Subtype.val h0)
    | (funext i; apply Subtype.ext; simp [Pi.smul_apply, smul_eq_mul])

private theorem absLogHeight_linear_le {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty ι]
    (M : κ → ι → AlgebraicClosure ℚ) (x : ι → AlgebraicClosure ℚ) :
    absLogHeight (fun j => ∑ i, M j i * x i)
      ≤ Real.log (Fintype.card ι) + absLogHeight (fun q : κ × ι => M q.1 q.2) + absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (Set.range x ∪ Set.range (fun q : κ × ι => M q.1 q.2)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  have hxE : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
  have hME : ∀ q : κ × ι, M q.1 q.2 ∈ E' := fun q => IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨q, rfl⟩)
  have hyE : ∀ j, (∑ i, M j i * x i) ∈ E' := fun j => sum_mem fun i _ => mul_mem (hME (j, i)) (hxE i)
  rw [absLogHeight_eq_of_mem _ E' hyE, absLogHeight_eq_of_mem _ E' hME, absLogHeight_eq_of_mem x E' hxE]
  have hd : (0 : ℝ) < Module.finrank ℚ E' := by exact_mod_cast Module.finrank_pos
  have hfun : (fun j => (⟨∑ i, M j i * x i, hyE j⟩ : E'))
      = fun j => ∑ i, (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E')) (j, i) * (⟨x i, hxE i⟩ : E') := by
    funext j
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul]
  have key := Height.logHeight_linearMap_apply_le (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
    (fun i => (⟨x i, hxE i⟩ : E'))
  rw [NumberField.totalWeight_eq_finrank, Nat.card_eq_fintype_card] at key
  rw [hfun]
  have hlog : 0 ≤ Real.log (Fintype.card ι : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  calc (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun j => ∑ i,
          (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E')) (j, i) * (⟨x i, hxE i⟩ : E'))
      ≤ (Module.finrank ℚ E' : ℝ)⁻¹ * ((Module.finrank ℚ E' : ℝ) * Real.log (Fintype.card ι)
          + Height.logHeight (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
          + Height.logHeight (fun i => (⟨x i, hxE i⟩ : E'))) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hd.le)
    _ = Real.log (Fintype.card ι)
          + (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
          + (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hxE i⟩ : E')) := by
        field_simp

private theorem absLogHeight_nonneg {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

private theorem absLogHeight_reindex_le {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι] [Nonempty κ]
    (e : κ → ι) (he : Function.Injective e) :
    ∃ C : ℝ, ∀ y : ι → AlgebraicClosure ℚ, (∀ p, p ∉ Set.range e → y p = 0) →
      |absLogHeight (y ∘ e) - absLogHeight y| ≤ C := by
  classical
  let M : κ → ι → AlgebraicClosure ℚ := fun k p => if p = e k then 1 else 0
  let M' : ι → κ → AlgebraicClosure ℚ := fun p k => if p = e k then 1 else 0
  refine ⟨Real.log (Fintype.card ι) + absLogHeight (fun q : κ × ι => M q.1 q.2)
    + (Real.log (Fintype.card κ) + absLogHeight (fun q : ι × κ => M' q.1 q.2)), fun y hy => ?_⟩
  have h1 : (y ∘ e) = fun k => ∑ p, M k p * y p := by
    funext k
    simp only [Function.comp_apply, M, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (e k) (fun p => y p)]
    simp
  have h2 : y = fun p => ∑ k, M' p k * (y ∘ e) k := by
    funext p
    simp only [Function.comp_apply, M', ite_mul, one_mul, zero_mul]
    by_cases hp : p ∈ Set.range e
    · obtain ⟨k₀, rfl⟩ := hp
      rw [Finset.sum_eq_single k₀]
      · simp
      · intro k _ hk
        rw [if_neg]
        intro h; exact hk (he h.symm)
      · intro h; exact absurd (Finset.mem_univ k₀) h
    · rw [hy p hp]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg]
      intro h; exact hp ⟨k, h.symm⟩
  have hA := absLogHeight_linear_le M y
  have hB := absLogHeight_linear_le M' (y ∘ e)
  rw [← h1] at hA
  rw [← h2] at hB
  have hlι : 0 ≤ Real.log (Fintype.card ι : ℝ) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hlκ : 0 ≤ Real.log (Fintype.card κ : ℝ) := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  have hM := absLogHeight_nonneg (fun q : κ × ι => M q.1 q.2)
  have hM' := absLogHeight_nonneg (fun q : ι × κ => M' q.1 q.2)
  rw [abs_le]
  constructor <;> linarith

end AbsHeight
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end P2MW
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

namespace P2MSC

open AlgebraicCurve ModularCurve P2MW

noncomputable section

section Generic

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

private def chordFun {r : ℕ} (s : Fin r → F) (w₀ : Place (AlgebraicClosure ℚ) F) (p : Fin r × Fin r) : F :=
  evalVec s w₀ p.1 • s p.2 - evalVec s w₀ p.2 • s p.1

private def mulFam {a b : ℕ} (s : Fin a → F) (t : Fin b → F) : Fin (a * b) → F :=
  fun k => s (finProdFinEquiv.symm k).1 * t (finProdFinEquiv.symm k).2

omit [Algebra (AlgebraicClosure ℚ) F] in
private theorem mulFam_ne_zero {a b : ℕ} {s : Fin a → F} {t : Fin b → F} (hs : ∀ i, s i ≠ 0) (ht : ∀ j, t j ≠ 0) :
    ∀ k, mulFam s t k ≠ 0 := fun _ => mul_ne_zero (hs _) (ht _)

private theorem mul_mem_rr_add {A B : Divisor (AlgebraicClosure ℚ) F} {f g : F} (hf : f ∈ riemannRochSpace A)
    (hg : g ∈ riemannRochSpace B) : f * g ∈ riemannRochSpace (A + B) := by
  rw [mem_riemannRochSpace_iff] at hf hg ⊢
  intro w
  rcases eq_or_ne f 0 with rfl | hf0
  · left; rw [zero_mul]
  rcases eq_or_ne g 0 with rfl | hg0
  · left; rw [mul_zero]
  right
  rw [Place.ord_mul _ hf0 hg0, Finsupp.add_apply, neg_add]
  exact add_le_add ((hf w).resolve_left hf0) ((hg w).resolve_left hg0)

private theorem mulFam_mem {a b : ℕ} {s : Fin a → F} {t : Fin b → F}
    {A B : Divisor (AlgebraicClosure ℚ) F} (hs : ∀ i, s i ∈ riemannRochSpace A) (ht : ∀ j, t j ∈ riemannRochSpace B) :
    ∀ k, mulFam s t k ∈ riemannRochSpace (A + B) := fun _ => mul_mem_rr_add (hs _) (ht _)

private theorem mulFam_bpf {a b : ℕ} {s : Fin a → F} {t : Fin b → F} (hs0 : ∀ i, s i ≠ 0) (ht0 : ∀ j, t j ≠ 0)
    {A B : Divisor (AlgebraicClosure ℚ) F}
    (hs : ∀ w : Place (AlgebraicClosure ℚ) F, ∃ i, w.ord (s i) + A w = 0)
    (ht : ∀ w : Place (AlgebraicClosure ℚ) F, ∃ j, w.ord (t j) + B w = 0) :
    ∀ w : Place (AlgebraicClosure ℚ) F, ∃ k, w.ord (mulFam s t k) + (A + B) w = 0 := by
  intro w
  obtain ⟨i, hi⟩ := hs w
  obtain ⟨j, hj⟩ := ht w
  refine ⟨finProdFinEquiv (i, j), ?_⟩
  simp only [mulFam, Equiv.symm_apply_apply]
  rw [Place.ord_mul _ (hs0 i) (ht0 j), Finsupp.add_apply]
  linarith

private theorem chordVec_swap {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    chordVec s w v = -chordVec s v w := by
  funext p
  simp only [chordVec, Pi.neg_apply]
  ring

private theorem absLogHeight_neg {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) :
    absLogHeight (-x) = absLogHeight x := by
  have h : -x = (-1 : AlgebraicClosure ℚ) • x := by funext i; simp
  rw [h, absLogHeight_smul x (by norm_num)]

private theorem pairHt_comm {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    pairHt s v w = pairHt s w v := by
  unfold pairHt
  rw [chordVec_swap s w v, absLogHeight_neg]
  ring

private theorem baseHt_of_ne {r : ℕ} (s : Fin r → F) {o v : Place (AlgebraicClosure ℚ) F} (hv : v ≠ o) :
    baseHt s o v = pairHt s o v := by
  unfold baseHt; rw [if_neg hv, pairHt_comm]

private theorem baseHt_self {r : ℕ} (s : Fin r → F) (o : Place (AlgebraicClosure ℚ) F) : baseHt s o o = 0 := by
  unfold baseHt; rw [if_pos rfl]

private theorem pointHt_nonneg {r : ℕ} (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) : 0 ≤ pointHt s v :=
  absLogHeight_nonneg _

end Generic
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

section BarBeta

variable (N : ℕ) [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]

private theorem embDivisor_apply_of_ne {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hw : w ≠ cuspInftyBar N) :
    embDivisor N w = 0 := by
  classical
  rw [embDivisor, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hw), smul_zero]

private theorem embDivisor_apply_self : embDivisor N (cuspInftyBar N) = embDegree N := by
  classical
  rw [embDivisor, Finsupp.smul_apply, Finsupp.single_apply, if_pos rfl, smul_eq_mul, mul_one]

private theorem degree_embDivisor : (embDivisor N).degree = embDegree N := by
  rw [embDivisor, map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N]; simp

private theorem embDegree_cast : (embDegree N : ℤ) = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 := by
  rw [embDegree]; push_cast; ring

private theorem degree_embDivisor_sub :
    (embDivisor N - Finsupp.single (cuspInftyBar N) 1).degree
      = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
  rw [map_sub, degree_embDivisor, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N, embDegree_cast]; push_cast; ring

variable {N}

private theorem chordFun_mem {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : Fin r × Fin r) :
    chordFun s (cuspInftyBar N) p ∈ riemannRochSpace (embDivisor N - Finsupp.single (cuspInftyBar N) 1) := by
  classical
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hr : 0 < r := pos_of_span_eq N s hs.2 (by rw [degree_embDivisor, embDegree_cast]; omega)
  have ho_rat := isRational_bar N (cuspInftyBar N)
  set piv := pivotIndex s (cuspInftyBar N) hr with hpiv
  have hp : ∀ j, (cuspInftyBar N).ord (s piv) ≤ (cuspInftyBar N).ord (s j) := ord_pivot_le N hr s (cuspInftyBar N)
  have hsmem : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := mem_of_span_eq s hs.2

  have hmemE : chordFun s (cuspInftyBar N) p ∈ riemannRochSpace (embDivisor N) :=
    sub_mem (Submodule.smul_mem _ _ (hsmem p.2)) (Submodule.smul_mem _ _ (hsmem p.1))

  set fi := s p.1 * (s piv)⁻¹
  set fj := s p.2 * (s piv)⁻¹
  have hfi : fi ∈ (cuspInftyBar N).toValuationSubring := ratio_mem N s hs0 (cuspInftyBar N) piv hp p.1
  have hfj : fj ∈ (cuspInftyBar N).toValuationSubring := ratio_mem N s hs0 (cuspInftyBar N) piv hp p.2
  set g := evalVec s (cuspInftyBar N) p.1 • fj - evalVec s (cuspInftyBar N) p.2 • fi with hg
  have hgmem : g ∈ (cuspInftyBar N).toValuationSubring := sub_mem (smul_mem_of_mem (cuspInftyBar N) _ hfj) (smul_mem_of_mem (cuspInftyBar N) _ hfi)
  have hfact : chordFun s (cuspInftyBar N) p = g * s piv := by
    simp only [chordFun, hg, sub_mul, smul_mul_assoc]
    rw [inv_mul_cancel_right₀ (hs0 piv), inv_mul_cancel_right₀ (hs0 piv)]
  have hgval : (cuspInftyBar N).evalAt g = 0 := by
    rw [hg, evalAt_sub_of_mem (cuspInftyBar N) ho_rat (smul_mem_of_mem (cuspInftyBar N) _ hfj) (smul_mem_of_mem (cuspInftyBar N) _ hfi),
      evalAt_smul_of_mem (cuspInftyBar N) ho_rat _ hfj, evalAt_smul_of_mem (cuspInftyBar N) ho_rat _ hfi,
      evalVec_apply N hr s (cuspInftyBar N) p.1, evalVec_apply N hr s (cuspInftyBar N) p.2]
    ring
  rw [mem_riemannRochSpace_iff]
  intro w
  rcases eq_or_ne (chordFun s (cuspInftyBar N) p) 0 with h0 | h0
  · exact Or.inl h0
  right
  by_cases hw : w = (cuspInftyBar N)
  · subst hw
    have hg0 : g ≠ 0 := by intro h; apply h0; rw [hfact, h, zero_mul]
    have hordg : 0 < (cuspInftyBar N).ord g := ord_pos_of_evalAt_eq_zero _ ho_rat hg0 hgmem hgval
    have hordpiv : -embDivisor N (cuspInftyBar N) ≤ (cuspInftyBar N).ord (s piv) :=
      ((mem_riemannRochSpace_iff.mp (hsmem piv)) _).resolve_left (hs0 piv)
    rw [hfact, Place.ord_mul _ hg0 (hs0 piv), Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl]
    omega
  · have h1 := ((mem_riemannRochSpace_iff.mp hmemE) w).resolve_left h0
    rw [Finsupp.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hw), sub_zero]
    exact h1

private theorem span_chordFun_eq {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    Submodule.span (AlgebraicClosure ℚ) (Set.range (chordFun s (cuspInftyBar N)))
      = riemannRochSpace (embDivisor N - Finsupp.single (cuspInftyBar N) 1) := by
  classical
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hdegE : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ (embDivisor N).degree := by
    rw [degree_embDivisor, embDegree_cast]; omega
  have hr : 0 < r := pos_of_span_eq N s hs.2 hdegE
  have ho_rat := isRational_bar N (cuspInftyBar N)
  set piv := pivotIndex s (cuspInftyBar N) hr with hpiv
  have hp : ∀ j, (cuspInftyBar N).ord (s piv) ≤ (cuspInftyBar N).ord (s j) := ord_pivot_le N hr s (cuspInftyBar N)
  have hsmem : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := mem_of_span_eq s hs.2
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro _ ⟨p, rfl⟩; exact chordFun_mem s hs p)
  · intro f hf
    have hfE : f ∈ riemannRochSpace (embDivisor N) := by
      refine lSpace_mono (Finsupp.le_def.mpr fun v => ?_) hf
      rw [Finsupp.sub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    have hspan : f ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := hs.2 ▸ hfE
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (AlgebraicClosure ℚ)).mp hspan

    have hratmem : ∀ i, s i * (s piv)⁻¹ ∈ (cuspInftyBar N).toValuationSubring := fun i => ratio_mem N s hs0 (cuspInftyBar N) piv hp i
    have hordpiv : (cuspInftyBar N).ord (s piv) = -(embDivisor N) (cuspInftyBar N) :=
      ord_eq_neg_of_forall_le s hs0 hsmem (cuspInftyBar N) (bpf_of_span_eq N s hs.2 hdegE (cuspInftyBar N)) piv hp
    have hval : ∑ j, a j * evalVec s (cuspInftyBar N) j = 0 := by
      have h1 : f * (s piv)⁻¹ = ∑ j, a j • (s j * (s piv)⁻¹) := by
        rw [← ha, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc]
      have h2 : (cuspInftyBar N).evalAt (f * (s piv)⁻¹) = ∑ j, a j * evalVec s (cuspInftyBar N) j := by
        rw [h1, evalAt_sum_smul_of_mem _ (cuspInftyBar N) ho_rat a hratmem]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [evalVec_apply N hr s (cuspInftyBar N) j]
      rw [← h2]
      rcases eq_or_ne f 0 with hf0 | hf0
      · rw [hf0, zero_mul, evalAt_zero]
      · have hordf := ((mem_riemannRochSpace_iff.mp hf) (cuspInftyBar N)).resolve_left hf0
        rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl] at hordf
        have hne : f * (s piv)⁻¹ ≠ 0 := mul_ne_zero hf0 (inv_ne_zero (hs0 piv))
        have hord : 0 < (cuspInftyBar N).ord (f * (s piv)⁻¹) := by
          rw [(cuspInftyBar N).ord_mul hf0 (inv_ne_zero (hs0 piv)), (cuspInftyBar N).ord_inv, hordpiv]; omega
        exact evalAt_eq_zero_of_ord_pos (cuspInftyBar N) ho_rat ((cuspInftyBar N).mem_toValuationSubring_of_ord_nonneg_alt hne hord.le) hord
    have hepiv : evalVec s (cuspInftyBar N) piv = 1 := by
      rw [evalVec_apply N hr s (cuspInftyBar N) piv, mul_inv_cancel₀ (hs0 piv), Place.evalAt_one]
    have hf_eq : f = ∑ j, a j • chordFun s (cuspInftyBar N) (piv, j) := by
      have : ∑ j, a j • chordFun s (cuspInftyBar N) (piv, j) = ∑ j, a j • s j - (∑ j, a j * evalVec s (cuspInftyBar N) j) • s piv := by
        simp only [chordFun, hepiv, one_smul, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, smul_smul]
      have hz : (∑ j, a j * evalVec s (cuspInftyBar N) j) • s piv = 0 := by rw [hval]; exact zero_smul (AlgebraicClosure ℚ) (s piv)
      rw [this, hz, sub_zero, ha]
    rw [hf_eq]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(piv, j), rfl⟩)

private theorem baseHt_estimate {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ (c₃ : ℕ) (s₃ : Fin c₃ → modularFunctionFieldBar N), (∀ i, s₃ i ≠ 0) ∧
      Submodule.span (AlgebraicClosure ℚ) (Set.range s₃)
        = riemannRochSpace ((embDivisor N - Finsupp.single (cuspInftyBar N) 1) + embDivisor N) ∧
      ∃ C : ℝ, ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v ≠ cuspInftyBar N →
        |baseHt s (cuspInftyBar N) v - (2 * pointHt s v - pointHt s₃ v)| ≤ C := by
  classical
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hdegE : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ (embDivisor N).degree := by
    rw [degree_embDivisor, embDegree_cast]; omega
  have hr : 0 < r := pos_of_span_eq N s hs.2 hdegE
  haveI : Nonempty (Fin r × Fin r) := ⟨(⟨0, hr⟩, ⟨0, hr⟩)⟩
  set D₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := embDivisor N - Finsupp.single (cuspInftyBar N) 1 with hD₁
  have hD₁deg : D₁.degree = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) :=
    degree_embDivisor_sub N
  have hD₁zero : ∀ v, v ≠ (cuspInftyBar N) → D₁ v = 0 := by
    intro v hv
    rw [hD₁, Finsupp.sub_apply, embDivisor_apply_of_ne N hv, Finsupp.single_apply, if_neg (Ne.symm hv), sub_zero]

  let S : Finset (Fin r × Fin r) := Finset.univ.filter (fun p => chordFun s (cuspInftyBar N) p ≠ 0)
  let e : Fin S.card → Fin r × Fin r := fun k => ((S.equivFin.symm k : S) : Fin r × Fin r)
  have he_mem : ∀ k, e k ∈ S := fun k => (S.equivFin.symm k).2
  have he_inj : Function.Injective e := fun k k' h => S.equivFin.symm.injective (Subtype.ext h)
  have hce : ∀ k, chordFun s (cuspInftyBar N) (e k) ≠ 0 := fun k => (Finset.mem_filter.mp (he_mem k)).2
  have hS_of : ∀ p, chordFun s (cuspInftyBar N) p ≠ 0 → p ∈ Set.range e := fun p hp =>
    ⟨S.equivFin ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩, by simp [e]⟩
  let c' : Fin S.card → modularFunctionFieldBar N := fun k => chordFun s (cuspInftyBar N) (e k)
  have hc'0 : ∀ k, c' k ≠ 0 := hce
  have hc'span : Submodule.span (AlgebraicClosure ℚ) (Set.range c') = riemannRochSpace D₁ := by
    rw [hD₁, ← span_chordFun_eq s hs]
    apply le_antisymm
    · exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨e k, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨p, rfl⟩
      rcases eq_or_ne (chordFun s (cuspInftyBar N) p) 0 with h0 | h0
      · rw [h0]; exact zero_mem _
      · obtain ⟨k, hk⟩ := hS_of p h0
        exact Submodule.subset_span ⟨k, by simp only [c', hk]⟩
  have hc'mem : ∀ k, c' k ∈ riemannRochSpace D₁ := mem_of_span_eq c' hc'span
  have hc'bpf := bpf_of_span_eq N c' hc'span (by rw [hD₁deg])
  have hb : 0 < S.card := by
    obtain ⟨k, -⟩ := hc'bpf (cuspInftyBar N)
    exact Fin.pos k
  haveI : Nonempty (Fin S.card) := ⟨⟨0, hb⟩⟩

  have hm0 : ∀ k, mulFam c' s k ≠ 0 := mulFam_ne_zero hc'0 hs0
  have hmmem : ∀ k, mulFam c' s k ∈ riemannRochSpace (D₁ + embDivisor N) :=
    mulFam_mem hc'mem (mem_of_span_eq s hs.2)
  have hmbpf := mulFam_bpf hc'0 hs0 hc'bpf (bpf_of_span_eq N s hs.2 hdegE)
  obtain ⟨c₃, s₃, hs₃0, hs₃span⟩ := exists_family_span_eq N (D₁ + embDivisor N)
  have hdeg3 : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 ≤ (D₁ + embDivisor N).degree := by
    rw [map_add, hD₁deg, degree_embDivisor, embDegree_cast]; omega
  obtain ⟨C₁, hC₁⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_of_forall_exists_ord_add_eq_zero N
    s₃ (mulFam c' s) hs₃0 hm0 (D₁ + embDivisor N) hdeg3 hs₃span hmmem hmbpf
  obtain ⟨C₀, hC₀⟩ := absLogHeight_reindex_le e he_inj
  refine ⟨c₃, s₃, hs₃0, hs₃span, |pointHt s (cuspInftyBar N)| + C₀ + C₁, fun v hv => ?_⟩
  have hv_rat := isRational_bar N v

  have hVH : absLogHeight (chordVec s (cuspInftyBar N) v) = absLogHeight (fun p : Fin r × Fin r => v.evalAt (chordFun s (cuspInftyBar N) p)) :=
    ModularCurve.JZero.absLogHeight_chordVec_eq_evalAt_of_ne N s hs (cuspInftyBar N) v hv
  set y : Fin r × Fin r → AlgebraicClosure ℚ := fun p => v.evalAt (chordFun s (cuspInftyBar N) p) with hy
  have hy0 : ∀ p, p ∉ Set.range e → y p = 0 := by
    intro p hp
    have h0 : chordFun s (cuspInftyBar N) p = 0 := by
      by_contra hne; exact hp (hS_of p hne)
    show v.evalAt (chordFun s (cuspInftyBar N) p) = 0
    rw [h0, evalAt_zero]

  set piv' := pivotIndex c' v hb with hpiv'
  have hp' : ∀ k, v.ord (c' piv') ≤ v.ord (c' k) := ord_pivot_le N hb c' v
  have hordpiv' : v.ord (c' piv') = 0 := by
    rw [ord_eq_neg_of_forall_le c' hc'0 hc'mem v (hc'bpf v) piv' hp', hD₁zero v hv, neg_zero]
  have hc'O : ∀ k, c' k ∈ v.toValuationSubring := fun k =>
    v.mem_toValuationSubring_of_ord_nonneg_alt (hc'0 k) (by
      have := ((mem_riemannRochSpace_iff.mp (hc'mem k)) v).resolve_left (hc'0 k)
      rw [hD₁zero v hv, neg_zero] at this; exact this)
  set μ : AlgebraicClosure ℚ := v.evalAt (c' piv')⁻¹ with hμ
  have hμ1 : v.evalAt (c' piv') * μ = 1 := evalAt_mul_evalAt_inv v hv_rat (hc'0 piv') hordpiv'
  have hμ0 : μ ≠ 0 := fun h => by rw [h, mul_zero] at hμ1; exact zero_ne_one hμ1
  have hev : evalVec c' v = μ • (y ∘ e) := by
    funext k
    rw [evalVec_apply N hb c' v k, ← hpiv', Pi.smul_apply, Function.comp_apply, smul_eq_mul,
      v.evalAt_mul_of_mem hv_rat (hc'O k) (inv_mem_of_ord_eq_zero v (hc'0 piv') hordpiv'), ← hμ]
    show v.evalAt (chordFun s (cuspInftyBar N) (e k)) * μ = μ * v.evalAt (chordFun s (cuspInftyBar N) (e k))
    ring
  have hpt : pointHt c' v = absLogHeight (y ∘ e) := by
    show absLogHeight (evalVec c' v) = _
    rw [hev, absLogHeight_smul _ hμ0]

  have hseg : pointHt (mulFam c' s) v = pointHt c' v + pointHt s v :=
    pointHt_mul_eq_add hb hr c' s hc'0 hs0 v hv_rat

  have hβ : baseHt s (cuspInftyBar N) v = pointHt s (cuspInftyBar N) + pointHt s v - absLogHeight (chordVec s (cuspInftyBar N) v) := by
    rw [baseHt_of_ne s hv]; rfl
  have h0 := hC₀ y hy0
  have h1 := hC₁ v
  rw [hβ, hVH]
  rw [hseg, hpt] at h1
  rw [abs_le] at h0 h1 ⊢
  constructor <;> linarith [le_abs_self (pointHt s (cuspInftyBar N)), neg_abs_le (pointHt s (cuspInftyBar N))]

end BarBeta
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end P2MSC
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

namespace P2MSC

open AlgebraicCurve ModularCurve P2MW

noncomputable section

section Multiples

variable (N : ℕ) [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]

private theorem exists_family_nsmul {a : ℕ} (sD : Fin a → modularFunctionFieldBar N) (hsD0 : ∀ i, sD i ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 ≤ D.degree)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range sD) = riemannRochSpace D) (m : ℕ) (hm : 1 ≤ m) :
    ∃ (c : ℕ) (Fm : Fin c → modularFunctionFieldBar N), (∀ i, Fm i ≠ 0) ∧
      Submodule.span (AlgebraicClosure ℚ) (Set.range Fm) = riemannRochSpace (m • D) ∧
      ∃ C : ℝ, ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), |pointHt Fm v - m * pointHt sD v| ≤ C := by
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨a, sD, hsD0, by rw [one_smul]; exact hsD, 0, fun v => ?_⟩
    simp
  | succ m hm ih =>
    obtain ⟨c, Fm, hFm0, hFmspan, C, hC⟩ := ih
    obtain ⟨c', F', hF'0, hF'span⟩ := exists_family_span_eq N ((m + 1) • D)
    have hdegm : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 ≤ (m • D).degree := by
      rw [map_nsmul, nsmul_eq_mul]
      have h0 : 0 ≤ D.degree := by linarith
      have : (1 : ℤ) * D.degree ≤ (m : ℤ) * D.degree := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) h0
      linarith
    have hF'span' : Submodule.span (AlgebraicClosure ℚ) (Set.range F') = riemannRochSpace (m • D + D) := by
      rw [hF'span, succ_nsmul]
    obtain ⟨C', hC'⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_add_pointHt_le N Fm sD F' hFm0 hsD0 hF'0 (m • D) D
      hdegm hD hFmspan hsD hF'span'
    refine ⟨c', F', hF'0, hF'span, C + C', fun v => ?_⟩
    have h1 := hC v
    have h2 := hC' v
    rw [abs_le] at h1 h2 ⊢
    push_cast
    constructor <;> linarith

end Multiples
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end P2MSC
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

namespace P2MSC

open AlgebraicCurve ModularCurve P2MW

noncomputable section

section StepOne

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

private theorem sum_erase_mul (B : Divisor (AlgebraicClosure ℚ) F) (v : Place (AlgebraicClosure ℚ) F)
    (g : Place (AlgebraicClosure ℚ) F → ℝ) :
    ((B.erase v).sum fun w m => (m : ℝ) * g w) = (B.sum fun w m => (m : ℝ) * g w) - (B v : ℝ) * g v := by
  have h := Finsupp.add_sum_erase' B v (fun w m => (m : ℝ) * g w) (fun w => by simp)
  linarith

private theorem sum_add_single_mul (B : Divisor (AlgebraicClosure ℚ) F) (o : Place (AlgebraicClosure ℚ) F) (d : ℤ)
    (g : Place (AlgebraicClosure ℚ) F → ℝ) :
    ((B + d • Finsupp.single o 1).sum fun w m => (m : ℝ) * g w)
      = (B.sum fun w m => (m : ℝ) * g w) + (d : ℝ) * g o := by
  rw [Finsupp.sum_add_index' (fun w => by simp) (fun w m₁ m₂ => by push_cast; ring)]
  congr 1
  rw [Finsupp.sum_smul_index' (fun w => by simp), Finsupp.sum_single_index (by simp)]
  simp

private theorem selfFunctional_normalForm (s : Fin r → F) (γ : ℝ) (d : ℤ)
    (o v : Place (AlgebraicClosure ℚ) F) (hvo : v ≠ o) (B : Divisor (AlgebraicClosure ℚ) F) :
    ((B.erase v).sum fun w m => (m : ℝ) * (baseHt s o w - pairHt s v w))
        + (2 * γ - 1) * (B v : ℝ) * baseHt s o v
      = (B.sum fun w m => (m : ℝ) * baseHt s o w)
        + ((d : ℝ) + (2 * γ - 2) * (B v : ℝ)) * baseHt s o v
        - ((B.erase v + d • Finsupp.single o 1).sum fun w m => (m : ℝ) * pairHt s v w) := by
  have hβv : baseHt s o v = pairHt s v o := by
    unfold baseHt; rw [if_neg hvo]
  rw [sum_erase_mul B v (fun w => baseHt s o w - pairHt s v w), sum_add_single_mul, sum_erase_mul B v]
  have hsplit : (B.sum fun w m => (m : ℝ) * (baseHt s o w - pairHt s v w))
      = (B.sum fun w m => (m : ℝ) * baseHt s o w) - (B.sum fun w m => (m : ℝ) * pairHt s v w) := by
    simp only [Finsupp.sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [hsplit, ← hβv]
  ring

private theorem sum_baseHt_eq_sum_erase_pairHt (s : Fin r → F) (o : Place (AlgebraicClosure ℚ) F)
    (B : Divisor (AlgebraicClosure ℚ) F) :
    (B.sum fun w m => (m : ℝ) * baseHt s o w) = ((B.erase o).sum fun w m => (m : ℝ) * pairHt s o w) := by
  classical
  rw [sum_erase_mul B o, ← sub_zero (B.sum fun w m => (m : ℝ) * baseHt s o w)]
  have h0 : (B o : ℝ) * pairHt s o o - (B o : ℝ) * pairHt s o o = 0 := sub_self _
  have key : (B.sum fun w m => (m : ℝ) * baseHt s o w)
      = (B.sum fun w m => (m : ℝ) * pairHt s o w) - (B o : ℝ) * pairHt s o o := by
    have e1 := sum_erase_mul B o (fun w => baseHt s o w)
    have e2 := sum_erase_mul B o (fun w => pairHt s o w)
    have e3 : ((B.erase o).sum fun w m => (m : ℝ) * baseHt s o w)
        = ((B.erase o).sum fun w m => (m : ℝ) * pairHt s o w) := by
      simp only [Finsupp.sum]
      refine Finset.sum_congr rfl fun w hw => ?_
      have hwo : w ≠ o := by
        rw [Finsupp.support_erase] at hw
        exact Finset.ne_of_mem_erase hw
      rw [baseHt_of_ne s hwo]
    rw [baseHt_self, mul_zero, sub_zero] at e1
    linarith
  linarith

end StepOne
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

section BarMain

variable (N : ℕ) [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]

omit [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)] in
private theorem degree_eq_sum (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    D.degree = ∑ w ∈ D.support, D w := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [deg_eq_one_modularFunctionFieldBar N w]

omit [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)] in
private theorem erase_add_embDivisor_of_ne (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hv : v ≠ cuspInftyBar N) :
    (B + embDivisor N).erase v = B.erase v + (embDegree N : ℤ) • Finsupp.single (cuspInftyBar N) 1 := by
  rw [Finsupp.erase_add, embDivisor, Finsupp.smul_single, Finsupp.erase_single_ne hv]

omit [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)] in
private theorem erase_add_embDivisor_self (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (B + embDivisor N).erase (cuspInftyBar N) = B.erase (cuspInftyBar N) := by
  rw [Finsupp.erase_add, embDivisor, Finsupp.smul_single, Finsupp.erase_single, add_zero]

private theorem mass_le (u : modularFunctionFieldBar N) (hu : u ∈ riemannRochSpace (embDivisor N)) (hu0 : u ≠ 0)
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u) (hBdeg : B.degree = 0) :
    (B.sum fun _ m => |(m : ℝ)|) ≤ 2 * (embDegree N : ℝ) := by
  classical
  set o := cuspInftyBar N
  have hnn : ∀ w, 0 ≤ B w + embDivisor N w := by
    intro w
    rw [hB w]
    have := ((mem_riemannRochSpace_iff.mp hu) w).resolve_left hu0
    linarith
  have hE0 : ∀ w, 0 ≤ embDivisor N w := by
    intro w
    by_cases hw : w = o
    · subst hw; rw [embDivisor_apply_self]; exact_mod_cast Nat.zero_le _
    · rw [embDivisor_apply_of_ne N hw]
  have habs : ∀ w, |(B w : ℝ)| ≤ (B w : ℝ) + 2 * (embDivisor N w : ℝ) := by
    intro w
    have h1 : (0 : ℝ) ≤ (B w : ℝ) + (embDivisor N w : ℝ) := by exact_mod_cast hnn w
    have h2 : (0 : ℝ) ≤ (embDivisor N w : ℝ) := by exact_mod_cast hE0 w
    rw [abs_le]; constructor <;> linarith
  have hdeg : ∑ w ∈ B.support, (B w : ℝ) = 0 := by
    have := degree_eq_sum N B
    rw [hBdeg] at this
    exact_mod_cast this.symm
  have hEsum : ∑ w ∈ B.support, (embDivisor N w : ℝ) ≤ embDegree N := by
    have : ∀ w ∈ B.support, (embDivisor N w : ℝ) = if w = o then (embDegree N : ℝ) else 0 := by
      intro w _
      by_cases hw : w = o
      · subst hw; rw [if_pos rfl, embDivisor_apply_self]; push_cast; rfl
      · rw [if_neg hw, embDivisor_apply_of_ne N hw]; push_cast; rfl
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact_mod_cast Nat.zero_le _
  calc (B.sum fun _ m => |(m : ℝ)|) = ∑ w ∈ B.support, |(B w : ℝ)| := rfl
    _ ≤ ∑ w ∈ B.support, ((B w : ℝ) + 2 * (embDivisor N w : ℝ)) := Finset.sum_le_sum fun w _ => habs w
    _ = ∑ w ∈ B.support, (B w : ℝ) + 2 * ∑ w ∈ B.support, (embDivisor N w : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (embDegree N : ℝ) := by rw [hdeg]; linarith

private theorem exists_chordFunction {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hv : v ≠ cuspInftyBar N) :
    ∃ (u : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      u ≠ 0 ∧ u ∈ riemannRochSpace (embDivisor N) ∧ v.ord u = 1 ∧ (∀ w, B w = w.ord u) ∧ B.degree = 0 ∧
      B v = 1 ∧ (B.sum fun _ m => |(m : ℝ)|) ≤ 2 * (embDegree N : ℝ) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  set o := cuspInftyBar N
  have hdeg1 : (embDivisor N - Finsupp.single v 1).degree = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
    rw [map_sub, degree_embDivisor, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar N, embDegree_cast]; ring
  obtain ⟨u, hu, hu'⟩ := exists_mem_notMem_bar N (embDivisor N - Finsupp.single v 1) (by rw [hdeg1]) v
  have hu0 : u ≠ 0 := ne_zero_of_notMem hu'
  have hord := ord_eq_of_mem_notMem v hu hu'
  rw [Finsupp.sub_apply, Finsupp.single_apply, if_pos rfl, embDivisor_apply_of_ne N hv] at hord
  have hordv : v.ord u = 1 := by omega
  have huE : u ∈ riemannRochSpace (embDivisor N) := by
    refine lSpace_mono (Finsupp.le_def.mpr fun w => ?_) hu
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  obtain ⟨B, hB, hBdeg⟩ := hCO.toHasPrincipalDivisors.exists_divisor u hu0
  refine ⟨u, B, hu0, huE, hordv, hB, hBdeg, by rw [hB, hordv], mass_le N u huE hu0 B hB hBdeg⟩

private theorem exists_function_at_cusp {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ (g : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      (∀ w, B w = w.ord g) ∧ 1 ≤ B (cuspInftyBar N) ∧ (B.sum fun _ m => |(m : ℝ)|) ≤ 2 * (embDegree N : ℝ) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  set o := cuspInftyBar N
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hdegE : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) ≤ (embDivisor N).degree := by
    rw [degree_embDivisor, embDegree_cast]; omega
  obtain ⟨i, hi⟩ := bpf_of_span_eq N s hs.2 hdegE o
  rw [embDivisor_apply_self] at hi
  obtain ⟨B₀, hB₀, hB₀deg⟩ := hCO.toHasPrincipalDivisors.exists_divisor (s i) (hs0 i)
  refine ⟨(s i)⁻¹, -B₀, fun w => by rw [Finsupp.neg_apply, hB₀ w, Place.ord_inv], ?_, ?_⟩
  · rw [Finsupp.neg_apply, hB₀ o]
    have h1 : (1 : ℤ) ≤ embDegree N := by rw [embDegree_cast]; omega
    omega
  · have := mass_le N (s i) (mem_of_span_eq s hs.2 i) (hs0 i) B₀ hB₀ hB₀deg
    rw [Finsupp.sum_neg_index (fun _ => by simp)]
    simpa [abs_neg] using this

end BarMain
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end P2MSC
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

namespace P2MSC

open AlgebraicCurve ModularCurve P2MW

noncomputable section

section BarMain2

variable (N : ℕ) [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]

private theorem tangent_at_E {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (hg : 1 ≤ genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ (c₄ : ℕ) (w₄ : Fin c₄ → modularFunctionFieldBar N) (K₀ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      (∀ i, w₄ i ≠ 0) ∧
      Submodule.span (AlgebraicClosure ℚ) (Set.range w₄) = riemannRochSpace (embDivisor N + K₀) ∧
      K₀.degree = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 2 ∧
      ∃ C : ℝ, ∀ (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N),
        v.ord t = 1 →
        |absLogHeight (fun p : Fin r × Fin r =>
            regVal s v t 1 1 (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1))
          - (pointHt s v + pointHt w₄ v)| ≤ C := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI hEFT : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    essFiniteType_modularFunctionFieldBar N
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  obtain ⟨x, hxT, hxfd, hxsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)
  haveI := hxfd
  haveI := hxsep
  have hx : KaehlerDifferential.D (AlgebraicClosure ℚ) (modularFunctionFieldBar N) x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental (AlgebraicClosure ℚ) x hxT
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hdegK : (canonicalDivisorOf hx).degree = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 2 := by
    rw [degree_canonicalDivisorOf_modularFunctionFieldBar N hx, genus_eq_genusFF_modularFunctionFieldBar N]
  have hE : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 ≤ (embDivisor N).degree := by
    rw [degree_embDivisor, embDegree_cast]
  obtain ⟨c₄, w₄, hw₄0, hw₄span⟩ := exists_family_span_eq N (embDivisor N + canonicalDivisorOf hx)
  obtain ⟨C, hC⟩ := ModularCurve.JZero.exists_abs_absLogHeight_regVal_sub_pointHt_add_pointHt_le N s w₄ hs0 hw₄0 hg
    (embDivisor N) hE hs.2 hx hw₄span
  exact ⟨c₄, w₄, canonicalDivisorOf hx, hw₄0, hw₄span, hdegK, C, hC⟩

omit [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)] in

private theorem apply_le_degree_of_nonneg (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ w, 0 ≤ D w)
    (w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : D w₀ ≤ D.degree := by
  classical
  rw [degree_eq_sum N D]
  by_cases h : w₀ ∈ D.support
  · rw [← Finset.add_sum_erase _ _ h]
    have : 0 ≤ ∑ w ∈ D.support.erase w₀, D w := Finset.sum_nonneg fun w _ => hD w
    linarith
  · rw [Finsupp.notMem_support_iff.mp h]
    exact Finset.sum_nonneg fun w _ => hD w

private theorem ledger_k1 (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ CL : ℝ, ∀ (u : modularFunctionFieldBar N), u ≠ 0 → u ∈ riemannRochSpace (embDivisor N) →
      ∀ (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), (∀ w, B w = w.ord u) → B.degree = 0 →
      ∀ (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), v ≠ cuspInftyBar N →
      (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) ∈ v.toValuationSubring → v.ord u = 1 →
      |(((B + embDivisor N).erase v).sum fun w n => (n : ℝ) * pairHt s v w)
          - (((B + embDivisor N).erase (cuspInftyBar N)).sum fun w n => (n : ℝ) * pairHt s (cuspInftyBar N) w)
          - (-pointHt s v + absLogHeight (fun p : Fin r × Fin r =>
              regVal s v u 1 1 (evalVec s v p.1 • s p.2 - evalVec s v p.2 • s p.1)))| ≤ CL := by
  classical
  obtain ⟨t', ht'⟩ := exists_ord_eq_one (cuspInftyBar N)
  obtain ⟨c₀, C₀, hL⟩ := ModularCurve.JZero.sum_pairHt_twoLine_ledger_of_nonCuspidal_of_prime_of_five_le N hN hN5 s hs
  set ho : ℝ := absLogHeight (fun p : Fin r × Fin r =>
    regVal s (cuspInftyBar N) t' 1 1 (evalVec s (cuspInftyBar N) p.1 • s p.2 - evalVec s (cuspInftyBar N) p.2 • s p.1)) with hho
  set d : ℝ := (embDegree N : ℝ) with hd
  refine ⟨c₀ * 1 + C₀ + ((1 + 2 * d) * pointHt s (cuspInftyBar N) + d * ho), fun u hu0 huE B hB hBdeg v hv hjv hordv => ?_⟩
  set Bp : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := B + embDivisor N with hBp
  have hBp' : ∀ w, Bp w = w.ord u + (((1 : ℕ) : ℤ) • embDivisor N) w := by
    intro w; rw [hBp, Finsupp.add_apply, hB w, Nat.cast_one, one_smul]
  have huE' : u ∈ riemannRochSpace (((1 : ℕ) : ℤ) • embDivisor N) := by rwa [Nat.cast_one, one_smul]
  have hBpv : Bp v = 1 := by rw [hBp, Finsupp.add_apply, hB v, hordv, embDivisor_apply_of_ne N hv, add_zero]
  have hnn : ∀ w, 0 ≤ Bp w := by
    intro w
    rw [hBp, Finsupp.add_apply, hB w]
    have := ((mem_riemannRochSpace_iff.mp huE) w).resolve_left hu0
    linarith
  have hBpdeg : Bp.degree = embDegree N := by rw [hBp, map_add, hBdeg, degree_embDivisor, zero_add]
  have hBo0 : (0 : ℝ) ≤ (Bp (cuspInftyBar N) : ℝ) := by exact_mod_cast hnn (cuspInftyBar N)
  have hBo1 : (Bp (cuspInftyBar N) : ℝ) ≤ d := by
    have := apply_le_degree_of_nonneg N Bp hnn (cuspInftyBar N)
    rw [hBpdeg] at this
    rw [hd]; exact_mod_cast this
  have key := hL 1 u hu0 huE' Bp hBp' v (Or.inr hjv) u t' (fun _ => hordv) (fun _ => ht')
  rw [hBpv] at key
  have hpo := pointHt_nonneg s (cuspInftyBar N)
  have hho0 : 0 ≤ ho := absLogHeight_nonneg _

  have hcusp : |((1 : ℝ) - 2 * (Bp (cuspInftyBar N) : ℝ)) * pointHt s (cuspInftyBar N) + (Bp (cuspInftyBar N) : ℝ) * ho|
      ≤ (1 + 2 * d) * pointHt s (cuspInftyBar N) + d * ho := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_le] at key hcusp ⊢
  push_cast at key ⊢
  constructor <;> linarith [key.1, key.2, hcusp.1, hcusp.2]

end BarMain2
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end P2MSC
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

namespace P2MSC

open AlgebraicCurve ModularCurve P2MW

noncomputable section

section BarMain3

variable (N : ℕ) [NeZero N] [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)]

local notation "gN" => (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N))

omit [HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)] in
private theorem apply_add_apply_le_degree_of_nonneg (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : ∀ w, 0 ≤ D w) {v w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hvw : v ≠ w) :
    D v + D w ≤ D.degree := by
  classical
  rw [degree_eq_sum N D]
  have h1 : ∑ x ∈ D.support, D x = ∑ x ∈ insert v (insert w D.support), D x := by
    apply Finset.sum_subset
    · intro x hx
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
    · intro x _ hx
      exact Finsupp.notMem_support_iff.mp hx
  have h2 : D v + D w = ∑ x ∈ ({v, w} : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))), D x := by
    rw [Finset.sum_pair hvw]
  rw [h1, h2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro x _ _
    exact hD x

private theorem functional_cusp {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (γ : ℝ)
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ((B.erase (cuspInftyBar N)).sum fun w m => (m : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s (cuspInftyBar N) w))
        + (2 * γ - 1) * (B (cuspInftyBar N) : ℝ) * baseHt s (cuspInftyBar N) (cuspInftyBar N) = 0 := by
  classical
  rw [baseHt_self, mul_zero, add_zero]
  simp only [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w hw
  have hwo : w ≠ cuspInftyBar N := by
    rw [Finsupp.support_erase] at hw
    exact Finset.ne_of_mem_erase hw
  rw [baseHt_of_ne s hwo, sub_self, mul_zero]

private theorem selfChord_main (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        ∃ (g : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
          (∀ w, B w = w.ord g) ∧ 1 ≤ B v ∧ (B.sum fun _ m => |(m : ℝ)|) ≤ M ∧
          |((B.erase v).sum fun w m => (m : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w))
              + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 1)
                * (B v : ℝ) * baseHt s (cuspInftyBar N) v|
            ≤ ε * pointHt s v + C := by
  classical
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hdegE : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) + 1 ≤ (embDivisor N).degree := by
    rw [degree_embDivisor, embDegree_cast]
  have hdR : ((embDegree N : ℤ) : ℝ) = 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) + 1 := by
    rw [embDegree_cast]; push_cast; ring
  obtain ⟨c₃, s₃, hs₃0, hs₃span, Cβ, hCβ⟩ := baseHt_estimate (N := N) s hs
  obtain ⟨CL, hCL⟩ := ledger_k1 N hN hN5 s hs
  obtain ⟨ginf, Binf, hBinf, hBinf1, hBinfmass⟩ := exists_function_at_cusp N s hs
  refine ⟨2 * (embDegree N : ℝ), fun ε hε => ?_⟩
  by_cases hγ : 1 ≤ genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
  ·
    have hγR : (1 : ℝ) ≤ (gN : ℝ) := by exact_mod_cast hγ
    have hγZ : (1 : ℤ) ≤ (gN : ℤ) := by exact_mod_cast hγ
    obtain ⟨c₄, w₄, K₀, hw₄0, hw₄span, hK₀deg, CT, hCT⟩ := tangent_at_E N s hs hγ
    obtain ⟨c₁, F₁, hF₁0, hF₁span, C₁, hC₁⟩ :=
      exists_family_nsmul N s hs0 (embDivisor N) hdegE hs.2 (8 * gN - 2) (by omega)
    set D₃ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      (embDivisor N - Finsupp.single (cuspInftyBar N) 1) + embDivisor N with hD₃
    have hD₃deg : D₃.degree = 4 * (gN : ℤ) + 1 := by
      rw [hD₃, map_add, degree_embDivisor_sub, degree_embDivisor, embDegree_cast]; ring
    have hdeg3 : 2 * (gN : ℤ) + 1 ≤ D₃.degree := by rw [hD₃deg]; omega
    obtain ⟨cG, G, hG0, hGspan, CG, hCG⟩ := exists_family_nsmul N s₃ hs₃0 D₃ hdeg3 hs₃span (4 * gN - 1) (by omega)
    set A₁ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := (8 * gN - 2) • embDivisor N with hA₁
    set A₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      (4 * gN - 1) • D₃ + (embDivisor N + K₀) with hA₂
    obtain ⟨c₂, F₂, hF₂0, hF₂span⟩ := exists_family_span_eq N A₂
    have h41 : ((4 * gN - 1 : ℕ) : ℤ) = 4 * (gN : ℤ) - 1 := by omega
    have h82 : ((8 * gN - 2 : ℕ) : ℤ) = 8 * (gN : ℤ) - 2 := by omega
    have hdegA : 2 * (gN : ℤ) + 1 ≤ ((4 * gN - 1) • D₃).degree := by
      rw [map_nsmul, nsmul_eq_mul, hD₃deg, h41]; nlinarith [hγZ]
    have hEK : (embDivisor N + K₀).degree = (2 * (gN : ℤ) + 1) + (2 * (gN : ℤ) - 2) := by
      rw [map_add, degree_embDivisor, embDegree_cast, hK₀deg]
    have hdegB : 2 * (gN : ℤ) + 1 ≤ (embDivisor N + K₀).degree := by
      rw [hEK]; omega
    obtain ⟨C₂, hC₂⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_add_pointHt_le N G w₄ F₂ hG0 hw₄0 hF₂0
      ((4 * gN - 1) • D₃) (embDivisor N + K₀) hdegA hdegB hGspan hw₄span (by rw [hF₂span])
    have hA₁deg : A₁.degree = (8 * (gN : ℤ) - 2) * (2 * (gN : ℤ) + 1) := by
      rw [hA₁, map_nsmul, nsmul_eq_mul, degree_embDivisor, embDegree_cast, h82]
    have hA₂deg : A₂.degree = (4 * (gN : ℤ) - 1) * (4 * (gN : ℤ) + 1) + ((2 * (gN : ℤ) + 1) + (2 * (gN : ℤ) - 2)) := by
      rw [hA₂, map_add, map_nsmul, nsmul_eq_mul, hD₃deg, hEK, h41]
    have hdeg1 : 2 * (gN : ℤ) + 1 ≤ A₁.degree := by
      rw [hA₁deg]; nlinarith [hγZ]
    have hdegeq : A₁.degree = A₂.degree := by
      rw [hA₁deg, hA₂deg]; ring
    have hε' : 0 < ε / (8 * (gN : ℝ)) := by positivity
    obtain ⟨CE, hCE⟩ := ModularCurve.JZero.exists_abs_pointHt_sub_pointHt_le_mul_add_of_degree_eq N F₁ F₂ hF₁0 hF₂0
      A₁ A₂ hdeg1 hdegeq hF₁span hF₂span (ε / (8 * (gN : ℝ))) hε'
    set Cmain : ℝ := CL + CT + (4 * (gN : ℝ) - 1) * Cβ + C₁ + CG + C₂ + CE + ε / (8 * (gN : ℝ)) * |C₁| with hCmain

    set jB : modularFunctionFieldBar N := (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) with hjB
    have h𝒞 : ∃ 𝒞 : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        ∀ v, jB ∉ v.toValuationSubring → v ∈ 𝒞 := by
      by_cases hj0 : jB = 0
      · exact ⟨∅, fun v hv => absurd (by rw [hj0]; exact zero_mem _) hv⟩
      · haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
        obtain ⟨Dj, hDj, -⟩ := hCO.toHasPrincipalDivisors.exists_divisor jB hj0
        refine ⟨Dj.support, fun v hv => ?_⟩
        rw [Finsupp.mem_support_iff, hDj]
        intro h0
        exact hv (mem_of_eq_zero_or_ord_nonneg v (Or.inr (le_of_eq h0.symm)))
    obtain ⟨𝒞, h𝒞⟩ := h𝒞

    let chU : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v ≠ cuspInftyBar N → modularFunctionFieldBar N :=
      fun v h => (exists_chordFunction N s hs v h).choose
    let chB : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v ≠ cuspInftyBar N →
        Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
      fun v h => (exists_chordFunction N s hs v h).choose_spec.choose
    have chSpec : ∀ (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (h : v ≠ cuspInftyBar N),
        (∀ w, chB v h w = w.ord (chU v h)) ∧ chB v h v = 1 ∧ ((chB v h).sum fun _ m => |(m : ℝ)|) ≤ 2 * (embDegree N : ℝ) :=
      fun v h => let hh := (exists_chordFunction N s hs v h).choose_spec.choose_spec
        ⟨hh.2.2.2.1, hh.2.2.2.2.2.1, hh.2.2.2.2.2.2⟩
    let X' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ := fun v =>
      if h : v = cuspInftyBar N then 0 else
        |(((chB v h).erase v).sum fun w m => (m : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w))
            + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 1)
              * ((chB v h) v : ℝ) * baseHt s (cuspInftyBar N) v|
    have hX'nn : ∀ v, 0 ≤ X' v := by
      intro v
      simp only [X']
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _
    refine ⟨max Cmain 0 + ∑ w ∈ 𝒞, X' w, fun v => ?_⟩
    have hsum_nn : 0 ≤ ∑ w ∈ 𝒞, X' w := Finset.sum_nonneg fun w _ => hX'nn w
    by_cases hv : v = cuspInftyBar N
    · subst hv
      refine ⟨ginf, Binf, hBinf, hBinf1, hBinfmass, ?_⟩
      rw [functional_cusp, abs_zero]
      have := pointHt_nonneg s (cuspInftyBar N)
      have := le_max_right Cmain 0
      positivity
    by_cases hjv : jB ∈ v.toValuationSubring
    swap
    ·
      have hv𝒞 : v ∈ 𝒞 := h𝒞 v hjv
      obtain ⟨hB, hBv, hmass⟩ := chSpec v hv
      refine ⟨chU v hv, chB v hv, hB, by rw [hBv], hmass, ?_⟩
      have hle : X' v ≤ ∑ w ∈ 𝒞, X' w := Finset.single_le_sum (fun w _ => hX'nn w) hv𝒞
      have hX'v : X' v = |(((chB v hv).erase v).sum fun w m => (m : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w))
            + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 1)
              * ((chB v hv) v : ℝ) * baseHt s (cuspInftyBar N) v| := by
        simp only [X', dif_neg hv]
      have hpt := pointHt_nonneg s v
      have hCm := le_max_right Cmain 0
      have hεpt : 0 ≤ ε * pointHt s v := mul_nonneg hε.le hpt
      rw [← hX'v]
      linarith
    · obtain ⟨u, B, hu0, huE, hordv, hB, hBdeg, hBv, hmass⟩ := exists_chordFunction N s hs v hv
      refine ⟨u, B, hB, by rw [hBv], hmass, ?_⟩

      have h1 := selfFunctional_normalForm s (gN : ℝ) (embDegree N : ℤ) (cuspInftyBar N) v hv B
      rw [← erase_add_embDivisor_of_ne N B hv, sum_baseHt_eq_sum_erase_pairHt s (cuspInftyBar N) B,
        ← erase_add_embDivisor_self N B, hBv, hdR] at h1
      rw [hBv]

      have hL := hCL u hu0 huE B hB hBdeg v hv hjv hordv
      have hT := hCT v u hordv
      have hβ := hCβ v hv
      have hf₁ := hC₁ v
      have hG := hCG v
      have hf₂ := hC₂ v
      have hE := hCE v
      have h82R : ((8 * gN - 2 : ℕ) : ℝ) = 8 * (gN : ℝ) - 2 := by exact_mod_cast h82
      have h41R : ((4 * gN - 1 : ℕ) : ℝ) = 4 * (gN : ℝ) - 1 := by exact_mod_cast h41
      rw [h82R] at hf₁
      rw [h41R] at hG

      have hβ' : -((4 * (gN : ℝ) - 1) * Cβ)
            ≤ (4 * (gN : ℝ) - 1) * baseHt s (cuspInftyBar N) v - (4 * (gN : ℝ) - 1) * (2 * pointHt s v - pointHt s₃ v)
          ∧ (4 * (gN : ℝ) - 1) * baseHt s (cuspInftyBar N) v - (4 * (gN : ℝ) - 1) * (2 * pointHt s v - pointHt s₃ v)
            ≤ (4 * (gN : ℝ) - 1) * Cβ := by
        have h4 : (0 : ℝ) ≤ 4 * (gN : ℝ) - 1 := by linarith
        rw [abs_le] at hβ
        constructor <;> nlinarith [hβ.1, hβ.2]
      have hptF₁ : pointHt F₁ v ≤ (8 * (gN : ℝ) - 2) * pointHt s v + |C₁| := by
        rw [abs_le] at hf₁; linarith [le_abs_self C₁]
      have hεmul : ε / (8 * (gN : ℝ)) * pointHt F₁ v ≤ ε * pointHt s v + ε / (8 * (gN : ℝ)) * |C₁| := by
        have hpt := pointHt_nonneg s v
        have hγ8 : (0 : ℝ) < 8 * (gN : ℝ) := by positivity
        have step : ε / (8 * (gN : ℝ)) * ((8 * (gN : ℝ) - 2) * pointHt s v) ≤ ε * pointHt s v := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hγ8]; nlinarith
        nlinarith [hε'.le]
      have hCle := le_max_left Cmain 0
      rw [Int.cast_one] at h1 ⊢
      rw [abs_le] at hL hT hf₁ hG hf₂ hE ⊢
      constructor <;> linarith [hβ'.1, hβ'.2, hsum_nn]
  ·
    have hγ0 : genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) = 0 := by omega
    refine ⟨0, fun v => ?_⟩
    by_cases hv : v = cuspInftyBar N
    · subst hv
      refine ⟨ginf, Binf, hBinf, hBinf1, hBinfmass, ?_⟩
      rw [functional_cusp, abs_zero]
      have := pointHt_nonneg s (cuspInftyBar N)
      positivity
    · obtain ⟨u, B, hu0, huE, hordv, hB, hBdeg, hBv, hmass⟩ := exists_chordFunction N s hs v hv
      refine ⟨u, B, hB, by rw [hBv], hmass, ?_⟩
      have hd1 : embDegree N = 1 := by rw [embDegree, hγ0]

      have hnn : ∀ w, 0 ≤ (B + embDivisor N) w := by
        intro w
        rw [Finsupp.add_apply, hB w]
        have := ((mem_riemannRochSpace_iff.mp huE) w).resolve_left hu0
        linarith
      have hBEv : (B + embDivisor N) v = 1 := by
        rw [Finsupp.add_apply, hBv, embDivisor_apply_of_ne N hv, add_zero]
      have hBEdeg : (B + embDivisor N).degree = 1 := by
        rw [map_add, hBdeg, degree_embDivisor, hd1]; rfl
      have hBE : B + embDivisor N = Finsupp.single v 1 := by
        ext w
        by_cases hw : w = v
        · subst hw; rw [hBEv, Finsupp.single_apply, if_pos rfl]
        · rw [Finsupp.single_apply, if_neg (Ne.symm hw)]
          have h1 := apply_add_apply_le_degree_of_nonneg N (B + embDivisor N) hnn (Ne.symm hw)
          rw [hBEv, hBEdeg] at h1
          have h2 := hnn w
          omega
      have h1 := selfFunctional_normalForm s (0 : ℝ) (embDegree N : ℤ) (cuspInftyBar N) v hv B
      rw [← erase_add_embDivisor_of_ne N B hv, hBE, Finsupp.erase_single, Finsupp.sum_zero_index, hBv] at h1
      have hBsum : (B.sum fun w m => (m : ℝ) * baseHt s (cuspInftyBar N) w) = baseHt s (cuspInftyBar N) v := by
        have hB' : B = Finsupp.single v 1 + (-(embDegree N : ℤ)) • Finsupp.single (cuspInftyBar N) 1 := by
          rw [neg_smul, ← sub_eq_add_neg, ← hBE, embDivisor, add_sub_cancel_right]
        rw [hB', sum_add_single_mul, Finsupp.sum_single_index (by simp), baseHt_self]
        push_cast; ring
      rw [hBsum, hd1] at h1
      rw [hγ0, hBv]
      push_cast at h1 ⊢
      have : ((B.erase v).sum fun w m => (m : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w))
          + (2 * (0 : ℝ) - 1) * 1 * baseHt s (cuspInftyBar N) v = 0 := by linarith
      rw [this, abs_zero]
      have := pointHt_nonneg s v
      positivity

end BarMain3
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

end P2MSC
p2m_reactivate "P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le.P2MW"

open ModularCurve AlgebraicCurve

theorem solution (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N)
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        ∃ (g : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
          (∀ w, B w = w.ord g) ∧ 1 ≤ B v ∧ (B.sum fun _ m => |(m : ℝ)|) ≤ M ∧
          |((B.erase v).sum fun w m => (m : ℝ) * (baseHt s (cuspInftyBar N) w - pairHt s v w))
              + (2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) - 1)
                * (B v : ℝ) * baseHt s (cuspInftyBar N) v|
            ≤ ε * pointHt s v + C := by
  haveI := ModularCurve.hasCanonicalDivisor_modularFunctionFieldBar N
  exact P2MSC.selfChord_main N hN hN5 s hs

end S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le
end P2MW
export P2MW.S_ModularCurve_JZero_pairing_chord_self_le_of_prime_of_five_le (solution)
