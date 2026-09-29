-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/b11d33e1-2335-5249-b65b-23bf4ac9070c

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_ConstantReduction_mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
import Theorems.Thm_AlgebraicCurve_exists_poleDivisor_of_transcendental
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqModC
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_ModularCurve_FullLevel_isIntegral_inclusion_modularFunctionFieldBar_fieldBar
import Theorems.Thm_AlgebraicCurve_ConstantReduction_exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
import Theorems.Thm_ModularCurve_FullLevel_exists_mem_integers_riemannRochSpace_residue_eq_of_mem_riemannRochSpace_placeMap
import Theorems.Thm_ModularCurve_exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve ModularCurve~coeffEmb_jq ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace N2RedPole

theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

theorem T_mem_gamma0 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M := by
  simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.T]

theorem transcendental_and_finiteDimensional_bar (M' : ℕ) [NeZero M']
    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hE : E = laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (y : ↥E) (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    Transcendental (AlgebraicClosure ℚ) y ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥E)) ↥E := by
  subst hE
  exact ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
    (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma0 M') (T_mem_gamma0 M') y hy

theorem finrank_adjoin_bar (M' : ℕ) [NeZero M']
    (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hE : E = modularFunctionFieldFullC (AlgebraicClosure ℚ) M')
    (y : ↥E) (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥E)) ↥E = dedekindPsi M' := by
  subst hE
  obtain rfl : y = ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_full (AlgebraicClosure ℚ) M'⟩ := Subtype.ext hy
  exact ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi (AlgebraicClosure ℚ) M'
    (Nat.cast_ne_zero.mpr (NeZero.ne M'))

theorem finrank_adjoin_geom (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (κ : Type*) [Field κ] [CharP κ q] :
    Module.finrank ↥(IntermediateField.adjoin κ ({(⟨jqModC κ, jqModC_mem κ M'⟩ : ↥(modularFunctionFieldC κ M'))} :
        Set ↥(modularFunctionFieldC κ M'))) ↥(modularFunctionFieldC κ M') = dedekindPsi M' := by
  have h1 := IntermediateField.lift_adjoin_simple κ (modularFunctionFieldC κ M') ⟨jqModC κ, jqModC_mem κ M'⟩
  have h2 : IntermediateField.adjoin κ ({jqModC κ} : Set (LaurentSeries κ)) =
      IntermediateField.map (modularFunctionFieldC κ M').val
        (IntermediateField.adjoin κ ({(⟨jqModC κ, jqModC_mem κ M'⟩ : ↥(modularFunctionFieldC κ M'))} :
          Set ↥(modularFunctionFieldC κ M'))) := h1.symm
  have hE : IntermediateField.comap (modularFunctionFieldC κ M').val (IntermediateField.adjoin κ ({jqModC κ} : Set (LaurentSeries κ))) =
      IntermediateField.adjoin κ ({(⟨jqModC κ, jqModC_mem κ M'⟩ : ↥(modularFunctionFieldC κ M'))} :
        Set ↥(modularFunctionFieldC κ M')) := by
    rw [h2, IntermediateField.comap_map]
  have h := IntermediateField.finrank_comap (IntermediateField.adjoin κ ({jqModC κ} : Set (LaurentSeries κ)))
    (modularFunctionFieldC κ M').val
  rw [IntermediateField.fieldRange_val,
    ModularCurve.relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi κ M' q hqM'] at h
  have h' := congrArg (fun K' : IntermediateField κ ↥(modularFunctionFieldC κ M') =>
    Module.finrank ↥K' ↥(modularFunctionFieldC κ M')) hE
  exact h'.symm.trans h

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
  (A : ValuationSubring (AlgebraicClosure ℚ))
  (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))

theorem mem_integers_j (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y) :
    ∃ hjO : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers, R₀.residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), hjO⟩ = jGeomGen (ResidueField A) M' := by
  have e : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [coeffMap_jqModC, coeffEmb_jq]
  have hy : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [e]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨h, hres⟩ := hR₀ (jqModC ↥A) hy
  have helt : (⟨coeffMap A.subtype (jqModC ↥A), hy⟩ : ↥(modularFunctionFieldBar M')) = (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) := Subtype.ext e
  refine ⟨helt ▸ h, ?_⟩
  apply Subtype.ext
  rw [coe_jGeomGen, ← coeffMap_jqModC (IsLocalRing.residue ↥A), ← hres]
  congr 2
  exact Subtype.ext helt.symm

theorem cuspPole_data (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M')
    (hjO : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers) (hres : R₀.residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), hjO⟩ = jGeomGen (ResidueField A) M') :
    ∃ (Du : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'))
      (Dū : Divisor (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')),
      (∀ P, Du P = max 0 (-(P.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M'))))) ∧
      (∀ Q, Dū Q = max 0 (-(Q.ord (R₀.residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), hjO⟩)))) ∧
      Divisor.degree Dū = Divisor.degree Du ∧ Dū ≠ 0 ∧
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), P.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) < 0 → 0 < P.deg) := by
  classical

  have hBar : modularFunctionFieldBar M' =
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
  have hcoe : (((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) :=
    coeffEmb_jq
  obtain ⟨htr, hfd⟩ := transcendental_and_finiteDimensional_bar M' _ hBar (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) hcoe
  haveI := hfd
  obtain ⟨Du, hDu⟩ := AlgebraicCurve.exists_poleDivisor_of_transcendental (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) htr
  have hdegu : Divisor.degree Du = (dedekindPsi M' : ℤ) := by
    rw [AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) htr Du hDu,
      finrank_adjoin_bar M' _ (ModularCurve.laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldFullC
        (AlgebraicClosure ℚ) M') (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) hcoe]

  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  have htr' : Transcendental (ResidueField ↥A) (jGeomGen (ResidueField ↥A) M') := by
    rw [← transcendental_algebraMap_iff
      (A := LaurentSeries (ResidueField ↥A)) (modularFunctionFieldC (ResidueField ↥A) M').val.toRingHom.injective]
    exact transcendental_jqModC (ResidueField ↥A)
  haveI hfd' : FiniteDimensional ↥(IntermediateField.adjoin (ResidueField ↥A)
      ({jGeomGen (ResidueField ↥A) M'} : Set ↥(modularFunctionFieldC (ResidueField ↥A) M')))
      ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
    ModularCurve.finiteDimensional_adjoin_jqModC A
  obtain ⟨Dū, hDū⟩ := AlgebraicCurve.exists_poleDivisor_of_transcendental (jGeomGen (ResidueField ↥A) M') htr'
  have hdegū : Divisor.degree Dū = (dedekindPsi M' : ℤ) := by
    rw [AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental _ htr' Dū hDū]
    exact_mod_cast finrank_adjoin_geom q M' hqM' (ResidueField ↥A)
  have hpos : 0 < Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A)
      ({jGeomGen (ResidueField ↥A) M'} : Set ↥(modularFunctionFieldC (ResidueField ↥A) M')))
      ↥(modularFunctionFieldC (ResidueField ↥A) M') := Module.finrank_pos
  refine ⟨Du, Dū, hDu, fun Q => by rw [hDū Q, hres], by rw [hdegu, hdegū], ?_, ?_⟩
  · intro h0
    have := AlgebraicCurve.degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental _ htr' Dū hDū
    rw [h0, map_zero] at this
    omega
  · intro P _
    rw [AlgebraicCurve.Place.deg_eq_one_of_isRational (ModularCurve.isRational_place_modularFunctionFieldBar M' P)]
    exact Nat.one_pos

theorem ord_residue_j_neg (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M') (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (hjO : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers) :
    ∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), P'.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) < 0 →
      (R₀.placeMap P').ord (R₀.residue ⟨(⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')), hjO⟩) < 0 := by
  obtain ⟨hjO', hres⟩ := mem_integers_j M' A R₀ hR₀
  obtain ⟨Du, Dū, hDu, hDū, hdeg, hnc, hfin⟩ := cuspPole_data q M' A R₀ hA hqM' hjO hres
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional M'
  exact (AlgebraicCurve.ConstantReduction.mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
    R₀ (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) hjO Du hDu Dū hDū hdeg hnc hfin).2.1

theorem placeMap_ne_of_ord_j_neg (hA : A.LiesOverPrime q) (hqM' : ¬ q ∣ M') (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (P₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) (hP₀ : P₀.IsRational)
    (hjP₀ : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ P₀.toValuationSubring) (hjA₀ : P₀.evalAt (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) ∈ A) :
    ∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), P'.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) < 0 → R₀.placeMap P' ≠ R₀.placeMap P₀ := by
  obtain ⟨hjO, hres⟩ := mem_integers_j M' A R₀ hR₀
  obtain ⟨Du, Dū, hDu, hDū, hdeg, hnc, hfin⟩ := cuspPole_data q M' A R₀ hA hqM' hjO hres
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional M'
  exact (AlgebraicCurve.ConstantReduction.mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
    R₀ (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) hjO Du hDu Dū hDū hdeg hnc hfin).2.2 P₀ hP₀ hjP₀ hjA₀

end N2RedPole

namespace SepCoreAux

theorem evalAt_eq_zero_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    {f : F} (hf : f ∈ v.toValuationSubring) (hpos : 0 < v.ord f) : v.evalAt f = 0 := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hf, map_zero, IsLocalRing.residue_eq_zero_iff]
  by_contra hu
  have hunit : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    by_contra h
    exact hu ((IsLocalRing.mem_maximalIdeal _).mpr h)
  obtain ⟨u, hu'⟩ := hunit
  have h0 := v.ord_coe_unit u
  rw [hu'] at h0
  change v.ord f = 0 at h0
  omega

theorem evalAt_sum_algebraMap_mul {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    {n : ℕ} (a : Fin n → K) (x : Fin n → F) (hx : ∀ i, x i ∈ v.toValuationSubring) :
    (∑ i, algebraMap K F (a i) * x i) ∈ v.toValuationSubring ∧
      v.evalAt (∑ i, algebraMap K F (a i) * x i) = ∑ i, a i * v.evalAt (x i) := by
  have hmem : (∑ i, algebraMap K F (a i) * x i) ∈ v.toValuationSubring :=
    Subring.sum_mem _ fun i _ => mul_mem (v.algebraMap_mem' (a i)) (hx i)
  refine ⟨hmem, ?_⟩
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hmem, map_sum]
  have : (⟨∑ i, algebraMap K F (a i) * x i, hmem⟩ : v.toValuationSubring) =
      ∑ i, (⟨algebraMap K F (a i), v.algebraMap_mem' (a i)⟩ : v.toValuationSubring) * ⟨x i, hx i⟩ := by
    apply Subtype.ext
    push_cast
    rfl
  rw [this, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, v.algebraMap_evalAt hv (hx i)]
  congr 1
  try (rw [← v.algebraMap_evalAt hv (v.algebraMap_mem' (a i)), v.evalAt_algebraMap_eq])

end SepCoreAux

open N2RedPole SepCoreAux in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 25600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s s' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))
    (hs : s.IsRational) (hs' : s'.IsRational)
    (hjs : jGeomGen (ResidueField A) M' ∈ s.toValuationSubring)
    (hjs' : jGeomGen (ResidueField A) M' ∈ s'.toValuationSubring)
    (hss' : s ≠ s') :
    ∃ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
      (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
        ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) ∧
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈ s.toValuationSubring ∧
      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈ s'.toValuationSubring ∧
      s.evalAt (R₀.residue ⟨_, hgi⟩) ≠ s'.evalAt (R₀.residue ⟨_, hgi⟩) := by
  classical
  set κj := (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) with hκj
  haveI hAC : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : CharP (ResidueField ↥A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA

  have hEq : modularFunctionFieldC (ResidueField ↥A) M' = modularFunctionFieldFullC (ResidueField ↥A) M' :=
    ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) q M' hqM'
  haveI hEFT : Algebra.EssFiniteType (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') := by
    have e : ∀ E : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)), E = modularFunctionFieldFullC (ResidueField ↥A) M' →
        Algebra.EssFiniteType (ResidueField ↥A) ↥E := by
      rintro E rfl; exact ModularCurve.essFiniteType_modularFunctionFieldFullC (ResidueField ↥A) M'
    exact e _ hEq
  have htr' : Transcendental (ResidueField ↥A) (jGeomGen (ResidueField ↥A) M') := by
    rw [← transcendental_algebraMap_iff
      (A := LaurentSeries (ResidueField ↥A)) (modularFunctionFieldC (ResidueField ↥A) M').val.toRingHom.injective]
    exact transcendental_jqModC (ResidueField ↥A)
  haveI hfd' : FiniteDimensional ↥(IntermediateField.adjoin (ResidueField ↥A)
      ({jGeomGen (ResidueField ↥A) M'} : Set ↥(modularFunctionFieldC (ResidueField ↥A) M'))) ↥(modularFunctionFieldC (ResidueField ↥A) M') :=
    ModularCurve.finiteDimensional_adjoin_jqModC A
  haveI hCO : IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr' hfd'

  obtain ⟨hjO, hres⟩ := mem_integers_j M' A R₀ hR₀
  have hjcusp : (cuspInftyBar M').ord κj < 0 := by
    have h := ModularCurve.ord_cuspInftyBar_coeffEmb_jq M'
    have he : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full M')⟩ : ↥(modularFunctionFieldBar M')) = κj :=
      Subtype.ext rfl
    rw [he] at h
    omega
  set c : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') := R₀.placeMap (cuspInftyBar M') with hc
  have hcpole : c.ord (jGeomGen (ResidueField ↥A) M') < 0 := by
    have := ord_residue_j_neg q M' A R₀ hA hqM' hR₀ hjO (cuspInftyBar M') hjcusp
    rwa [hres] at this
  have hsc : s ≠ c := fun h => by
    have := AlgebraicCurve.Place.ord_nonneg_of_mem s hjs
    rw [h] at this; omega
  have hs'c : s' ≠ c := fun h => by
    have := AlgebraicCurve.Place.ord_nonneg_of_mem s' hjs'
    rw [h] at this; omega

  obtain ⟨hbar, hbarRR, hbars', hbars⟩ :=
    AlgebraicCurve.exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') c s' s hs'c hsc (Ne.symm hss')

  set n : ℕ := 2 * genusFF (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') + 1 + 2 * genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') with hn
  have hbarRR' : hbar ∈ riemannRochSpace ((n : ℤ) • Finsupp.single c (1 : ℤ)) := by
    rw [mem_riemannRochSpace_iff] at hbarRR ⊢
    intro v
    rcases hbarRR v with h | h
    · exact Or.inl h
    · right
      refine le_trans ?_ h
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      split_ifs
      · simp only [mul_one, neg_le_neg_iff]; push_cast; omega
      · simp
  have hnb : 2 * genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ≤ n + 1 := by omega

  obtain ⟨f, hfO, hfRR, hfres⟩ :=
    ModularCurve.FullLevel.exists_mem_integers_riemannRochSpace_residue_eq_of_mem_riemannRochSpace_placeMap q M' hqM' A hA R₀ hR₀
      (cuspInftyBar M') n hnb hbar hbarRR'

  have hfreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), 0 ≤ P.ord κj → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M')) := by
    intro P hP
    have hP' : P ≠ cuspInftyBar M' := fun h => by rw [h] at hP; omega
    rcases (mem_riemannRochSpace_iff.mp hfRR) P with h | h
    · rw [h, Place.ord_zero]
    · simpa [Finsupp.smul_apply, Finsupp.single_apply, hP', Ne.symm hP'] using h

  obtain ⟨m, a, g, hg, hgi, hgreg, ⟨hjO', hgv⟩, hsum⟩ :=
    ModularCurve.exists_sum_smul_coeffEmb_of_mem_integers_of_cuspRegular q M' hqM' A hA R₀ hR₀ f hfO hfreg

  have hresj : R₀.residue ⟨κj, hjO'⟩ = jGeomGen (ResidueField ↥A) M' := by
    have : (⟨κj, hjO'⟩ : ↥R₀.integers) = ⟨κj, hjO⟩ := Subtype.ext rfl
    rw [this]; exact hres
  have hgs : ∀ i, (R₀.residue ⟨_, hgi i⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M')) ∈ s.toValuationSubring := fun i => hgv i (hgi i) s (hresj ▸ hjs)
  have hgs' : ∀ i, (R₀.residue ⟨_, hgi i⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M')) ∈ s'.toValuationSubring := fun i => hgv i (hgi i) s' (hresj ▸ hjs')

  by_contra hcon
  push Not at hcon
  have heq : ∀ i, s.evalAt (R₀.residue ⟨_, hgi i⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M')) = s'.evalAt (R₀.residue ⟨_, hgi i⟩) :=
    fun i => hcon (g i) (hg i) (hgi i) (hgreg i) (hgs i) (hgs' i)

  have hfsum : (⟨f, hfO⟩ : ↥R₀.integers) = ∑ i, (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ((a i : ↥A) : AlgebraicClosure ℚ),
      (R₀.algebraMap_mem_iff _).mpr (a i).2⟩ : ↥R₀.integers) * ⟨_, hgi i⟩ := by
    apply Subtype.ext
    push_cast
    exact hsum
  have hfbar : R₀.residue ⟨f, hfO⟩ = ∑ i, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') (IsLocalRing.residue ↥A (a i)) * R₀.residue ⟨_, hgi i⟩ := by
    rw [hfsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, R₀.residue_algebraMap]
  rw [hfres] at hfbar

  obtain ⟨hms, hvs⟩ := evalAt_sum_algebraMap_mul s hs (fun i => IsLocalRing.residue ↥A (a i)) (fun i => (R₀.residue ⟨_, hgi i⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M'))) hgs
  obtain ⟨hms', hvs'⟩ := evalAt_sum_algebraMap_mul s' hs' (fun i => IsLocalRing.residue ↥A (a i)) (fun i => (R₀.residue ⟨_, hgi i⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) M'))) hgs'
  rw [← hfbar] at hms hvs hms' hvs'
  have hval : s.evalAt hbar = s'.evalAt hbar := by
    rw [hvs, hvs']; exact Finset.sum_congr rfl fun i _ => by rw [heq i]

  have hbar0 : hbar ≠ 0 := fun h => by rw [h, Place.ord_zero] at hbars'; exact lt_irrefl _ hbars'
  have h1 : s.evalAt hbar ≠ 0 := s.evalAt_ne_zero_of_ord_eq_zero hs hbar0 hbars
  have h2 : s'.evalAt hbar = 0 := evalAt_eq_zero_of_ord_pos s' hs' hms' hbars'
  exact h1 (hval.trans h2)

end S_ModularCurve_FullLevel_exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_rational_integral_cuspRegular_evalAt_ne_of_isRational_of_ne (solution)
