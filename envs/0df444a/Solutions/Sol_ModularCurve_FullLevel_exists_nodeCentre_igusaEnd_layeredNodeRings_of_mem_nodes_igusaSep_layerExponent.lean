-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_nodeCentre_igusaEnd_layeredNodeRings_of_mem_nodes_igusaSep_layerExponent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/b703e0d9-d00d-525c-ad1d-72ed766e02c4

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Theorems.Thm_ModularCurve_FullLevel_exists_centrePlace_ord_residue_eq_one_of_node_crossingPresentation
import Theorems.Thm_ModularCurve_FullLevel_exists_branchPlace_igusaEnd_integral_overS_of_node_crossingPresentation_igusaBranch
import Theorems.Thm_ModularCurve_mem_iff_mem_constantReduction_integers_of_jq_mem_residuallyTranscendental
import Theorems.Thm_ModularCurve_FullLevel_evalAt_mem_of_mem_integers_igusaEnd_of_forall_mem_nodePlaces
import Theorems.Thm_ModularCurve_FullLevel_exists_layeredRationalNodeRings_of_node_ends_layers
import Theorems.Thm_ModularCurve_FullLevel_igusaBranch_le_of_le_of_mem_maximalIdeal_of_not_mem_of_node_crossingPresentation
import Theorems.Thm_ModularCurve_FullLevel_exists_mem_eq_cx_mul_unit_isUnit_of_commonChart_of_igusaSep
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_FullLevel_mem_nodePlaces_iff_smul_mem_of_arithmeticGalois_smul_eq_of_mem_decompositionSubgroup
import Theorems.Thm_ModularCurve_FullLevel_tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_eq_self_of_forall_coeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_nodeCentre_igusaEnd_layeredNodeRings_of_mem_nodes_igusaSep_layerExponent
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar"
p2m_attr_erase "instance" "ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem nc1_pow_exp_unique {L : Type*} [Field L] (A : ValuationSubring L) {π t v v' : L} (hπA : π ∈ A)
    (hπm : (⟨π, hπA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) (hπ0 : π ≠ 0)
    (hv : v ∈ A) (hvi : v⁻¹ ∈ A) (hv' : v' ∈ A) (hvi' : v'⁻¹ ∈ A)
    {m n : ℕ} (hm : π ^ m = t * v) (hn : π ^ n = t * v') : m = n := by
  have key : ∀ {m n : ℕ} {v v' : L}, v ∈ A → v⁻¹ ∈ A → v' ∈ A → v'⁻¹ ∈ A →
      π ^ m = t * v → π ^ n = t * v' → m ≤ n → m = n := by
    intro m n v v' hv hvi hv' hvi' hm hn hle
    by_contra hne
    have hlt : m < n := lt_of_le_of_ne hle hne
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact pow_ne_zero m hπ0 (by rw [hm, zero_mul])
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact pow_ne_zero m hπ0 (by rw [hm, mul_zero])
    have hv'0 : v' ≠ 0 := by
      rintro rfl
      exact pow_ne_zero n hπ0 (by rw [hn, mul_zero])
    have h2 : v * π ^ (n - m) = v' := by
      have h1 : π ^ m * π ^ (n - m) = π ^ n := pow_mul_pow_sub π hle
      rw [hm, hn, mul_assoc] at h1
      exact mul_left_cancel₀ ht0 h1
    have hpow : π ^ (n - m) = v' * v⁻¹ := by
      rw [← h2]; field_simp
    have hmemA : π ^ (n - m) ∈ A := pow_mem hπA _
    have hunit : IsUnit (⟨π ^ (n - m), hmemA⟩ : ↥A) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨v * v'⁻¹, mul_mem hv hvi'⟩, Subtype.ext ?_⟩
      show π ^ (n - m) * (v * v'⁻¹) = 1
      rw [hpow]; field_simp
    have hmax : (⟨π ^ (n - m), hmemA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      have : (⟨π ^ (n - m), hmemA⟩ : ↥A) = (⟨π, hπA⟩ : ↥A) ^ (n - m) := Subtype.ext (by simp)
      rw [this]
      exact Ideal.pow_mem_of_mem _ hπm _ (Nat.sub_pos_of_lt hlt)
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmax)) hunit
  rcases le_total m n with h | h
  · exact key hv hvi hv' hvi' hm hn h
  · exact (key hv' hvi' hv hvi hn hm h).symm

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 0 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    {ι : Type} (K : ι → IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKfin : ∀ n, FiniteDimensional ↥k₀ ↥(K n))
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : AlgebraicClosure ℚ) ∈ A)

    (n₀ : ι) (hn₀ : ∀ n, K n₀ ≤ K n)

    (hKcof : ∀ T : Finset (AlgebraicClosure ℚ), ∃ n : ι, ∀ x ∈ T, x ∈ Set.range (fun y : ↥(K n) => (y : AlgebraicClosure ℚ)))

    (πt : AlgebraicClosure ℚ) (hπt : πt ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπA : πt ∈ A)

    (htame : ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 → ∀ x : ↥(K n₀), τ (x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))

    (Kb : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKb : Kb = ⊥)
    (Ab : ValuationSubring ↥Kb) (hAb : ∀ x : ↥Kb, x ∈ Ab ↔ (x : (AlgebraicClosure ℚ)) ∈ A)
    (ϖb : ↥Ab) (hϖb : maximalIdeal ↥Ab = Ideal.span {ϖb}) (hϖb0 : ϖb ≠ 0) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),
      (

      (∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ∃ c : ↥k₀, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n = ((c : ↥k₀) : AlgebraicClosure ℚ)) ∧

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) ∧

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ γ f ∈ F₀) ∧

      (∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' →
        ∀ (m : ℕ) (c : Fin m → (AlgebraicClosure ℚ)) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
          LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0)) →
    ∀ (W₀ : ValuationSubring ↥F₀),

    ∀ (B : Subring ↥(fieldBar q M')) (alg : Algebra ↥Ab ↥B)
      (hjR : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
         coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
         ↥(modularFunctionFieldBar M')) ∈ R₀.integers)
      (hjs : (R₀.residue ⟨_, hjR⟩ : modularFunctionFieldC (ResidueField A) M') ∈
         (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring)
      (hJK : ModularCurve.jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M')
      (a₀ : ↥k₀) (ha₀ : (a₀ : (AlgebraicClosure ℚ)) ∈ A)
      (hpin : (residue A ⟨(a₀ : (AlgebraicClosure ℚ)), ha₀⟩) ^ q =
         (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hjR⟩))
      (nodes : Finset (Subring ↥F₀)),
      (

      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W₀) ∧
      IsDiscreteValuationRing ↥W₀ ∧
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W₀, maximalIdeal ↥W₀ = Ideal.span {(⟨_, hπW⟩ : ↥W₀)}) ∧

      (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
        (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
            ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
            (⟨_, hF⟩ : ↥F₀) ∈ W₀ ∧
            ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
              residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
              ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ W₀, (⟨_, hm⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧

      (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀),
          (⟨f, hf⟩ : ↥F₀) ∈ W₀ ↔ (⟨_, hf'⟩ : ↥F₀) ∈ W₀) ∧

      (

        (∀ a : ↥Ab, ((@algebraMap ↥Ab ↥B _ _ alg a : ↥B) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥Kb) : (AlgebraicClosure ℚ))) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
        (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑Kb : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥B, (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        @Algebra.FormallySmooth ↥Ab ↥B _ _ alg ∧ @Algebra.FinitePresentation ↥Ab ↥B _ _ alg ∧
        Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb}) ∧

        (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ W₀) ∧
        Prime (@algebraMap ↥Ab ↥B _ _ alg ϖb) ∧
        (∀ f : ↥F₀, f ∈ W₀ ↔ ∃ g h : ↥B, ¬ (@algebraMap ↥Ab ↥B _ _ alg ϖb ∣ h) ∧ (f : ↥(fieldBar q M')) * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

        ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ B) ∧
        (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ B → levelAutBar q M' ζ γ f ∈ B) ∧

        (∃ (b : ↥(fieldBar q M')) (hbF : b ∈ F₀), b ∈ B ∧ ∀ V : ValuationSubring ↥F₀,
          (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
          (∀ hπV : algebraMap ↥k₀ ↥F₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
          ∀ (hjF : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)
            (hjV : (⟨(IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjF⟩ : ↥F₀) ∈ V),
            (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
              ∀ hp : Polynomial.aeval (⟨(IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjF⟩ : ↥F₀) (p.map (algebraMap ↥k₀ ↥F₀)) ∈ V,
                (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
          (⟨b, hbF⟩ : ↥F₀) ∉ V) ∧

        (∀ s' : ↥W, s' ≠ s → ∃ (b : ↥(fieldBar q M')) (hbF : b ∈ F₀), b ∈ B ∧ ∀ V : ValuationSubring ↥F₀,
          (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
          (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
            (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                ((s' : ↥W) : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                (⟨_, hF⟩ : ↥F₀) ∈ V ∧
                ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
                  residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                    ((s' : ↥W) : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                  ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
          (⟨b, hbF⟩ : ↥F₀) ∉ V) ∧

        (∀ (inst : Algebra (GaloisField q 2) (ResidueField ↥A)),
          ∀ (_ : IsDomain (DrinfeldCurve.CoordRing q (ResidueField ↥A))),
          ∀ (ζ : Idx q),
          ∃ (Cs : Subgroup (rootsOfUnity (q + 1) (GaloisField q 2)))
            (ρ : ↥B →+* ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)),
            Nat.card Cs = 2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
            RingHom.ker ρ = Ideal.span {@algebraMap ↥Ab ↥B _ _ alg ϖb} ∧
            (∀ a : ↥Ab, ρ (@algebraMap ↥Ab ↥B _ _ alg a) =
              algebraMap (ResidueField ↥A) ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs) (IsLocalRing.residue ↥A ⟨((a : ↥Kb) : (AlgebraicClosure ℚ)), (hAb a).mp a.2⟩)) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), ∃ g h : ↥B, ρ h ≠ 0 ∧ z * ρ h = ρ g) ∧
            (∀ z : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs), z ∈ Set.range ρ ↔
              (z : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) ∈ Set.range (algebraMap (DrinfeldCurve.CoordRing q (ResidueField ↥A)) (DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧
            (∀ (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
              ∀ (hmem : (redQ q γ, (1 : (GaloisField q 2)ˣ)) ∈ DrinfeldCurve.hSubgroup q)
                (f : ↥B) (hf' : levelAutBar q M' ζ γ⁻¹ (f : ↥(fieldBar q M')) ∈ B),
                ((ρ ⟨_, hf'⟩ : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)) =
                  DrinfeldCurve.hFunctionFieldAction q (ResidueField ↥A) ⟨_, hmem⟩ ((ρ f : ↥(DrinfeldCurve.quotField q (ResidueField ↥A) Cs)) : DrinfeldCurve.drinfeldFunctionField q (ResidueField ↥A)))) ∧

        (
          nodes.card = q + 1 ∧

          (∃ Bc : Subring ↥F₀,
            (∃ T : Finset ↥F₀, Bc = Subring.closure
              ({f : ↥F₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥F₀ x} ∪ (↑T : Set ↥F₀))) ∧
            ∀ O ∈ nodes, (∀ f : ↥F₀, f ∈ Bc → f ∈ O) ∧
              (∀ f : ↥F₀, f ∈ O ↔ ∃ g h : ↥F₀, g ∈ Bc ∧ h ∈ Bc ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)) ∧

          (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ O ∈ nodes, ∃ O' ∈ nodes,
            ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨_, hf'⟩ : ↥F₀) ∈ O') ∧
          (∀ (ζ : Idx q), ∀ O ∈ nodes, ∀ O' ∈ nodes, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧
            ∀ (f : ↥(fieldBar q M')) (hf : f ∈ F₀) (hf' : levelAutBar q M' ζ γ f ∈ F₀), (⟨f, hf⟩ : ↥F₀) ∈ O ↔ (⟨_, hf'⟩ : ↥F₀) ∈ O') ∧

          (∀ O ∈ nodes, ∀ O' ∈ nodes, O ≠ O' → ∃ (f : ↥F₀) (hf : f ∈ O) (hf' : f ∈ O'),
            ¬ IsUnit (⟨f, hf⟩ : ↥O) ∧ IsUnit (⟨f, hf'⟩ : ↥O')) ∧

          (∀ V : ValuationSubring ↥F₀, (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
                  (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
              (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
              (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                  ↥(modularFunctionFieldBar M'))) →
              (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                  (⟨_, hF⟩ : ↥F₀) ∈ V ∧
                  ∀ (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A),
                    residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                    ∃ hm : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ V, (⟨_, hm⟩ : ↥V) ∈ maximalIdeal ↥V) →
            (∀ f : ↥(fieldBar q M'), f ∈ B → ∃ hf : f ∈ F₀, (⟨f, hf⟩ : ↥F₀) ∈ V) ∨
            (∃ O ∈ nodes, ∀ (f : ↥F₀) (hfO : f ∈ O), f ∈ V ∧ (¬ IsUnit (⟨f, hfO⟩ : ↥O) → ∀ hfV : f ∈ V, (⟨f, hfV⟩ : ↥V) ∈ maximalIdeal ↥V))) ∧

          (∀ O ∈ nodes,

            (∀ f : ↥F₀, f ∈ O → f ∈ W₀) ∧ ∃ (_ : IsLocalRing ↥O) (_ : IsNoetherianRing ↥O),
            (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ O) ∧
            (∀ (f : ↥F₀) (hf : f ∈ O), ∃ (x : ↥k₀) (hx : algebraMap ↥k₀ ↥F₀ x ∈ O), (x : (AlgebraicClosure ℚ)) ∈ A ∧
              ¬ IsUnit ((⟨f, hf⟩ : ↥O) - ⟨_, hx⟩)) ∧

            (∃ (E₀ : ℕ) (_ : 1 ≤ E₀)

               (_ : ∃ v : ↥k₀, (v : (AlgebraicClosure ℚ)) ∈ A ∧ ((v⁻¹ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A ∧
                  π₀ ^ E₀ = ϖt ^ (2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) * v)
               (hπO : algebraMap ↥k₀ ↥F₀ π₀ ∈ O) (cx cy : ↥O) (u : (↥O)ˣ)
               (ι : (AdicCompletion (maximalIdeal ↥O) ↥O) ≃+* UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))
               (γU γV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ),
              cx * cy = (⟨_, hπO⟩ : ↥O) ^ E₀ * (u : ↥O) ∧
              (∀ (x : ↥k₀) (hx : (x : (AlgebraicClosure ℚ)) ∈ A) (hxO : algebraMap ↥k₀ ↥F₀ x ∈ O),
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hxO⟩) =
                  UVCrossingModel.const ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) (algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨x, hx⟩)) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cx) = (γU : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.U ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
              ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) cy) = (γV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀) ∧
              ((cy : ↥F₀) ∈ W₀) ∧ (∀ hcy : (cy : ↥F₀) ∈ W₀, (⟨(cy : ↥F₀), hcy⟩ : ↥W₀) ∈ maximalIdeal ↥W₀) ∧
              (∀ hcx : (cx : ↥F₀) ∈ W₀, (⟨(cx : ↥F₀), hcx⟩ : ↥W₀) ∉ maximalIdeal ↥W₀) ∧

              (∃ (hjF : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                    algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a₀ : (AlgebraicClosure ℚ)) ∈ F₀)
                 (hjO : (⟨_, hjF⟩ : ↥F₀) ∈ O) (e : ℕ) (wV : (UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀))ˣ), 1 ≤ e ∧
                ι (algebraMap ↥O (AdicCompletion (maximalIdeal ↥O) ↥O) ⟨_, hjO⟩) =
                  (wV : UVCrossingModel (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) * (UVCrossingModel.V ((algebraMap ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) (AdicCompletion (maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ⟨π₀, hπ⟩) ^ E₀)) ^ e) ∧

              (∃ Wx : ValuationSubring ↥F₀,
                (∀ f : ↥F₀, f ∈ O → f ∈ Wx) ∧
                (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ Wx) ∧
                IsDiscreteValuationRing ↥Wx ∧
                (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx, maximalIdeal ↥Wx = Ideal.span {(⟨_, hπW⟩ : ↥Wx)}) ∧
                (∃ t : ↥Wx, ∀ p : Polynomial ↥k₀, (∀ n, ((p.coeff n : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                  (∃ hm : Polynomial.aeval (t : ↥F₀) p ∈ Wx, (⟨_, hm⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) →
                    ∀ n, ∃ hc : algebraMap ↥k₀ ↥F₀ (p.coeff n) ∈ Wx, (⟨_, hc⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcx : (cx : ↥F₀) ∈ Wx, (⟨(cx : ↥F₀), hcx⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
                (∀ hcy : (cy : ↥F₀) ∈ Wx, (⟨(cy : ↥F₀), hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
                (∀ (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
                  (hgi : (⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers),
                  (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                      ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
                    0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(modularFunctionFieldBar M')) :
                      ↥(modularFunctionFieldBar M'))) →
                  ∃ hF : (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : ↥(fieldBar q M')) ∈ F₀,
                    (⟨_, hF⟩ : ↥F₀) ∈ Wx ∧
                    (∀ hW : (⟨_, hF⟩ : ↥F₀) ∈ Wx, (⟨_, hW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx ↔
                      (R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') = 0) ∧
                    ((R₀.residue ⟨_, hgi⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                      (⟨_, hF⟩ : ↥F₀) ∈ O ∧
                      ∀ (hO : (⟨_, hF⟩ : ↥F₀) ∈ O) (c : ↥k₀) (hc : (c : (AlgebraicClosure ℚ)) ∈ A) (hcO : algebraMap ↥k₀ ↥F₀ c ∈ O),
                        residue A ⟨(c : (AlgebraicClosure ℚ)), hc⟩ =
                          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) →
                        ¬ IsUnit ((⟨_, hO⟩ : ↥O) - ⟨_, hcO⟩))) ∧

                (∀ O' ∈ nodes, O' ≠ O → ∃ f : ↥F₀, f ∈ O' ∧ f ∉ Wx)) ∧

              (∃ Bx : Subring ↥F₀,
                (∀ f : ↥F₀, f ∈ Bx → (f : ↥(fieldBar q M')) ∈ B ∧ f ∈ O) ∧
                (∀ (f : ↥F₀), f ∈ Bx → ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'),
                  0 ≤ P.ord ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))) → 0 ≤ P.ord (f : ↥(fieldBar q M'))) ∧
                (∀ f : ↥F₀, f ∈ O ↔ ∃ g h : ↥F₀, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g) ∧
                (∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ Bx ∧ h ∈ Bx ∧ h ≠ 0 ∧ f * h = g) ∧
                (∃ T : Finset ↥F₀, Bx = Subring.closure
                  ({f : ↥F₀ | ∃ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ∧ f = algebraMap ↥k₀ ↥F₀ x} ∪ (↑T : Set ↥F₀))) ∧

                (∃ b : ↥F₀, b ∈ Bx ∧ ∀ V : ValuationSubring ↥F₀,
                  (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ V) →
                  (∀ hπV : algebraMap ↥k₀ ↥F₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
                  ∀ (hjF : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)
                    (hjV : (⟨(IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjF⟩ : ↥F₀) ∈ V),
                    (∀ p : Polynomial ↥k₀, p.Monic → (∀ i : ℕ, ((p.coeff i : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A) →
                      ∀ hp : Polynomial.aeval (⟨(IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')), hjF⟩ : ↥F₀) (p.map (algebraMap ↥k₀ ↥F₀)) ∈ V,
                        (⟨_, hp⟩ : ↥V) ∉ maximalIdeal ↥V) →
                  (∃ f : ↥F₀, f ∈ O ∧ f ∉ V) → b ∉ V))))))
      ) →
      (∀ (FSS : Type) [Field FSS] [Algebra (ResidueField ↥A) FSS] (R : RegularProlongation A ↥(fieldBar q M') FSS),
        (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W₀)) →

    ∀ (O : Subring ↥F₀), O ∈ nodes → ∀ (E₀ : ℕ), 1 ≤ E₀ →
      (∃ v : ↥k₀, (v : (AlgebraicClosure ℚ)) ∈ A ∧ ((v⁻¹ : ↥k₀) : (AlgebraicClosure ℚ)) ∈ A ∧
                  π₀ ^ E₀ = ϖt ^ (2 * placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) * v) →

    ∀ (C' : ι → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : ι) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
      [∀ l, IsDomain ↥(C' l)] [∀ l, IsDiscreteValuationRing ↥(C' l)]
      (ϖ' : ∀ l, ↥(C' l))
      (Wc : ι → Type) [∀ l, CommRing (Wc l)] [∀ l, IsDomain (Wc l)] [∀ l, IsDiscreteValuationRing (Wc l)]
      [∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l)]
      (π : ∀ l, Wc l) (eL : ι → ℕ) (jc : ∀ l, ↥(C' l) →+* Wc l),
      (∀ (l : ι) (c : AlgebraicClosure ℚ), c ∈ C' l ↔ c ∈ A ∧ c ∈ Set.range (fun x : ↥(K l) => (x : AlgebraicClosure ℚ))) →
      (∀ (l : ι) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d') →
      (∀ l, C' n₀ ≤ C' l) →
      (∀ l, Irreducible (π l)) →
      (∀ l, ∃ v : AlgebraicClosure ℚ, v ∈ C' l ∧ v⁻¹ ∈ C' l ∧ (π₀ : AlgebraicClosure ℚ) = v * ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ^ eL l) →
      (∀ l, jc l (ϖ' l) = π l) →
      (∀ (l : ι) (n : ℕ) (c : ↥(C' l)), jc l c ∈ Ideal.span {π l ^ n} → c ∈ Ideal.span {ϖ' l ^ n}) →
      (∀ (l : ι) (n : ℕ) (w : Wc l), ∃ c : ↥(C' l), w - jc l c ∈ Ideal.span {π l ^ n}) →
        ∃ (nd : Place (ResidueField ↥A) FSS) (FI : Type) (_ : Field FI) (_ : Algebra (ResidueField ↥A) FI)
          (Rx : RegularProlongation A ↥(fieldBar q M') FI) (bx : Place (ResidueField ↥A) FI)
          (Wx : ValuationSubring ↥F₀)
          (S : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))) (𝒩 : Subring ↥(fieldBar q M'))
          (𝒩₀L : ι → Subring ↥(fieldBar q M')) (hlocL : ∀ l, IsLocalRing ↥(𝒩₀L l)) (_ : ∀ l, IsNoetherianRing ↥(𝒩₀L l))
          (cx cy cu : ↥(fieldBar q M')),
          nd.IsRational ∧

          (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ Rx.integers ↔ f ∈ Wx)) ∧
          (∀ f : ↥F₀, f ∈ O → f ∈ Wx) ∧
          (∀ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ Wx, (⟨_, hπW⟩ : ↥Wx) ∈ maximalIdeal ↥Wx) ∧
          (∃ (cyO : ↥F₀), cyO ∈ O ∧ (cyO : ↥(fieldBar q M')) = cy ∧ (∀ hcy : cyO ∈ Wx, (⟨cyO, hcy⟩ : ↥Wx) ∉ maximalIdeal ↥Wx) ∧
            ∀ V : ValuationSubring ↥F₀, (∀ f : ↥F₀, f ∈ O → f ∈ V) →
              (∀ hπV : algebraMap ↥k₀ ↥F₀ π₀ ∈ V, (⟨_, hπV⟩ : ↥V) ∈ maximalIdeal ↥V) →
              (∀ hcy : cyO ∈ V, (⟨cyO, hcy⟩ : ↥V) ∉ maximalIdeal ↥V) → ∀ f : ↥F₀, f ∈ Wx → f ∈ V) ∧

          (∀ O' ∈ nodes, O' ≠ O → ∃ (g : ↥F₀) (hg : g ∈ O) (hg' : g ∈ O'),
            (∃ (c : ↥F₀) (hc : c ∈ O) (u : ↥F₀) (hu : u ∈ O), (c : ↥(fieldBar q M')) = cx ∧ IsUnit (⟨u, hu⟩ : ↥O) ∧ g = c * u) ∧
            IsUnit (⟨g, hg'⟩ : ↥O')) ∧

            (O ∈ nodes ∧
              (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ 𝒩₀L n₀) ∧
              (∀ (f : ↥F₀) (hf : f ∈ O) (hN : (f : ↥(fieldBar q M')) ∈ 𝒩₀L n₀),
                ¬ IsUnit (⟨f, hf⟩ : ↥O) → ¬ IsUnit (⟨(f : ↥(fieldBar q M')), hN⟩ : ↥(𝒩₀L n₀))) ∧

              (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S ↔
                (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ P.toValuationSubring) ∧
                (∀ (f : ↥F₀) (hfO : f ∈ O), ¬ IsUnit (⟨f, hfO⟩ : ↥O) →
                  ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)) ∧

              (∀ (f : ↥F₀) (_ : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ R.integers),
                R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ nd.toValuationSubring) ∧
              (∀ (f : ↥F₀) (hf : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ R.integers), ¬ IsUnit (⟨f, hf⟩ : ↥O) →
                ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ nd.toValuationSubring,
                  (⟨_, hm⟩ : ↥nd.toValuationSubring) ∈ maximalIdeal ↥nd.toValuationSubring) ∧
              (∀ y : Place (ResidueField A) FSS,
                (∀ (f : ↥F₀) (_ : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ R.integers),
                  R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ y.toValuationSubring) →
                (∀ (f : ↥F₀) (hf : f ∈ O) (hR : (f : ↥(fieldBar q M')) ∈ R.integers), ¬ IsUnit (⟨f, hf⟩ : ↥O) →
                  ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ y.toValuationSubring,
                    (⟨_, hm⟩ : ↥y.toValuationSubring) ∈ maximalIdeal ↥y.toValuationSubring) →
                y = nd)) ∧

            bx.IsRational ∧ nd.IsRational ∧ (∀ P ∈ S, P.IsRational) ∧

            (∀ f : fieldBar q M', f ∈ 𝒩 ↔ f ∈ Rx.integers ∧ f ∈ R.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring) ∧
            (∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A) ∧

            cx * cy = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) ^ (eL n₀ * E₀) * cu ∧
            (∀ h₁ : cx ∈ Rx.integers, Rx.residue ⟨cx, h₁⟩ = 0) ∧
            (∀ h₂ : cx ∈ R.integers, nd.ord (R.residue ⟨cx, h₂⟩) = 1) ∧
            (∀ h₂ : cy ∈ R.integers, R.residue ⟨cy, h₂⟩ = 0) ∧
            (∀ h₁ : cy ∈ Rx.integers, bx.ord (Rx.residue ⟨cy, h₁⟩) = 1) ∧

            (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 →
              let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S ↔ g • P ∈ S) ∧ g • cx = cx ∧ g • cy = cy) ∧

            (∀ f : fieldBar q M', ∃ (l : ι) (a b : ↥(𝒩₀L l)), (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = (a : fieldBar q M')) ∧

            (∀ f : fieldBar q M', ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀L n₀)) (b : ↥(𝒩₀L n₀)),
              (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = ∑ i, c i • ((a i : ↥(𝒩₀L n₀)) : fieldBar q M')) ∧

            (∀ l, letI : IsLocalRing ↥(𝒩₀L l) := hlocL l;
              𝒩₀L n₀ ≤ 𝒩₀L l ∧ 𝒩₀L l ≤ 𝒩 ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S ↔
                (∀ f : fieldBar q M', f ∈ 𝒩₀L l → f ∈ P.toValuationSubring) ∧
                (∀ f : ↥(𝒩₀L l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
              (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀L l) ∧
              (∀ g : ↥(𝒩₀L l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀L l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
              (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀L l)), LinearIndependent ↥(C' l) c →
                ∑ i, c i • ((a i : ↥(𝒩₀L l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧

              (∃ Bx : Subring (fieldBar q M'),
                (∀ f : fieldBar q M', f ∈ Bx → f ∈ 𝒩₀L l) ∧
                cx ∈ Bx ∧ cy ∈ Bx ∧ cu ∈ Bx ∧
                (∀ f : fieldBar q M', f ∈ 𝒩₀L l ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
                  (∀ hh : h ∈ 𝒩₀L l, IsUnit (⟨h, hh⟩ : ↥(𝒩₀L l))) ∧ f * h = g) ∧
                (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
                  ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
                    (↑T : Set (fieldBar q M'))))) ∧
              cx ∈ 𝒩₀L l ∧ cy ∈ 𝒩₀L l ∧ (∃ hu : cu ∈ 𝒩₀L l, IsUnit (⟨cu, hu⟩ : ↥(𝒩₀L l))) ∧
              ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l))
                (ιc : AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l) ≃+* UVCrossingModel (Wc l) (π l ^ (eL l * E₀))),
                (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀L l,
                  σ (π l) = algebraMap ↥(𝒩₀L l) (AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l)) ⟨_, h⟩) ∧
                (∀ o : Wc l, ιc (σ o) = const (π l ^ (eL l * E₀)) o) ∧

                (∃ (hJ : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a₀ : AlgebraicClosure ℚ) ∈ 𝒩₀L l)
                   (e : ℕ) (w : (UVCrossingModel (Wc l) (π l ^ (eL l * E₀)))ˣ), 1 ≤ e ∧
                  ιc (algebraMap ↥(𝒩₀L l) (AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l)) ⟨_, hJ⟩) =
                    (w : UVCrossingModel (Wc l) (π l ^ (eL l * E₀))) * V (π l ^ (eL l * E₀)) ^ e) ∧
                (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀L l),
                  ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀L l) (AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l)) ⟨_, h⟩) ∧
                (∀ (f : ↥(𝒩₀L l)) (n : ℕ) (h₁ : f.1 ∈ Rx.integers), Rx.residue ⟨f.1, h₁⟩ ≠ 0 →
                  bx.ord (Rx.residue ⟨f.1, h₁⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (π l ^ (eL l * E₀)), IsUnit γ ∧
                      ιc (algebraMap ↥(𝒩₀L l) (AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l)) f) - γ * V (π l ^ (eL l * E₀)) ^ n ∈
                        Ideal.span {const (π l ^ (eL l * E₀)) (π l), U (π l ^ (eL l * E₀))}) ∧
                (∀ (f : ↥(𝒩₀L l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
                  nd.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (π l ^ (eL l * E₀)), IsUnit γ ∧
                      ιc (algebraMap ↥(𝒩₀L l) (AdicCompletion (maximalIdeal ↥(𝒩₀L l)) ↥(𝒩₀L l)) f) - γ * U (π l ^ (eL l * E₀)) ^ n ∈
                        Ideal.span {const (π l ^ (eL l * E₀)) (π l), V (π l ^ (eL l * E₀))})) ∧

          (∀ P ∈ S, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              ∀ a : A, residue A a =
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧

          (∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ Rx.integers) ∧

          (∃ j : modularFunctionFieldC (ResidueField A) M' →+* FI,
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ Rx.integers,
                Rx.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
            ∀ g : modularFunctionFieldC (ResidueField A) M',
              g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
                j g ∈ bx.toValuationSubring)) := by

  intro F₀ hF₀ W₀ B alg hjR hjs hJK a₀ ha₀ hpin nodes hANT FSS instFSS instAlgFSS R hRW O hO E₀ hE₀ hmod C' hC'A iCD iCV ϖ' Wc iW1 iW2 iW3 iW4 π eL jc hLP hϖker hCle hπirr hram hjϖ hjinj hjsur
  obtain ⟨hCHAR, hK1, hSTAB, hLD⟩ := hF₀
  obtain ⟨h2a, h2b, h2c, h4, h5W, hM1, hM0a, hM0b, hM4a, hM4b, hM4c, hM2a, hM2b, hM2c, hM5a, hM5b, hE1p, hE3, hM3, hNrest⟩ := hANT
  have hNCOMMON := hNrest.2.1
  have hNSEP := hNrest.2.2.2.2.1
  have hpernode := hNrest.2.2.2.2.2.2
  classical

  have hpo := hpernode O hO
  obtain ⟨hN1W, instLoc, instNoeth, hN1k, hN1res, E₁, hE₁, hmod₁, hπO, cx, cy, u, ιO, γU, γV, hxy, hconst, hιcx, hιcy,
    hcyW, hcyM, hcxM, ⟨hjF, hjO, eJ, wV, heJ, hgerm⟩, ⟨Wx, hOWx, hWxk, hWxdvr, hWxunif, hWxtr, hcxWx, hcyWx, hWxM', hIGSEP⟩,
    ⟨Bx, hBxBO, hBxreg, hOloc, hfrac, hBxfg, hN5⟩⟩ := hpo
  haveI : IsLocalRing ↥O := instLoc
  haveI : IsNoetherianRing ↥O := instNoeth

  have hπcomap : (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∈
      maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) := by
    rw [hunif]; exact Ideal.mem_span_singleton_self _
  have hπ0 : (π₀ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field' (R := ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    rw [hunif, Ideal.span_singleton_eq_bot]
    exact Subtype.ext (Subtype.ext h0)
  have hπmax : (⟨(π₀ : AlgebraicClosure ℚ), hπ⟩ : ↥A) ∈ maximalIdeal ↥A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    have hwval : (w : AlgebraicClosure ℚ) = (π₀ : AlgebraicClosure ℚ)⁻¹ := by
      have e := congrArg Subtype.val hw
      change (π₀ : AlgebraicClosure ℚ) * (w : AlgebraicClosure ℚ) = 1 at e
      exact (eq_inv_of_mul_eq_one_right e)
    have hinvA : ((π₀⁻¹ : ↥k₀) : AlgebraicClosure ℚ) ∈ A := by
      push_cast; rw [← hwval]; exact w.2
    have hunit' : IsUnit (⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨π₀⁻¹, hinvA⟩, Subtype.ext ?_⟩
      show π₀ * π₀⁻¹ = 1
      exact mul_inv_cancel₀ (fun h => hπ0 (by rw [h]; rfl))
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hπcomap)) hunit'

  obtain rfl : E₀ = E₁ := Eq.symm <| by
    obtain ⟨v₁, hv₁, hv₁i, he₁⟩ := hmod₁
    obtain ⟨v, hv, hvi, he⟩ := hmod
    have he₁' := congrArg (fun x : ↥k₀ => (x : AlgebraicClosure ℚ)) he₁
    have he' := congrArg (fun x : ↥k₀ => (x : AlgebraicClosure ℚ)) he
    push_cast at he₁' he'
    exact nc1_pow_exp_unique A hπ hπmax hπ0 hv₁ (by push_cast at hv₁i ⊢; exact hv₁i) hv (by push_cast at hvi ⊢; exact hvi) he₁' he'

  have hfracO : ∀ f : ↥F₀, ∃ g h : ↥F₀, g ∈ O ∧ h ∈ O ∧ h ≠ 0 ∧ f * h = g := fun f => by
    obtain ⟨g, h, hg, hh, h0, e⟩ := hfrac f
    exact ⟨g, h, (hBxBO g hg).2, (hBxBO h hh).2, h0, e⟩

  obtain ⟨nd, hndrat, hC1, hC2, hC3, hRcy, hRcx⟩ :=
    ModularCurve.FullLevel.exists_centrePlace_ord_residue_eq_one_of_node_crossingPresentation q hq M' hqM' A hA k₀ π₀ hπ hdvr hunif hhens hres hκ
      F₀ hK1 hLD W₀ ⟨h2a, h2b, h2c⟩ O hN1W hN1k hN1res hfracO E₀ hE₁ hπO cx cy u ιO γU γV hxy hconst hιcx hιcy hcyW hcyM hcxM FSS R hRW

  obtain ⟨FI, instFI, instAlgFI, Rx, bx, hTR, hbxrat, hI1, hI2, hI3, hRxcx, hRxcy, hIGINT, hIGOVER⟩ :=
    ModularCurve.FullLevel.exists_branchPlace_igusaEnd_integral_overS_of_node_crossingPresentation_igusaBranch q hq M' hqM' A hA W hW hle R₀ hR₀ s
      (ModularCurve.mem_iff_mem_constantReduction_integers_of_jq_mem_residuallyTranscendental q M' hqM' A hA R₀ hR₀)
      k₀ π₀ hπ hdvr hunif hhens hres hκ
      F₀ hK1 hLD W₀ ⟨h2a, h2b, h2c⟩ O hN1W hN1k hN1res hfracO E₀ hE₁ hπO cx cy u ιO γU γV hxy hconst hιcx hιcy hcyW hcyM hcxM
      Wx hOWx hWxk hWxdvr hWxunif hWxtr hcxWx hcyWx hWxM' FSS R hRW
  letI : Field FI := instFI
  letI : Algebra (ResidueField ↥A) FI := instAlgFI

  obtain ⟨S, hS⟩ : ∃ S : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S ↔
      (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ P.toValuationSubring) ∧
      (∀ (f : ↥F₀) (hfO : f ∈ O), ¬ IsUnit (⟨f, hfO⟩ : ↥O) →
        ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) :=
    ⟨{P | (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ P.toValuationSubring) ∧
      (∀ (f : ↥F₀) (hfO : f ∈ O), ¬ IsUnit (⟨f, hfO⟩ : ↥O) →
        ∃ h : P.evalAt (f : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A)}, fun P => Iff.rfl⟩

  have hratAll : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational := by
    intro P
    haveI := (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')).1
    haveI : Module.Finite (AlgebraicClosure ℚ) P.ResidueField := AlgebraicCurve.IsCurveOver.finiteResidue P
    haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) P.ResidueField := Algebra.IsIntegral.of_finite _ _
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure ℚ) (K := P.ResidueField)).2
  have hSrat : ∀ P ∈ S, P.IsRational := fun P _ => hratAll P

  have hS7 : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S ↔
      (∀ f : ↥F₀, f ∈ O → ((f : ↥(fieldBar q M')) ∈ P.toValuationSubring)) ∧
      (∀ f : ↥O, ¬ IsUnit f → ∃ h : P.evalAt (((f : ↥F₀)) : ↥(fieldBar q M')) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A) := by
    intro P
    rw [hS P]
    exact ⟨fun h => ⟨h.1, fun f hf => h.2 f.1 f.2 hf⟩, fun h => ⟨h.1, fun f hfO hf => h.2 ⟨f, hfO⟩ hf⟩⟩
  have hP7 := ModularCurve.FullLevel.evalAt_mem_of_mem_integers_igusaEnd_of_forall_mem_nodePlaces q hq M' hqM' A hA k₀ π₀ hπ hdvr hunif hhens hres hκ
      F₀ hK1 hLD W₀ ⟨h2a, h2b, h2c⟩ O hN1W hN1k hN1res hfracO E₀ hE₁ hπO cx cy u ιO γU γV hxy hconst hιcx hιcy hcyW hcyM hcxM
      Wx hOWx hWxk hWxdvr hWxunif hcxWx hcyWx FSS R hRW FI Rx hTR S hS7

  obtain ⟨𝒩, h𝒩⟩ : ∃ 𝒩 : Subring ↥(fieldBar q M'), ∀ f : ↥(fieldBar q M'),
      f ∈ 𝒩 ↔ f ∈ Rx.integers ∧ f ∈ R.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring :=
    ⟨{ carrier := {f | f ∈ Rx.integers ∧ f ∈ R.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring}
       mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, mul_mem ha.2.1 hb.2.1, fun P hP => mul_mem (ha.2.2 P hP) (hb.2.2 P hP)⟩
       one_mem' := ⟨one_mem _, one_mem _, fun P _ => one_mem _⟩
       add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, add_mem ha.2.1 hb.2.1, fun P hP => add_mem (ha.2.2 P hP) (hb.2.2 P hP)⟩
       zero_mem' := ⟨zero_mem _, zero_mem _, fun P _ => zero_mem _⟩
       neg_mem' := fun {a} ha => ⟨neg_mem ha.1, neg_mem ha.2.1, fun P hP => neg_mem (ha.2.2 P hP)⟩ }, fun f => Iff.rfl⟩
  have h𝒩val : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A := fun f hf P hP =>
    hP7 f ((h𝒩 f).1 hf).1 ((h𝒩 f).1 hf).2.1 ((h𝒩 f).1 hf).2.2 P hP

  obtain ⟨𝒩₀L, hlocL, hnoethL, hLINK1, hLINK2, hgen, hLAY⟩ :=
    ModularCurve.FullLevel.exists_layeredRationalNodeRings_of_node_ends_layers q hq M' hqM' A hA k₀ π₀ hπ hdvr hunif hhens hres hκ K hKfin An hAn n₀ hn₀
      F₀ hK1 hLD W₀ ⟨h2a, h2b, h2c⟩ O hN1W hN1k hN1res hfracO E₀ hE₁ hπO cx cy u ιO γU γV hxy hconst hιcx hιcy hcyW hcyM hcxM
      hJK a₀ hjF hjO eJ wV heJ hgerm Bx (fun f hf => (hBxBO f hf).2) hOloc hBxfg
      FI Rx bx hbxrat (fun f hf => (hTR f).2 (hOWx f hf)) hI1 hI2 hRxcx hRxcy
      FSS R nd hRW hndrat hC1 hC2 hRcy hRcx S hS hSrat 𝒩 h𝒩 h𝒩val
      C' hC'A ϖ' Wc π eL jc hLP hϖker hCle hπirr hram hjϖ hjinj hjsur

  obtain ⟨v₀, hv₀, hv₀i, hπv⟩ := hram n₀
  have hv₀0 : v₀ ≠ 0 := by
    intro h0; apply hπ0; rw [hπv, h0, zero_mul]

  have evalAt_sub : ∀ (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')) (x y : ↥(fieldBar q M'))
      (hx : x ∈ P.toValuationSubring) (hy : y ∈ P.toValuationSubring),
      P.evalAt (x - y) = P.evalAt x - P.evalAt y := by
    intro P x y hx hy
    apply P.algebraMap_residueField_injective
    rw [map_sub, P.algebraMap_evalAt (hratAll P) hx, P.algebraMap_evalAt (hratAll P) hy,
      P.algebraMap_evalAt (hratAll P) (sub_mem hx hy), ← map_sub]
    rfl
  refine ⟨nd, FI, instFI, instAlgFI, Rx, bx, Wx, S, 𝒩, 𝒩₀L, hlocL, hnoethL,
    ((cx : ↥F₀) : ↥(fieldBar q M')), ((cy : ↥F₀) : ↥(fieldBar q M')),
    algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (v₀ ^ E₀) * ((((u : ↥O) : ↥F₀)) : ↥(fieldBar q M')),
    hndrat, hTR, hOWx, ?_, ?_, ?_, ⟨hO, hLINK1, fun f hf hN => hLINK2 f hf hN, hS, hC1, hC2, hC3⟩,
    hbxrat, hndrat, hSrat, h𝒩, h𝒩val, ?_, hRxcx, hRcx, hRcy, hRxcy, ?_, ?_, hgen, ?_, ?_, hIGINT, hIGOVER⟩
  ·
    intro hπW
    obtain ⟨hπW', e⟩ := hWxunif
    rw [e]; exact Ideal.mem_span_singleton_self _
  ·
    refine ⟨(cy : ↥F₀), cy.2, rfl, hcyWx, ?_⟩
    intro V hOV hπV hcyV
    exact ModularCurve.FullLevel.igusaBranch_le_of_le_of_mem_maximalIdeal_of_not_mem_of_node_crossingPresentation q hq M' hqM' A hA k₀ π₀ hπ hdvr hunif hhens hres hκ
      F₀ W₀ ⟨h2a, h2b, h2c⟩ O hN1W hN1k hN1res hfracO E₀ hE₁ hπO cx cy u ιO γU γV hxy hconst hιcx hιcy
      Wx hOWx hWxdvr hWxunif hcxWx hcyWx V hOV hπV hcyV
  ·
    intro O' hO' hne
    obtain ⟨-, instLoc', -⟩ := hpernode O' hO'
    haveI : IsLocalRing ↥O' := instLoc'
    obtain ⟨Bc, -, hBc⟩ := hNCOMMON
    obtain ⟨g, hg, hg', ⟨w, hw, hgw⟩, hgu⟩ := ModularCurve.FullLevel.exists_mem_eq_cx_mul_unit_isUnit_of_commonChart_of_igusaSep q hq M' hqM' A hA k₀ π₀ hπ hdvr hunif hhens hres hκ
      F₀ W₀ ⟨h2a, h2b, h2c⟩ O hN1W hN1k hN1res hfracO E₀ hE₁ hπO cx cy u ιO γU γV hxy hconst hιcx hιcy
      Wx hOWx hWxdvr hWxunif hcxWx hcyWx O' Bc (hBc O hO).1 (hBc O' hO').1 (hBc O hO).2 (hBc O' hO').2 (hIGSEP O' hO' hne)
    exact ⟨g, hg, hg', ⟨(cx : ↥F₀), cx.2, (w : ↥F₀), w.2, rfl, hw, congrArg Subtype.val hgw⟩, hgu⟩
  ·
    have e1 := congrArg (fun z : ↥O => ((z : ↥F₀) : ↥(fieldBar q M'))) hxy
    have hcoe : ((algebraMap ↥k₀ ↥F₀ π₀ : ↥F₀) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (π₀ : AlgebraicClosure ℚ) := rfl
    have e2 : ((cx : ↥F₀) : ↥(fieldBar q M')) * ((cy : ↥F₀) : ↥(fieldBar q M')) =
        ((algebraMap ↥k₀ ↥F₀ π₀ : ↥F₀) : ↥(fieldBar q M')) ^ E₀ * ((((u : ↥O) : ↥F₀)) : ↥(fieldBar q M')) := by
      have e1' := e1
      push_cast at e1' ⊢
      try exact_mod_cast e1'
    rw [e2, hcoe, hπv]
    simp only [map_mul, map_pow]
    ring
  ·
    intro τ hτI hχ
    have hτk : ∀ x : ↥k₀, τ (x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := fun x =>
      htame τ hτI hχ (algebraMap ↥k₀ ↥(K n₀) x)
    have hτD : τ ∈ A.decompositionSubgroup ℚ := by
      obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hτI
      exact σ.2
    have hfix : ∀ f : ↥F₀, ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')) = (f : ↥(fieldBar q M')) := by
      intro f
      apply ModularCurve.arithmeticGalois_smul_eq_self_of_forall_coeff_eq
      intro n
      obtain ⟨c, hc⟩ := (hCHAR (f : ↥(fieldBar q M'))).1 f.2 n
      rw [hc]; exact hτk c
    have hSinv := ModularCurve.FullLevel.mem_nodePlaces_iff_smul_mem_of_arithmeticGalois_smul_eq_of_mem_decompositionSubgroup q M' A k₀ F₀ O S hS hratAll τ hτD (fun f _ => hfix f)
    exact ⟨hSinv, hfix _, hfix _⟩
  ·
    intro f
    obtain ⟨m, c, a, b, hb0, hfb⟩ := hgen f
    obtain ⟨l, hl⟩ := hKcof (Finset.univ.image c)
    have hc : ∀ i, ∃ y : ↥(K l), (y : AlgebraicClosure ℚ) = c i := fun i => by
      obtain ⟨y, hy⟩ := hl (c i) (Finset.mem_image_of_mem c (Finset.mem_univ i))
      exact ⟨y, hy⟩
    choose y hy using hc
    obtain ⟨⟨d, hd⟩, hdint⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ↥(An l)) y
    have hd0 : (d : ↥(K l)) ≠ 0 := by
      have := nonZeroDivisors.ne_zero hd
      exact fun h => this (Subtype.ext h)
    obtain ⟨a1, -, -, a4, -⟩ := hLAY l

    obtain ⟨e, he⟩ : ∃ e : AlgebraicClosure ℚ, (((d : ↥(An l)) : ↥(K l)) : AlgebraicClosure ℚ) = e := ⟨_, rfl⟩
    have heC : e ∈ C' l := (hLP l e).2 ⟨he ▸ (hAn l _).1 d.2, ⟨_, he⟩⟩
    have he0 : e ≠ 0 := fun h => hd0 (ZeroMemClass.coe_eq_zero.mp (he.trans h))
    have heci : ∀ i, e * c i ∈ C' l := by
      intro i
      obtain ⟨z, hz⟩ : ∃ z : ↥(An l), algebraMap ↥(An l) ↥(K l) z = (d : ↥(An l)) • y i := hdint i
      have hz' : ((z : ↥(An l)) : ↥(K l)) = (d : ↥(K l)) * y i := by
        rw [Algebra.smul_def] at hz
        exact hz
      have hz'' : (((z : ↥(An l)) : ↥(K l)) : AlgebraicClosure ℚ) = e * c i := by
        rw [hz', ← hy i, ← he]; push_cast; rfl
      refine (hLP l _).2 ⟨?_, ⟨(z : ↥(An l)), hz''⟩⟩
      rw [← hz'']; exact (hAn l _).1 z.2
    refine ⟨l, ⟨∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (e * c i) * ((a i : ↥(𝒩₀L n₀)) : ↥(fieldBar q M')), ?_⟩,
      ⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') e * (b : ↥(fieldBar q M')), ?_⟩, ?_, ?_⟩
    · exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (a4 _ (heci i)) (a1 (a i).2)
    · exact Subring.mul_mem _ (a4 _ heC) (a1 b.2)
    · show algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') e * (b : ↥(fieldBar q M')) ≠ 0
      exact mul_ne_zero ((map_ne_zero _).2 he0) hb0
    · show f * (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') e * (b : ↥(fieldBar q M'))) =
        ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (e * c i) * ((a i : ↥(𝒩₀L n₀)) : ↥(fieldBar q M'))
      rw [mul_comm (algebraMap _ _ e), ← mul_assoc, hfb, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul]; ring
  ·
    intro l
    obtain ⟨a1, a2, a3, a4, a5, a6, ⟨Bxl, b1, b2, b3, b4, b5, b6⟩, c1, c2, ⟨hu, huU⟩, rest⟩ := hLAY l
    have hv₀l : v₀ ∈ C' l := hCle l hv₀
    have hv₀il : v₀⁻¹ ∈ C' l := hCle l hv₀i
    have hvN : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (v₀ ^ E₀) ∈ 𝒩₀L l := by
      rw [map_pow]; exact pow_mem (a4 _ hv₀l) _
    have hviN : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (v₀⁻¹ ^ E₀) ∈ 𝒩₀L l := by
      rw [map_pow]; exact pow_mem (a4 _ hv₀il) _
    have hvB : algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (v₀ ^ E₀) ∈ Bxl := by
      obtain ⟨T, hT⟩ := b6
      rw [map_pow]; refine pow_mem ?_ _
      rw [hT]; exact Subring.subset_closure (Or.inl ⟨v₀, hv₀l, rfl⟩)
    have hvunit : IsUnit (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (v₀ ^ E₀), hvN⟩ : ↥(𝒩₀L l)) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (v₀⁻¹ ^ E₀), hviN⟩, Subtype.ext ?_⟩
      show algebraMap _ _ (v₀ ^ E₀) * algebraMap _ _ (v₀⁻¹ ^ E₀) = 1
      rw [← map_mul, ← mul_pow, mul_inv_cancel₀ hv₀0, one_pow, map_one]
    refine ⟨a1, a2, a3, a4, a5, a6, ⟨Bxl, b1, b2, b3, Subring.mul_mem _ hvB b4, b5, b6⟩, c1, c2,
      ⟨Subring.mul_mem _ hvN hu, ?_⟩, rest⟩
    have := hvunit.mul huU
    exact this
  ·
    intro P hP f hf hreg hfs a ha
    obtain ⟨hmemO, hmaxO⟩ := (hS P).mp hP
    refine ModularCurve.FullLevel.tube_of_isRational_of_forall_rational_cuspRegular_evalAt_sub_mem_maximalIdeal q M' hqM' A hA W hW hle R₀ hR₀ s P (hratAll P) ?_ f hf hreg hfs a ha
    intro g hg hgi hgreg hgs
    obtain ⟨hF, -, -, hval⟩ := hWxM' g hg hgi hgreg
    obtain ⟨hgO, hnon⟩ := hval hgs
    refine ⟨hmemO _ hgO, fun a ha => ?_⟩
    obtain ⟨c, hcA, hm, hcm⟩ := hκ (a : AlgebraicClosure ℚ) a.2
    have hcO : algebraMap ↥k₀ ↥F₀ c ∈ O := (hN1k c).1 hcA
    have hres : residue ↥A ⟨(c : AlgebraicClosure ℚ), hcA⟩ =
        (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hgi⟩) := by
      rw [← ha]
      apply Eq.symm
      apply Ideal.Quotient.eq.mpr
      exact hcm
    have hnu := hnon hgO c hcA hcO hres
    have hsubO : (⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c ∈ O := Subring.sub_mem _ hgO hcO
    have hnu' : ¬ IsUnit (⟨_, hsubO⟩ : ↥O) := hnu
    obtain ⟨hdA, hdmax⟩ := hmaxO _ hsubO hnu'
    have hgP : ((⟨_, hF⟩ : ↥F₀) : ↥(fieldBar q M')) ∈ P.toValuationSubring := hmemO _ hgO
    have hcP : ((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) ∈ P.toValuationSubring := hmemO _ hcO
    have hcoe : ((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) := rfl
    have hevc : P.evalAt ((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) = (c : AlgebraicClosure ℚ) := by
      rw [hcoe]; exact P.evalAt_algebraMap _
    have hev : P.evalAt (((⟨_, hF⟩ : ↥F₀) - algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) =
        P.evalAt (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : fieldBar q M') - (c : AlgebraicClosure ℚ) := by
      rw [← hevc, ← evalAt_sub P _ _ hgP hcP]; rfl

    have key : P.evalAt (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : fieldBar q M') - (a : AlgebraicClosure ℚ) =
        (P.evalAt (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : fieldBar q M') - (c : AlgebraicClosure ℚ)) - ((a : AlgebraicClosure ℚ) - c) := by ring
    rw [← hev] at key
    have hmemA : P.evalAt (IntermediateField.inclusion hle ⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A := by
      rw [key]; exact sub_mem hdA hm
    refine ⟨hmemA, ?_⟩
    have hsplit : (⟨_, hmemA⟩ : ↥A) = ⟨_, hdA⟩ - ⟨_, hm⟩ := Subtype.ext key
    rw [hsplit]; exact Ideal.sub_mem _ hdmax hcm

end S_ModularCurve_FullLevel_exists_nodeCentre_igusaEnd_layeredNodeRings_of_mem_nodes_igusaSep_layerExponent
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_nodeCentre_igusaEnd_layeredNodeRings_of_mem_nodes_igusaSep_layerExponent (solution)
