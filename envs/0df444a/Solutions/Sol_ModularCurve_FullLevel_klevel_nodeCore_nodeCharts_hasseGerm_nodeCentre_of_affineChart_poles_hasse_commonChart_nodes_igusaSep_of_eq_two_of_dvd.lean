-- Prove2me | solution 1 for ModularCurve.FullLevel.klevel_nodeCore_nodeCharts_hasseGerm_nodeCentre_of_affineChart_poles_hasse_commonChart_nodes_igusaSep_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/a0d80a8a-6b71-5c00-9d69-591f544f0467

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
import Theorems.Thm_ModularCurve_FullLevel_exists_nodeCentre_igusaEnd_layeredNodeRings_of_mem_nodes_igusaSep_layerExponent_of_prime_of_width
import Theorems.Thm_ModularCurve_FullLevel_exists_layerConstants_uniformizers_completions_of_constantsTower
import Theorems.Thm_ModularCurve_FullLevel_levelAut_transport_nodePlaces_igusaEnds_of_nodeCentre_igusaBranch_of_prime_of_width
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_klevel_nodeCore_nodeCharts_hasseGerm_nodeCentre_of_affineChart_poles_hasse_commonChart_nodes_igusaSep_of_eq_two_of_dvd
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

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 0 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
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
            Nat.card Cs = placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) ∧
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
                  π₀ ^ E₀ = ϖt ^ (placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) * v)
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
        ∃ (N : Finset (Place (ResidueField A) FSS)),

          N.card = q + 1 ∧
        ∃
          (FIx : Place (ResidueField A) FSS → Type) (_ : ∀ x, Field (FIx x)) (_ : ∀ x, Algebra (ResidueField A) (FIx x))
          (Rx : ∀ x : Place (ResidueField A) FSS, RegularProlongation A (fieldBar q M') (FIx x))
          (bx : ∀ x : Place (ResidueField A) FSS, Place (ResidueField A) (FIx x))

          (C' : ι → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : ι) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
          (_ : ∀ l, IsDomain ↥(C' l)) (_ : ∀ l, IsDiscreteValuationRing ↥(C' l))
          (ϖ' : ∀ l, ↥(C' l))
          (Wc : ι → Type) (_ : ∀ l, CommRing (Wc l)) (_ : ∀ l, IsDomain (Wc l)) (_ : ∀ l, IsDiscreteValuationRing (Wc l))
          (_ : ∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l))
          (π : ∀ l, Wc l) (E : ι → ℕ) (E₀ : ℕ)

          (S : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
          (𝒩 : Place (ResidueField A) FSS → Subring (fieldBar q M'))
          (𝒩₀ : Place (ResidueField A) FSS → ι → Subring (fieldBar q M'))
          (hloc : ∀ nd l, IsLocalRing ↥(𝒩₀ nd l)) (hnoe : ∀ nd l, IsNoetherianRing ↥(𝒩₀ nd l))
          (cx cy cu : Place (ResidueField A) FSS → fieldBar q M'),

          (∀ (n : ι) (c : AlgebraicClosure ℚ), c ∈ C' n ↔ c ∈ A ∧ c ∈ Set.range (fun x : ↥(K n) => (x : AlgebraicClosure ℚ))) ∧

          (∀ (l : ι) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d') ∧
          (∀ l, C' n₀ ≤ C' l) ∧
          ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) ≠ 0 ∧
          (∀ a : AlgebraicClosure ℚ, a ∈ A → IsAlgebraic ↥(C' n₀) a) ∧
          (∀ l, Irreducible (π l)) ∧ (∀ l, 1 ≤ E l) ∧

          (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 →
            τ ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) = ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ)) ∧

          (∃ w : ℕ, 1 ≤ w ∧ ∃ v : (↥A)ˣ,
            (⟨((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ), hC'A n₀ _ (ϖ' n₀).2⟩ : ↥A) ^ E₀ = (v : ↥A) * ⟨πt, hπA⟩ ^ w) ∧

          (∀ nd ∈ N,

            (∃ O ∈ nodes,
              (∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ 𝒩₀ nd n₀) ∧
              (∀ (f : ↥F₀) (hf : f ∈ O) (hN : (f : ↥(fieldBar q M')) ∈ 𝒩₀ nd n₀),
                ¬ IsUnit (⟨f, hf⟩ : ↥O) → ¬ IsUnit (⟨(f : ↥(fieldBar q M')), hN⟩ : ↥(𝒩₀ nd n₀))) ∧

              (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ S nd ↔
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

            (bx nd).IsRational ∧ nd.IsRational ∧ (∀ P ∈ S nd, P.IsRational) ∧

            (∀ f : fieldBar q M', f ∈ 𝒩 nd ↔ f ∈ (Rx nd).integers ∧ f ∈ R.integers ∧ ∀ P ∈ S nd, f ∈ P.toValuationSubring) ∧
            (∀ f ∈ 𝒩 nd, ∀ P ∈ S nd, P.evalAt f ∈ A) ∧

            cx nd * cy nd = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' n₀ : ↥(C' n₀)) : AlgebraicClosure ℚ) ^ E₀ * cu nd ∧
            (∀ h₁ : cx nd ∈ (Rx nd).integers, (Rx nd).residue ⟨cx nd, h₁⟩ = 0) ∧
            (∀ h₂ : cx nd ∈ R.integers, nd.ord (R.residue ⟨cx nd, h₂⟩) = 1) ∧
            (∀ h₂ : cy nd ∈ R.integers, R.residue ⟨cy nd, h₂⟩ = 0) ∧
            (∀ h₁ : cy nd ∈ (Rx nd).integers, (bx nd).ord ((Rx nd).residue ⟨cy nd, h₁⟩) = 1) ∧

            (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter πt τ = 1 →
              let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S nd ↔ g • P ∈ S nd) ∧ g • cx nd = cx nd ∧ g • cy nd = cy nd) ∧

            (∀ f : fieldBar q M', ∃ (l : ι) (a b : ↥(𝒩₀ nd l)), (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = (a : fieldBar q M')) ∧

            (∀ f : fieldBar q M', ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd n₀)) (b : ↥(𝒩₀ nd n₀)),
              (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = ∑ i, c i • ((a i : ↥(𝒩₀ nd n₀)) : fieldBar q M')) ∧

            (∀ l, letI : IsLocalRing ↥(𝒩₀ nd l) := hloc nd l;
              𝒩₀ nd n₀ ≤ 𝒩₀ nd l ∧ 𝒩₀ nd l ≤ 𝒩 nd ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S nd ↔
                (∀ f : fieldBar q M', f ∈ 𝒩₀ nd l → f ∈ P.toValuationSubring) ∧
                (∀ f : ↥(𝒩₀ nd l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
              (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀ nd l) ∧
              (∀ g : ↥(𝒩₀ nd l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
              (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd l)), LinearIndependent ↥(C' l) c →
                ∑ i, c i • ((a i : ↥(𝒩₀ nd l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧

              (∃ Bx : Subring (fieldBar q M'),
                (∀ f : fieldBar q M', f ∈ Bx → f ∈ 𝒩₀ nd l) ∧
                cx nd ∈ Bx ∧ cy nd ∈ Bx ∧ cu nd ∈ Bx ∧
                (∀ f : fieldBar q M', f ∈ 𝒩₀ nd l ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
                  (∀ hh : h ∈ 𝒩₀ nd l, IsUnit (⟨h, hh⟩ : ↥(𝒩₀ nd l))) ∧ f * h = g) ∧
                (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
                  ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
                    (↑T : Set (fieldBar q M'))))) ∧
              cx nd ∈ 𝒩₀ nd l ∧ cy nd ∈ 𝒩₀ nd l ∧ (∃ hu : cu nd ∈ 𝒩₀ nd l, IsUnit (⟨cu nd, hu⟩ : ↥(𝒩₀ nd l))) ∧
              ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l))
                (ιc : AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l) ≃+* UVCrossingModel (Wc l) (π l ^ E l)),
                (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l,
                  σ (π l) = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ o : Wc l, ιc (σ o) = const (π l ^ E l) o) ∧

                (∃ (hJ : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a₀ : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l)
                   (e : ℕ) (w : (UVCrossingModel (Wc l) (π l ^ E l))ˣ), 1 ≤ e ∧
                  ιc (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, hJ⟩) =
                    (w : UVCrossingModel (Wc l) (π l ^ E l)) * V (π l ^ E l) ^ e) ∧
                (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l),
                  ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₁ : f.1 ∈ (Rx nd).integers), (Rx nd).residue ⟨f.1, h₁⟩ ≠ 0 →
                  (bx nd).ord ((Rx nd).residue ⟨f.1, h₁⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (π l ^ E l), IsUnit γ ∧
                      ιc (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * V (π l ^ E l) ^ n ∈
                        Ideal.span {const (π l ^ E l) (π l), U (π l ^ E l)}) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
                  nd.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (π l ^ E l), IsUnit γ ∧
                      ιc (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * U (π l ^ E l) ^ n ∈
                        Ideal.span {const (π l ^ E l) (π l), V (π l ^ E l)}))) ∧

          (∀ nd ∈ N, ∀ nd' ∈ N, ∀ P, P ∈ S nd → P ∈ S nd' → nd = nd') ∧

          (∀ nd ∈ N, ∀ P ∈ S nd, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
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

          (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∃ τN : Place (ResidueField A) FSS → Place (ResidueField A) FSS,
            ∀ nd ∈ N, τN nd ∈ N ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), (levelAutBar q M' ζ' γ) • P ∈ S nd ↔ P ∈ S (τN nd)) ∧
              ((Rx nd).integers).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = (Rx (τN nd)).integers) ∧

          (∀ τ ∈ Subgroup.closure {τ : (fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] (fieldBar q M') |
                ∃ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ' γ},
            ∀ (hτ : ∀ f : fieldBar q M', τ f ∈ R.integers ↔ f ∈ R.integers), ∀ nd ∈ N,
              R.resAut τ hτ • nd ∈ N ∧
              AlgebraicCurve.RegularProlongation.smulDisc τ (S nd) = S (R.resAut τ hτ • nd)) ∧

          (∀ nd ∈ N, ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ (Rx nd).integers) ∧

          (∀ nd ∈ N, ∃ j : modularFunctionFieldC (ResidueField A) M' →+* FIx nd,
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ (Rx nd).integers,
                (Rx nd).residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
            ∀ g : modularFunctionFieldC (ResidueField A) M',
              g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
                j g ∈ (bx nd).toValuationSubring) ∧

          (∀ x ∈ N, ∀ x' ∈ N, x ≠ x' →
                ∃ (g : ↥(fieldBar q M')) (hgx : g ∈ 𝒩₀ x n₀) (hcx : cx x ∈ 𝒩₀ x n₀) (hgx' : g ∈ 𝒩₀ x' n₀),
                  (∃ u : (↥(𝒩₀ x n₀))ˣ, (⟨g, hgx⟩ : ↥(𝒩₀ x n₀)) = ⟨cx x, hcx⟩ * (u : ↥(𝒩₀ x n₀))) ∧
                  IsUnit (⟨g, hgx'⟩ : ↥(𝒩₀ x' n₀)))) := by
  intro F₀ hF₀ W₀ B alg hjR hjs hJK a₀ ha₀ hpin nodes hANT FSS _ _ R hRW
  have hANT' := hANT
  obtain ⟨h2a, h2b, h2c, h4, h5W, hM1, hM0a, hM0b, hM4a, hM4b, hM4c, hM2a, hM2b, hM2c, hM5a, hM5b, hE1p, hE3, hM3, hNrest⟩ := hANT
  have hnodescard := hNrest.1
  have hNCOMMON := hNrest.2.1
  have hNEQV := hNrest.2.2.1
  have hNEQV2 := hNrest.2.2.2.1
  have hNSEP := hNrest.2.2.2.2.1
  have hCOVER := hNrest.2.2.2.2.2.1
  have hpernode := hNrest.2.2.2.2.2.2
  classical

  have hpos : 0 < nodes.card := by rw [hnodescard]; omega
  obtain ⟨O₀, hO₀⟩ := Finset.card_pos.mp hpos
  have hpo₀ := hpernode O₀ hO₀
  obtain ⟨-, -, -, -, -, E₀, hE₀, hmod, -⟩ := hpo₀

  have hLD := ModularCurve.FullLevel.exists_layerConstants_uniformizers_completions_of_constantsTower q A hA k₀ π₀ hπ hdvr hunif hhens hres hκ ϖt hϖtA hϖt K hKfin An hAn n₀ hn₀ πt hπt hπA htame E₀ hE₀ _ hmod
  obtain ⟨C', hC'A, iCD, iCV, ϖ', Wc, iW1, iW2, iW3, iW4, π, eL, jc, hLP, hϖker, hCle, hϖ0, halg, hπirr, heLpos, htamefix, hmodulus, hram, hjϖ, hjinj, hjsur⟩ := hLD
  haveI : ∀ l, IsDomain ↥(C' l) := iCD
  haveI : ∀ l, IsDiscreteValuationRing ↥(C' l) := iCV
  letI : ∀ l, CommRing (Wc l) := iW1
  haveI : ∀ l, IsDomain (Wc l) := iW2
  haveI : ∀ l, IsDiscreteValuationRing (Wc l) := iW3
  haveI : ∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l) := iW4

  have hNC1 : ∀ O ∈ nodes, _ := fun O hO =>
    ModularCurve.FullLevel.exists_nodeCentre_igusaEnd_layeredNodeRings_of_mem_nodes_igusaSep_layerExponent_of_prime_of_width q M' hqM' A hA W hW hle R₀ hR₀ s
      (placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) k₀ π₀ hπ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt K hKfin An hAn n₀ hn₀ hKcof πt hπt hπA htame Kb hKb Ab hAb ϖb hϖb hϖb0
      F₀ hF₀ W₀ B alg hjR hjs hJK a₀ ha₀ hpin nodes hANT' FSS R hRW O hO E₀ hE₀ hmod C' hC'A ϖ' Wc π eL jc hLP hϖker hCle hπirr hram hjϖ hjinj hjsur

  let ndOf : {O // O ∈ nodes} → Place (ResidueField ↥A) FSS := fun O => (hNC1 O.1 O.2).choose
  have hrest : ∀ O : {O // O ∈ nodes}, _ := fun O => (hNC1 O.1 O.2).choose_spec
  let N : Finset (Place (ResidueField ↥A) FSS) := nodes.attach.image ndOf

  have hcen : ∀ O : {O // O ∈ nodes},
      (∀ (f : ↥F₀) (_ : f ∈ O.1) (hR : (f : ↥(fieldBar q M')) ∈ R.integers), R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ (ndOf O).toValuationSubring) ∧
      (∀ (f : ↥F₀) (hf : f ∈ O.1) (hR : (f : ↥(fieldBar q M')) ∈ R.integers), ¬ IsUnit (⟨f, hf⟩ : ↥O.1) →
        ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ (ndOf O).toValuationSubring,
          (⟨_, hm⟩ : ↥(ndOf O).toValuationSubring) ∈ maximalIdeal ↥(ndOf O).toValuationSubring) := by
    intro O
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, c1, c2, -⟩, -⟩ := hrest O
    exact ⟨c1, c2⟩
  have hN1W : ∀ O : {O // O ∈ nodes}, ∀ f : ↥F₀, f ∈ O.1 → f ∈ W₀ := fun O => (hpernode O.1 O.2).1
  have hunitres : ∀ (O : {O // O ∈ nodes}) (f : ↥F₀) (hf : f ∈ O.1) (hR : (f : ↥(fieldBar q M')) ∈ R.integers),
      IsUnit (⟨f, hf⟩ : ↥O.1) → ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ (ndOf O).toValuationSubring,
        IsUnit (⟨_, hm⟩ : ↥(ndOf O).toValuationSubring) := by
    intro O f hf hR hu
    obtain ⟨c1, -⟩ := hcen O
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
    have hbR : (((b : ↥O.1) : ↥F₀) : ↥(fieldBar q M')) ∈ R.integers := (hRW _).mpr (hN1W O _ b.2)
    have hm := c1 f hf hR
    have hmb := c1 _ b.2 hbR
    refine ⟨hm, isUnit_iff_exists_inv.mpr ⟨⟨_, hmb⟩, Subtype.ext ?_⟩⟩
    show R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ * R.residue ⟨_, hbR⟩ = 1
    rw [← map_mul]
    have : (⟨(f : ↥(fieldBar q M')), hR⟩ : ↥R.integers) * ⟨_, hbR⟩ = 1 := by
      apply Subtype.ext
      have e := congrArg (fun z : ↥O.1 => ((z : ↥F₀) : ↥(fieldBar q M'))) hb
      simpa using e
    rw [this, map_one]
  have hinj : Function.Injective ndOf := by
    intro O O' h
    by_contra hne
    have hne' : O.1 ≠ O'.1 := fun e => hne (Subtype.ext e)
    obtain ⟨f, hfO, hfO', hnu, hu⟩ := hNSEP O.1 O.2 O'.1 O'.2 hne'
    obtain ⟨-, c2⟩ := hcen O
    have hR : (f : ↥(fieldBar q M')) ∈ R.integers := (hRW f).mpr (hN1W O f hfO)
    obtain ⟨hm, hmax⟩ := c2 f hfO hR hnu
    have key := hunitres O' f hfO' hR hu
    rw [← h] at key
    obtain ⟨hm', hu'⟩ := key
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax hu'
  have hNcard : N.card = q + 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, hnodescard]
  have D' : ∀ nd : Place (ResidueField ↥A) FSS,
          ∃ (FI : Type) (_ : Field FI) (_ : Algebra (ResidueField ↥A) FI)
            (Rx : RegularProlongation A ↥(fieldBar q M') FI) (bx : Place (ResidueField ↥A) FI)
            (Wx : ValuationSubring ↥F₀)
            (S : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))) (𝒩 : Subring ↥(fieldBar q M'))
            (𝒩₀L : ι → Subring ↥(fieldBar q M')) (hlocL : ∀ l, IsLocalRing ↥(𝒩₀L l)) (_ : ∀ l, IsNoetherianRing ↥(𝒩₀L l))
            (cx cy cu : ↥(fieldBar q M')),
            ∀ (O : Subring ↥F₀) (hO : O ∈ nodes), ndOf ⟨O, hO⟩ = nd →
            (          nd.IsRational ∧

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
    intro nd
    by_cases h : ∃ O : {O // O ∈ nodes}, ndOf O = nd
    · obtain ⟨O, rfl⟩ := h
      obtain ⟨FI, iF, iA, Rx, bx, Wx, S, 𝒩, 𝒩₀L, hl, hn, cx, cy, cu, props⟩ := hrest O
      refine ⟨FI, iF, iA, Rx, bx, Wx, S, 𝒩, 𝒩₀L, hl, hn, cx, cy, cu, ?_⟩
      intro O' hO' he
      have hOO : (⟨O', hO'⟩ : {O // O ∈ nodes}) = O := hinj he
      subst hOO
      exact props
    · obtain ⟨FI, iF, iA, Rx, bx, Wx, S, 𝒩, 𝒩₀L, hl, hn, cx, cy, cu, -⟩ := hrest ⟨O₀, hO₀⟩
      exact ⟨FI, iF, iA, Rx, bx, Wx, S, 𝒩, 𝒩₀L, hl, hn, cx, cy, cu, fun O' hO' he => absurd ⟨⟨O', hO'⟩, he⟩ h⟩

  choose FIx iFx iAx Rxx bxx Wxx Sx Nx N0x hlocx hnoex cxx cyx cux propsx using D'

  have hmemN : ∀ nd, nd ∈ N → ∃ (O : Subring ↥F₀) (hO : O ∈ nodes), ndOf ⟨O, hO⟩ = nd := by
    intro nd hnd
    obtain ⟨O, -, hO⟩ := Finset.mem_image.mp hnd
    exact ⟨O.1, O.2, hO⟩

  let Oof : Place (ResidueField ↥A) FSS → Subring ↥F₀ := fun nd => if h : ∃ O : {O // O ∈ nodes}, ndOf O = nd then h.choose.1 else O₀
  have hOof : ∀ nd ∈ N, ∃ hO : Oof nd ∈ nodes, ndOf ⟨Oof nd, hO⟩ = nd := by
    intro nd hnd
    obtain ⟨O, hO, he⟩ := hmemN nd hnd
    have h : ∃ O : {O // O ∈ nodes}, ndOf O = nd := ⟨⟨O, hO⟩, he⟩
    have : Oof nd = h.choose.1 := by simp only [Oof, dif_pos h]
    refine ⟨this ▸ h.choose.2, ?_⟩
    have e : (⟨Oof nd, this ▸ h.choose.2⟩ : {O // O ∈ nodes}) = h.choose := Subtype.ext this
    rw [e]; exact h.choose_spec
  have hOmem : ∀ nd ∈ N, Oof nd ∈ nodes := fun nd hnd => (hOof nd hnd).1
  have hOsurj : ∀ O ∈ nodes, ∃ nd ∈ N, Oof nd = O := by
    intro O hO
    refine ⟨ndOf ⟨O, hO⟩, Finset.mem_image.mpr ⟨⟨O, hO⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    obtain ⟨hO', he⟩ := hOof _ (Finset.mem_image.mpr ⟨⟨O, hO⟩, Finset.mem_attach _ _, rfl⟩)
    have := hinj he
    exact congrArg Subtype.val this
  have hOinj : ∀ nd ∈ N, ∀ nd' ∈ N, Oof nd = Oof nd' → nd = nd' := by
    intro nd hnd nd' hnd' h
    obtain ⟨hO, he⟩ := hOof nd hnd
    obtain ⟨hO', he'⟩ := hOof nd' hnd'
    rw [← he, ← he']
    congr 1
    exact Subtype.ext h
  have PX : ∀ nd ∈ N, _ := fun nd hnd => propsx nd (Oof nd) (hOof nd hnd).1 (hOof nd hnd).2
  letI : ∀ x, Field (FIx x) := iFx
  letI : ∀ x, Algebra (ResidueField ↥A) (FIx x) := iAx
  have hEQV := ModularCurve.FullLevel.levelAut_transport_nodePlaces_igusaEnds_of_nodeCentre_igusaBranch_of_prime_of_width q M' hqM' A hA W hW hle R₀ hR₀ s
      (placeWidthChar q M' (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))) k₀ π₀ hπ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt K hKfin An hAn n₀ hn₀ hKcof πt hπt hπA htame Kb hKb Ab hAb ϖb hϖb hϖb0
      F₀ hF₀ W₀ B alg hjR hjs hJK a₀ ha₀ hpin nodes hANT' FSS R hRW N Oof hOmem hOsurj hOinj Sx
      (fun nd hnd => (PX nd hnd).2.2.2.2.2.2.1.2.2.2.1)
      (fun nd hnd => ⟨(PX nd hnd).2.2.2.2.2.2.1.2.2.2.2.1, (PX nd hnd).2.2.2.2.2.2.1.2.2.2.2.2.1, (PX nd hnd).2.2.2.2.2.2.1.2.2.2.2.2.2⟩)
      FIx Rxx Wxx
      (fun nd hnd => (PX nd hnd).2.1) (fun nd hnd => (PX nd hnd).2.2.1) (fun nd hnd => (PX nd hnd).2.2.2.1)
      (fun nd hnd => by
        have PXn := PX nd hnd
        obtain ⟨-, -, -, -, hIG, -, -, -, -, -, -, -, -, -, -, a9, -⟩ := PXn
        obtain ⟨cyO, hcyO, hcoe, hnm, hV⟩ := hIG
        refine ⟨cyO, hcyO, hnm, ?_, hV⟩
        intro h₂
        have e : (⟨((cyO : ↥F₀) : ↥(fieldBar q M')), h₂⟩ : ↥R.integers) = ⟨cyx nd, hcoe ▸ h₂⟩ := Subtype.ext hcoe
        rw [e]; exact a9 _)
  have hEpos : ∀ l, 1 ≤ eL l * E₀ := fun l => Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := heLpos l; omega) (by omega))
  refine ⟨N, hNcard, FIx, iFx, iAx, Rxx, bxx, C', hC'A, iCD, iCV, ϖ', Wc, iW1, iW2, iW3, iW4, π, (fun l => eL l * E₀), eL n₀ * E₀,
    Sx, Nx, N0x, hlocx, hnoex, cxx, cyx, cux, hLP, hϖker, hCle, hϖ0, halg, hπirr, hEpos, htamefix, hmodulus, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro nd hnd
    obtain ⟨O, hO, he⟩ := hmemN nd hnd
    have P := propsx nd O hO he
    obtain ⟨-, -, -, -, -, -, hLINK, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, hlay, -, -, -⟩ := P
    exact ⟨⟨O, hLINK.1, hLINK.2⟩, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, hlay⟩
  ·
    intro nd hnd nd' hnd' P hP hP'
    obtain ⟨O, hO, he⟩ := hmemN nd hnd
    obtain ⟨O', hO', he'⟩ := hmemN nd' hnd'
    by_contra hne
    have hOO' : O ≠ O' := by
      rintro rfl
      exact hne (he.symm.trans he')
    obtain ⟨f, hfO, hfO', hnu, hu⟩ := hNSEP O hO O' hO' hOO'
    have Q := propsx nd O hO he
    have Q' := propsx nd' O' hO' he'
    obtain ⟨-, -, -, -, -, -, hLINK, -, -, hSr, -⟩ := Q
    obtain ⟨-, -, -, -, -, -, hLINK', -⟩ := Q'
    have hS := hLINK.2.2.2.1
    have hS' := hLINK'.2.2.2.1
    obtain ⟨hmemO, hmaxO⟩ := (hS P).mp hP
    obtain ⟨hmemO', -⟩ := (hS' P).mp hP'
    have hrat : P.IsRational := hSr P hP
    obtain ⟨hfA, hfmax⟩ := hmaxO f hfO hnu

    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hu
    have hfP : ((f : ↥F₀) : ↥(fieldBar q M')) ∈ P.toValuationSubring := hmemO f hfO
    have hbP : (((b : ↥O') : ↥F₀) : ↥(fieldBar q M')) ∈ P.toValuationSubring := hmemO' _ b.2
    have hprod : (⟨_, hfP⟩ : ↥P.toValuationSubring) * ⟨_, hbP⟩ = 1 := by
      apply Subtype.ext
      have e := congrArg (fun z : ↥O' => ((z : ↥F₀) : ↥(fieldBar q M'))) hb
      simpa using e
    have hinj := P.algebraMap_residueField_injective
    have key : P.evalAt ((f : ↥F₀) : ↥(fieldBar q M')) * P.evalAt (((b : ↥O') : ↥F₀) : ↥(fieldBar q M')) = 1 := by
      apply hinj
      rw [map_mul, map_one, P.algebraMap_evalAt hrat hfP, P.algebraMap_evalAt hrat hbP, ← map_mul, hprod, map_one]

    have hbA : P.evalAt (((b : ↥O') : ↥F₀) : ↥(fieldBar q M')) ∈ A := by

      by_cases hbu : IsUnit (b : ↥O')
      ·
        obtain ⟨-, -, -, hN1c', hN1r', -⟩ := hpernode O' hO'
        obtain ⟨c, hcO, hcA, hm⟩ := hN1r' _ b.2
        have hmO : (((b : ↥O') : ↥F₀) - algebraMap ↥k₀ ↥F₀ c) ∈ O' := Subring.sub_mem _ b.2 hcO
        have hm' : ¬ IsUnit (⟨_, hmO⟩ : ↥O') := by
          have : (⟨_, hmO⟩ : ↥O') = ⟨_, b.2⟩ - ⟨_, hcO⟩ := rfl
          rw [this]; exact hm
        obtain ⟨hmA, -⟩ := (hS' P |>.mp hP').2 _ hmO hm'
        have hcP : ((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) ∈ P.toValuationSubring := hmemO' _ hcO
        have hmP : ((((b : ↥O') : ↥F₀) - algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) ∈ P.toValuationSubring := hmemO' _ hmO
        have hcoe : ((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c : AlgebraicClosure ℚ) := rfl
        have hevc : P.evalAt ((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) = (c : AlgebraicClosure ℚ) := by
          rw [hcoe]; exact P.evalAt_algebraMap _
        have hsum : P.evalAt (((b : ↥O') : ↥F₀) : ↥(fieldBar q M')) =
            P.evalAt ((algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) + P.evalAt ((((b : ↥O') : ↥F₀) - algebraMap ↥k₀ ↥F₀ c : ↥F₀) : ↥(fieldBar q M')) := by
          apply hinj
          rw [map_add, P.algebraMap_evalAt hrat hbP, P.algebraMap_evalAt hrat hcP, P.algebraMap_evalAt hrat hmP, ← map_add]
          congr 1
          apply Subtype.ext; push_cast; ring
        rw [hsum, hevc]
        exact add_mem hcA hmA
      · obtain ⟨hA', -⟩ := (hS' P |>.mp hP').2 _ b.2 hbu
        exact hA'
    have : (⟨_, hfA⟩ : ↥A) * ⟨_, hbA⟩ = 1 := Subtype.ext key
    exact (IsLocalRing.mem_maximalIdeal _).mp hfmax (IsUnit.of_mul_eq_one _ this)
  ·
    intro nd hnd
    obtain ⟨O, hO, he⟩ := hmemN nd hnd
    have P := propsx nd O hO he
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htube, -, -⟩ := P
    exact htube
  ·
    exact hEQV.1
  ·
    exact hEQV.2
  ·
    intro nd hnd
    obtain ⟨O, hO, he⟩ := hmemN nd hnd
    have P := propsx nd O hO he
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hII, -⟩ := P
    exact hII
  ·
    intro nd hnd
    obtain ⟨O, hO, he⟩ := hmemN nd hnd
    have P := propsx nd O hO he
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hIO⟩ := P
    exact hIO
  ·
    intro x hx x' hx' hne
    obtain ⟨O, hO, he⟩ := hmemN x hx
    obtain ⟨O', hO', he'⟩ := hmemN x' hx'
    have hOO' : O' ≠ O := by
      rintro rfl
      exact hne (he.symm.trans he')
    have P := propsx x O hO he
    have P' := propsx x' O' hO' he'
    obtain ⟨-, -, -, -, -, hS2, hLINK, -⟩ := P
    obtain ⟨-, -, -, -, -, -, hLINK', -⟩ := P'
    have hsub : ∀ f : ↥F₀, f ∈ O → (f : ↥(fieldBar q M')) ∈ N0x x n₀ := hLINK.2.1
    have hsub' : ∀ f : ↥F₀, f ∈ O' → (f : ↥(fieldBar q M')) ∈ N0x x' n₀ := hLINK'.2.1

    have unitUp : ∀ (T : Subring ↥(fieldBar q M')) (O₁ : Subring ↥F₀) (hs : ∀ f : ↥F₀, f ∈ O₁ → (f : ↥(fieldBar q M')) ∈ T)
        (u : ↥F₀) (hu : u ∈ O₁), IsUnit (⟨u, hu⟩ : ↥O₁) → IsUnit (⟨(u : ↥(fieldBar q M')), hs u hu⟩ : ↥T) := by
      intro T O₁ hs u hu hU
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp hU
      refine isUnit_iff_exists_inv.mpr ⟨⟨((b : ↥O₁) : ↥F₀), hs _ b.2⟩, Subtype.ext ?_⟩
      have e := congrArg (fun z : ↥O₁ => ((z : ↥F₀) : ↥(fieldBar q M'))) hb
      simpa using e
    obtain ⟨g₀, hg, hg', ⟨c, hc, u, hu, hcx, hu1, hgcu⟩, hgu'⟩ := hS2 O' hO' hOO'
    have hcxmem : cxx x ∈ N0x x n₀ := hcx ▸ hsub c hc
    refine ⟨(g₀ : ↥(fieldBar q M')), hsub g₀ hg, hcxmem, hsub' g₀ hg', ?_, unitUp _ O' hsub' g₀ hg' hgu'⟩
    obtain ⟨uu, huu⟩ := unitUp _ O hsub u hu hu1
    refine ⟨uu, Subtype.ext ?_⟩
    have huu' : ((uu : ↥(N0x x n₀)) : ↥(fieldBar q M')) = ((u : ↥F₀) : ↥(fieldBar q M')) := by rw [huu]
    show ((g₀ : ↥F₀) : ↥(fieldBar q M')) = cxx x * ((uu : ↥(N0x x n₀)) : ↥(fieldBar q M'))
    rw [huu', hgcu, ← hcx]; push_cast; rfl

end S_ModularCurve_FullLevel_klevel_nodeCore_nodeCharts_hasseGerm_nodeCentre_of_affineChart_poles_hasse_commonChart_nodes_igusaSep_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_klevel_nodeCore_nodeCharts_hasseGerm_nodeCentre_of_affineChart_poles_hasse_commonChart_nodes_igusaSep_of_eq_two_of_dvd (solution)
