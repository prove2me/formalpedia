-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/5d68d86a-1901-5d0b-a3af-53f73aafd253

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_mem_ssPlaces_of_ne
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valueIntegralityLaw_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_le_mem_nodeIntegersOver_of_mem_nodeIntegers
import Definitions.Def_ModularCurve_NodeDepth
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_range_redRestrict_of_hasValue_nodeResidueFst
import Theorems.Thm_ModularCurve_exists_fieldOver_lift_isIntegral_of_isIntegral
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_heckeAlphaBar_mem_nodeIntegersOver_and_nodeResidue_eq_coeffMap
import Theorems.Thm_ModularCurve_forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin
import Theorems.Thm_ModularCurve_NodeLocalized_exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

noncomputable section

namespace P2mWs18Seed0

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}
  (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
  (W : Finset (Place k (modularFunctionFieldC k N))) (hWss : ∀ w ∈ W, w ∈ ssPlaces q N k)
  (hreg : R.RegularityLaw W) (hO : R.OrderLawFixed)

theorem forall_ord_nonneg_of_mem_nodeIntegers {w : Place k (modularFunctionFieldC k N)}
    {g : ↥(modularFunctionFieldBar (N * q))} (hg : g ∈ R.nodeIntegers w) :
    ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → 0 ≤ V.ord g :=
  fun _ hV => R.ord_nonneg_of_mem_nodeIntegers hg hV

include hqN hWss hreg in

theorem residueFst_mem_of_mem_nodeIntegers {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W)
    (g : ↥(R.nodeIntegers w)) :
    (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring := by
  have hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w :=
    frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr w (hWss w hw)
  have haff : IsAffineGeomPlace k N w := (hWss w hw).2.1
  have h := (hreg.1 (g : ↥(modularFunctionFieldBar (N * q))) g.2.1 g.2.2.1 w hfix haff
    (forall_ord_nonneg_of_mem_nodeIntegers R g.2)).1
  by_cases h0 : (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) = 0
  · rw [h0]; exact zero_mem _
  · rw [nodeResidue₁_apply] at h0 ⊢
    exact w.mem_of_ord_nonneg h0 (h h0)

def nodeEval {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) :
    ↥(R.nodeIntegers w) →+* w.ResidueField :=
  (IsLocalRing.residue ↥w.toValuationSubring).comp
    { toFun := fun g => ⟨R.nodeResidue₁ w g, residueFst_mem_of_mem_nodeIntegers R hqN W hWss hreg hw g⟩
      map_one' := Subtype.ext (by simp only [map_one]; rfl)
      map_mul' := fun g g' => Subtype.ext (by simp only [map_mul]; rfl)
      map_zero' := Subtype.ext (by simp only [map_zero]; rfl)
      map_add' := fun g g' => Subtype.ext (by simp only [map_add]; rfl) }

theorem nodeEval_apply {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (g : ↥(R.nodeIntegers w)) :
    nodeEval R hqN W hWss hreg hw g =
      IsLocalRing.residue ↥w.toValuationSubring
        ⟨R.nodeResidue₁ w g, residueFst_mem_of_mem_nodeIntegers R hqN W hWss hreg hw g⟩ := rfl

theorem nodeEval_eq_zero_iff {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (g : ↥(R.nodeIntegers w)) :
    nodeEval R hqN W hWss hreg hw g = 0 ↔ w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) 0 := by
  rw [nodeEval_apply, Place.hasValue_iff, map_zero]
  exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩

theorem nodeEval_eq_of_hasValue {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (g : ↥(R.nodeIntegers w))
    {c : k} (hc : w.HasValue (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) c) :
    nodeEval R hqN W hWss hreg hw g = algebraMap k w.ResidueField c := by
  rw [nodeEval_apply]
  exact hc.residue_eq

omit [IsAlgClosed k] [DecidableEq k] in

private theorem inv_mem_of_isUnit_vs {F : Type*} [Field F] (S : ValuationSubring F) {g : F} (h : g ∈ S)
    (hu : IsUnit (⟨g, h⟩ : ↥S)) : g ≠ 0 ∧ g⁻¹ ∈ S := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hv' : g * (v : F) = 1 := congrArg Subtype.val hv
  have hg0 : g ≠ 0 := fun h0 => by rw [h0, zero_mul] at hv'; exact zero_ne_one hv'
  exact ⟨hg0, (eq_inv_of_mul_eq_one_right hv') ▸ v.2⟩

private theorem mapDomain_apply_eq_sum {ι κ : Type*} [DecidableEq κ] (f : ι → κ) (D : ι →₀ ℤ) (w : κ) :
    Finsupp.mapDomain f D w = ∑ V ∈ D.support, (if f V = w then D V else 0) := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [Finsupp.single_apply]

include hO in

theorem isUnit_iff_nodeEval_ne_zero {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (g : ↥(R.nodeIntegers w)) :
    IsUnit g ↔ nodeEval R hqN W hWss hreg hw g ≠ 0 := by
  classical
  constructor
  · intro hu h0
    obtain ⟨g', hg'⟩ := hu.exists_right_inv
    have := congrArg (nodeEval R hqN W hWss hreg hw) hg'
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  · intro hne

    obtain ⟨c, hc₁, hc₂⟩ := hreg.2 (g : ↥(modularFunctionFieldBar (N * q))) g.2.1 g.2.2.1
      (ModularCurve.smulNodePair (arithFrobC q k N) w) (ModularCurve.smulNodePair_mem_nodePairsOfPlaces _ hw)
      (forall_ord_nonneg_of_mem_nodeIntegers R g.2)
    change w.HasValue (R.residue₁ _ : ↥(modularFunctionFieldC k N)) c at hc₁
    change (arithFrobC q k N • w).HasValue (R.residue₂ _ : ↥(modularFunctionFieldC k N)) c at hc₂
    have hc0 : c ≠ 0 := by
      intro h0
      apply hne
      rw [nodeEval_eq_of_hasValue R hqN W hWss hreg hw g (c := c) (by rw [nodeResidue₁_apply]; exact hc₁), h0, map_zero]

    have hres₁ : R.R₁.residue ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.1⟩ ≠ 0 := by
      intro h0
      apply hc₁.ne_zero hc0
      rw [residue₁_apply, h0, map_zero]
    have hres₂ : R.R₂.residue ⟨(g : ↥(modularFunctionFieldBar (N * q))), g.2.2.1⟩ ≠ 0 := by
      intro h0
      apply hc₂.ne_zero hc0
      rw [residue₂_apply, h0, map_zero]
    obtain ⟨hg0, hinv₁⟩ := inv_mem_of_isUnit_vs R.R₁.integers g.2.1 (R.R₁.isUnit_of_residue_ne_zero hres₁)
    obtain ⟨-, hinv₂⟩ := inv_mem_of_isUnit_vs R.R₂.integers g.2.2.1 (R.R₂.isUnit_of_residue_ne_zero hres₂)

    haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
      hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
      (g : ↥(modularFunctionFieldBar (N * q))) hg0
    have hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr w) = w :=
      frobOnPlacesGeomLevel_frobOnPlacesGeomLevel_eq_self_of_mem_ssPlaces_of_isAlgClosed k N hqN data hKr w (hWss w hw)
    have haff : IsAffineGeomPlace k N w := (hWss w hw).2.1
    have hlaw := hO (g : ↥(modularFunctionFieldBar (N * q))) g.2.1 g.2.2.1 hres₁ hres₂ D hD w hfix haff
    have hφ : frobOnPlacesGeomLevel k N data hKr w = arithFrobC q k N • w :=
      (arithFrobC_smul_eq_frobOnPlacesGeomLevel q k N data hKr w).symm
    rw [hφ, hc₁.ord_eq_zero hc0, hc₂.ord_eq_zero hc0, add_zero, mapDomain_apply_eq_sum] at hlaw

    have hterms : ∀ V ∈ D.support, (if P.reduceFst V = w then D V else 0) = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun V _ => ?_).mp hlaw
      split_ifs with hV
      · rw [hD]; exact R.ord_nonneg_of_mem_nodeIntegers g.2 hV
      · exact le_rfl
    have hordV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        V.ord (g : ↥(modularFunctionFieldBar (N * q))) = 0 := by
      intro V hV
      by_cases hs : V ∈ D.support
      · have := hterms V hs
        rw [if_pos hV, hD] at this
        exact this
      · have : D V = 0 := Finsupp.notMem_support_iff.mp hs
        rw [hD] at this
        exact this

    have hinvV : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
        (g : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ V.toValuationSubring := by
      intro V hV
      refine V.mem_of_ord_nonneg (inv_ne_zero hg0) ?_
      rw [Place.ord_inv, hordV V hV, neg_zero]
    refine isUnit_iff_exists_inv.mpr ⟨⟨(g : ↥(modularFunctionFieldBar (N * q)))⁻¹, ⟨hinv₁, hinv₂, hinvV⟩⟩, ?_⟩
    exact Subtype.ext (mul_inv_cancel₀ hg0)

omit [IsAlgClosed k] [DecidableEq k] in

theorem ord_eq_zero_of_isUnit {w : Place k (modularFunctionFieldC k N)} {g : ↥(R.nodeIntegers w)}
    (hu : IsUnit g) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    V.ord (g : ↥(modularFunctionFieldBar (N * q))) = 0 := by
  obtain ⟨g', hg'⟩ := hu.exists_right_inv
  have h1 := R.ord_nonneg_of_mem_nodeIntegers g.2 hV
  have h2 := R.ord_nonneg_of_mem_nodeIntegers g'.2 hV
  have hval : (g : ↥(modularFunctionFieldBar (N * q))) * (g' : ↥(modularFunctionFieldBar (N * q))) = 1 :=
    congrArg Subtype.val hg'
  have hg0 : (g : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hval; exact zero_ne_one hval
  have hg0' : (g' : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hval; exact zero_ne_one hval
  have := V.ord_mul hg0 hg0'
  rw [hval, Place.ord_one] at this
  omega

include hqN hWss hreg in

theorem ord_residueFst_eq_zero_of_isUnit {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) {g : ↥(R.nodeIntegers w)}
    (hu : IsUnit g) : w.ord (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) = 0 := by
  obtain ⟨g', hg'⟩ := hu.exists_right_inv
  have h1 := w.ord_nonneg_of_mem (residueFst_mem_of_mem_nodeIntegers R hqN W hWss hreg hw g)
  have h2 := w.ord_nonneg_of_mem (residueFst_mem_of_mem_nodeIntegers R hqN W hWss hreg hw g')
  have hval : (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) * R.nodeResidue₁ w g' = 1 := by
    rw [← map_mul, hg', map_one]
  have hg0 : (R.nodeResidue₁ w g : ↥(modularFunctionFieldC k N)) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hval; exact zero_ne_one hval
  have hg0' : (R.nodeResidue₁ w g' : ↥(modularFunctionFieldC k N)) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hval; exact zero_ne_one hval
  have := w.ord_mul hg0 hg0'
  rw [hval, Place.ord_one] at this
  omega

section PartB

def BW : Subring ↥(modularFunctionFieldBar (N * q)) := ⨅ w ∈ W, R.nodeIntegers w

theorem mem_BW_iff (f : ↥(modularFunctionFieldBar (N * q))) : f ∈ BW R W ↔ ∀ w ∈ W, f ∈ R.nodeIntegers w := by
  simp only [BW, Subring.mem_iInf]

theorem BW_le {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) : BW R W ≤ R.nodeIntegers w :=
  fun _ hf => (mem_BW_iff R W _).mp hf w hw

def ψ {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) : ↥(BW R W) →+* w.ResidueField :=
  (nodeEval R hqN W hWss hreg hw).comp (Subring.inclusion (BW_le R W hw))

theorem ψ_apply {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (b : ↥(BW R W)) :
    ψ R hqN W hWss hreg hw b = nodeEval R hqN W hWss hreg hw (Subring.inclusion (BW_le R W hw) b) := rfl

def 𝔪 {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) : Ideal ↥(BW R W) := RingHom.ker (ψ R hqN W hWss hreg hw)

theorem mem_𝔪_iff {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (b : ↥(BW R W)) :
    b ∈ 𝔪 R hqN W hWss hreg hw ↔ ψ R hqN W hWss hreg hw b = 0 := RingHom.mem_ker

theorem algebraMap_mem_BW (a : ↥A) : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ BW R W := by
  rw [mem_BW_iff]
  intro w _
  exact ⟨(R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2, (R.R₂.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2,
    fun V _ => V.algebraMap_mem' (a : AlgebraicClosure ℚ)⟩

def cst (a : ↥A) : ↥(BW R W) := ⟨_, algebraMap_mem_BW R W a⟩

@[scoped simp] theorem coe_cst (a : ↥A) :
    ((cst R W a : ↥(BW R W)) : ↥(modularFunctionFieldBar (N * q))) = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) := rfl

theorem residue₁_algebraMap (a : ↥A) (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ), h⟩ = algebraMap k ↥(modularFunctionFieldC k N) (red a) := by
  rw [residue₁_apply]
  have h1 : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ), h⟩ : ↥R.R₁.integers)
      = ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (a : AlgebraicClosure ℚ), (R.R₁.algebraMap_mem_iff _).mpr a.2⟩ := rfl
  rw [h1, R.R₁.residue_algebraMap a]
  apply Subtype.ext
  rw [R.ι_coe]
  show coeffMap R.redBar (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) (IsLocalRing.residue ↥A a))
    = algebraMap k (LaurentSeries k) (red a)
  rw [LaurentSeries.algebraMap_apply, LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.C_apply,
    coeffMap_single, R.redBar_residue]

theorem ψ_cst {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (a : ↥A) :
    ψ R hqN W hWss hreg hw (cst R W a) = algebraMap k w.ResidueField (red a) := by
  rw [ψ_apply]
  apply nodeEval_eq_of_hasValue
  have key : (R.nodeResidue₁ w (Subring.inclusion (BW_le R W hw) (cst R W a)) : ↥(modularFunctionFieldC k N)) = algebraMap k ↥(modularFunctionFieldC k N) (red a) :=
    residue₁_algebraMap R a (Subring.inclusion (BW_le R W hw) (cst R W a)).2.1
  rw [key]
  exact w.hasValue_algebraMap (red a)

theorem inv_mem_of_isUnit_subring {F : Type*} [Field F] (S : Subring F) {g : F} (h : g ∈ S)
    (hu : IsUnit (⟨g, h⟩ : ↥S)) : g⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hmul : g * ((u⁻¹ : (↥S)ˣ) : ↥S) = 1 := by
    have := congrArg (fun z : ↥S => (z : F)) u.mul_inv
    simpa [hu] using this
  rcases eq_or_ne g 0 with rfl | hg0
  · simp at hmul
  · have : g⁻¹ = ((u⁻¹ : (↥S)ˣ) : ↥S) := by
      rw [inv_eq_of_mul_eq_one_right hmul]
    rw [this]; exact SetLike.coe_mem _

include hO in

theorem isUnit_of_forall_notMem {b : ↥(BW R W)} (hb0 : (b : ↥(modularFunctionFieldBar (N * q))) ≠ 0)
    (hb : ∀ (w) (hw : w ∈ W), b ∉ 𝔪 R hqN W hWss hreg hw) : IsUnit b := by
  have hinv : (b : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ BW R W := by
    rw [mem_BW_iff]
    intro w hw
    have hu : IsUnit (Subring.inclusion (BW_le R W hw) b) := by
      rw [isUnit_iff_nodeEval_ne_zero R hqN W hWss hreg hO hw]
      intro h0; exact hb w hw ((mem_𝔪_iff R hqN W hWss hreg hw b).mpr h0)
    exact inv_mem_of_isUnit_subring (R.nodeIntegers w) (BW_le R W hw b.2) hu
  refine ⟨⟨b, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hb0), Subtype.ext (inv_mul_cancel₀ hb0)⟩, rfl⟩

theorem isAlgebraic_redRestrict {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K₀]
    [Algebra (ZMod q) k] (x : ↥(NodeLocalized.coeffSubring A K₀)) :
    IsAlgebraic (ZMod q) (NodeLocalized.redRestrict red K₀ x) := by
  have hxK : (x : AlgebraicClosure ℚ) ∈ K₀ := x.2.2
  have halgQ : IsAlgebraic ℚ (x : AlgebraicClosure ℚ) := by
    have : IsAlgebraic ℚ (⟨(x : AlgebraicClosure ℚ), hxK⟩ : ↥K₀) :=
      Algebra.IsAlgebraic.isAlgebraic _
    exact isAlgebraic_algebraMap_iff (algebraMap ↥K₀ (AlgebraicClosure ℚ)).injective |>.mpr this
  have halgZ : IsAlgebraic ℤ (x : AlgebraicClosure ℚ) := (IsFractionRing.isAlgebraic_iff ℤ ℚ _).mpr halgQ
  obtain ⟨p, hp0, hpx⟩ := halgZ
  set p' := p.primPart with hp'
  have hp'x : Polynomial.aeval (x : AlgebraicClosure ℚ) p' = 0 := by
    have hdec := Polynomial.eq_C_content_mul_primPart p
    have hc : (algebraMap ℤ (AlgebraicClosure ℚ)) p.content ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap ℤ (AlgebraicClosure ℚ)).injective_int]
      exact (Polynomial.content_eq_zero_iff).not.mpr hp0
    rw [hdec, map_mul, Polynomial.aeval_C, mul_eq_zero] at hpx
    exact hpx.resolve_left hc
  have hprim : p'.IsPrimitive := Polynomial.isPrimitive_primPart p
  have hmap : p'.map (Int.castRingHom k) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (q : ℤ) ∣ p' := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro n
      have hc : ((p'.coeff n : ℤ) : k) = 0 := by
        have := congrArg (fun r => Polynomial.coeff r n) h0
        simpa [Polynomial.coeff_map] using this
      exact (CharP.intCast_eq_zero_iff k q _).mp hc
    have hu : IsUnit (q : ℤ) := hprim _ hdvd
    have : (q : ℤ).natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hu
    simp at this
    exact (Fact.out : q.Prime).one_lt.ne' this
  have hxA : Polynomial.aeval ((⟨(x : AlgebraicClosure ℚ), x.2.1⟩ : ↥A)) p' = 0 := by
    have hinj : Function.Injective (algebraMap ↥A (AlgebraicClosure ℚ)) := Subtype.val_injective
    apply hinj
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
      RingHom.ext_int ((algebraMap ↥A (AlgebraicClosure ℚ)).comp (algebraMap ℤ ↥A)) (algebraMap ℤ (AlgebraicClosure ℚ))]
    rw [Polynomial.aeval_def] at hp'x
    exact hp'x
  have hred : Polynomial.eval₂ (Int.castRingHom k) (NodeLocalized.redRestrict red K₀ x) p' = 0 := by
    have h1 : NodeLocalized.redRestrict red K₀ x = red ⟨(x : AlgebraicClosure ℚ), x.2.1⟩ := rfl
    rw [h1, RingHom.ext_int (Int.castRingHom k) (red.comp (algebraMap ℤ ↥A)), ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, hxA, map_zero]
  refine ⟨(p'.map (Int.castRingHom (ZMod q))), ?_, ?_⟩
  · intro h0; apply hmap
    have : p'.map (Int.castRingHom k) = (p'.map (Int.castRingHom (ZMod q))).map (algebraMap (ZMod q) k) := by
      rw [Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _
    rw [this, h0, Polynomial.map_zero]
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, RingHom.ext_int ((algebraMap (ZMod q) k).comp (Int.castRingHom (ZMod q))) (Int.castRingHom k)]
    exact hred

theorem exists_numberField_pow_sq_subset_range :
    ∃ (K₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K₁),
      ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K₁) := by
  classical
  have hq2 : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero k two_ne_zero (Fact.out : q.Prime).one_lt
  obtain ⟨K₁, hK₁fd, -, hK₁⟩ :=
    ModularCurve.NodeLocalized.exists_finiteDimensional_forall_inertia_apply_eq_and_mem_range_redRestrict q A k red
      ((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset) (by
        intro a ha
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hq2, Polynomial.IsRoot.def] at ha
        simpa [sub_eq_zero] using ha)
  refine ⟨K₁, hK₁fd, fun a ha => hK₁ a ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hq2, Polynomial.IsRoot.def]
  simp [ha]

theorem range_redRestrict_mono {K₁ K₂ : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K₁ ≤ K₂) :
    Set.range (NodeLocalized.redRestrict red K₁) ⊆ Set.range (NodeLocalized.redRestrict red K₂) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨(x : AlgebraicClosure ℚ), x.2.1, h x.2.2⟩, rfl⟩

theorem algebraMap_residueField_surjective (w : Place k (modularFunctionFieldC k N)) : Function.Surjective (algebraMap k w.ResidueField) := by
  haveI : PerfectField k := IsAlgClosed.perfectField k
  haveI : IsCurveOver k ↥(modularFunctionFieldC k N) := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField k N
  haveI : Module.Finite k w.ResidueField := IsCurveOver.finite_residueField w
  haveI : Algebra.IsIntegral k w.ResidueField := Algebra.IsIntegral.of_finite k w.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := w.ResidueField)).2

theorem isAlgebraic_ψ {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (b : ↥(BW R W)) :
    letI : Algebra (ZMod q) k := ZMod.algebra k q
    letI : Algebra (ZMod q) w.ResidueField := ((algebraMap k w.ResidueField).comp (algebraMap (ZMod q) k)).toAlgebra
    IsAlgebraic (ZMod q) (ψ R hqN W hWss hreg hw b) := by
  letI : Algebra (ZMod q) k := ZMod.algebra k q
  letI : Algebra (ZMod q) w.ResidueField := ((algebraMap k w.ResidueField).comp (algebraMap (ZMod q) k)).toAlgebra
  haveI : IsScalarTower (ZMod q) k w.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨K₁, hK₁fd, hK₁⟩ := exists_numberField_pow_sq_subset_range (k := k) (red := red) (q := q) (A := A)
  haveI := hK₁fd
  obtain ⟨K, hKfd, hK₁K, hbK⟩ := R.exists_le_mem_nodeIntegersOver_of_mem_nodeIntegers w (b : ↥(modularFunctionFieldBar (N * q))) (BW_le R W hw b.2) K₁
  haveI := hKfd
  have hk₀ : ∀ a : k, a ^ (q ^ 2) = a → a ∈ Set.range (NodeLocalized.redRestrict red K) :=
    fun a ha => range_redRestrict_mono (red := red) hK₁K (hK₁ a ha)
  obtain ⟨a, ha⟩ := algebraMap_residueField_surjective (k := k) (N := N) w (ψ R hqN W hWss hreg hw b)
  have hval : w.HasValue (R.nodeResidue₁ w ⟨(b : ↥(modularFunctionFieldBar (N * q))), hbK.1⟩ : ↥(modularFunctionFieldC k N)) a := by
    refine ⟨residueFst_mem_of_mem_nodeIntegers R hqN W hWss hreg hw (Subring.inclusion (BW_le R W hw) b), ?_⟩
    rw [ha]; rfl
  obtain ⟨x, hx⟩ := R.mem_range_redRestrict_of_hasValue_nodeResidueFst hqN K w (hWss w hw) hk₀ ⟨_, hbK⟩ a hval
  rw [← ha, ← hx]
  exact (isAlgebraic_redRestrict red K x).algebraMap

theorem isMaximal_𝔪 {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) : (𝔪 R hqN W hWss hreg hw).IsMaximal := by
  classical
  letI : Algebra (ZMod q) k := ZMod.algebra k q
  letI : Algebra (ZMod q) w.ResidueField := ((algebraMap k w.ResidueField).comp (algebraMap (ZMod q) k)).toAlgebra
  set ψ' := ψ R hqN W hWss hreg hw with hψ'

  have hinv : ∀ b : ↥(BW R W), ψ' b ≠ 0 → ∃ c : ↥(BW R W), ψ' b * ψ' c = 1 := by
    intro b hb
    let Ψ : Subalgebra (ZMod q) w.ResidueField :=
      { ψ'.range with
        algebraMap_mem' := fun r => by
          obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective r
          rw [map_natCast]; exact natCast_mem ψ'.range n }
    have hmemΨ : ψ' b ∈ Ψ := ⟨b, rfl⟩
    have : (ψ' b)⁻¹ ∈ Ψ := Ψ.inv_mem_of_algebraic (x := ⟨ψ' b, hmemΨ⟩) (isAlgebraic_ψ R hqN W hWss hreg hw b)
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by rw [hc, mul_inv_cancel₀ hb]⟩

  rw [𝔪]
  refine Ideal.Quotient.maximal_of_isField _ ?_
  refine ⟨⟨0, 1, ?_⟩, mul_comm, ?_⟩
  · intro h
    have := (Ideal.Quotient.eq (I := RingHom.ker ψ')).mp h
    rw [zero_sub, RingHom.mem_ker, map_neg, map_one, neg_eq_zero] at this
    exact one_ne_zero this
  · intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hb : ψ' b ≠ 0 := by
      intro h0; apply hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr h0)
    obtain ⟨c, hc⟩ := hinv b hb
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (RingHom.ker ψ'))]
    apply (Ideal.Quotient.eq (I := RingHom.ker ψ')).mpr
    rw [RingHom.mem_ker, map_sub, map_mul, map_one, hc, sub_self]

theorem exists_mem_𝔪_notMem_𝔪 {w w' : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (hw' : w' ∈ W) (hne : w ≠ w') :
    ∃ b : ↥(BW R W), b ∈ 𝔪 R hqN W hWss hreg hw ∧ b ∉ 𝔪 R hqN W hWss hreg hw' := by
  classical
  obtain ⟨t, htcoef, htaff, htw, htw'⟩ :=
    ModularCurve.exists_coeff_pow_sq_eq_and_hasValue_zero_and_not_hasValue_zero_of_mem_ssPlaces_of_ne
      hqN w w' (hWss w hw) hne
  obtain ⟨K, hKfd, hK⟩ := exists_numberField_pow_sq_subset_range (k := k) (red := red) (q := q) (A := A)
  haveI := hKfd

  have hseries : ∃ h₀ : LaurentSeries ↥(NodeLocalized.coeffSubring A K),
      coeffMap (NodeLocalized.redRestrict red K) h₀ = (t : LaurentSeries k) := by
    choose c hc using fun n : ℤ => hK ((t : LaurentSeries k).coeff n) (htcoef n)
    let c' : ℤ → ↥(NodeLocalized.coeffSubring A K) := fun n => if (t : LaurentSeries k).coeff n = 0 then 0 else c n
    have hsupp : Function.support c' ⊆ Function.support (t : LaurentSeries k).coeff := by
      intro n hn
      simp only [Function.mem_support, ne_eq, c'] at hn ⊢
      intro h0; exact hn (by rw [if_pos h0])
    refine ⟨⟨c', (t : LaurentSeries k).isPWO_support'.mono hsupp⟩, ?_⟩
    ext n
    simp only [coeffMap_coeff]
    show NodeLocalized.redRestrict red K (c' n) = _
    simp only [c']
    split_ifs with h0
    · rw [map_zero, h0]
    · exact hc n
  obtain ⟨h₀, hh₀⟩ := hseries
  have hN : (N : k) ≠ 0 := by
    intro h0
    exact hqN ((CharP.cast_eq_zero_iff k q N).mp h0)
  have hint : IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) t :=
    (ModularCurve.forall_isAffineGeomPlace_mem_iff_isIntegral_adjoin hN t).mp htaff
  obtain ⟨y, a, hay, hared, haK, haint⟩ :=
    ModularCurve.exists_fieldOver_lift_isIntegral_of_isIntegral red hqN K h₀ t hh₀ hint

  have hL3 : ∀ (w'') (hw'' : w'' ∈ W), ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q a ∈ R.nodeIntegersOver K w'',
      ((R.nodeResidue₁ w'' ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q a, h.1⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
        = coeffMap (NodeLocalized.redRestrict red K) y :=
    fun w'' hw'' => (R.heckeAlphaBar_mem_nodeIntegersOver_and_nodeResidue_eq_coeffMap hqN K w'' (hWss w'' hw'')
      y a hay haK haint).1
  have hmem : heckeAlphaBar (AlgebraicClosure ℚ) N q a ∈ BW R W := by
    rw [mem_BW_iff]
    intro w'' hw''
    exact (hL3 w'' hw'').choose.1
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  ·
    rw [mem_𝔪_iff, ψ_apply, nodeEval_eq_zero_iff]
    obtain ⟨h, hres⟩ := hL3 w hw
    have : (R.nodeResidue₁ w (Subring.inclusion (BW_le R W hw) ⟨_, hmem⟩) : ↥(modularFunctionFieldC k N)) = t :=
      Subtype.ext (by rw [← hared]; exact hres)
    rw [this]; exact htw
  · rw [mem_𝔪_iff, ψ_apply, nodeEval_eq_zero_iff]
    obtain ⟨h, hres⟩ := hL3 w' hw'
    have : (R.nodeResidue₁ w' (Subring.inclusion (BW_le R W hw') ⟨_, hmem⟩) : ↥(modularFunctionFieldC k N)) = t :=
      Subtype.ext (by rw [← hared]; exact hres)
    rw [this]; exact htw'

theorem 𝔪_sup_𝔪_eq_top {w w' : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (hw' : w' ∈ W) (hne : w ≠ w') :
    𝔪 R hqN W hWss hreg hw ⊔ 𝔪 R hqN W hWss hreg hw' = ⊤ := by
  have hne' : 𝔪 R hqN W hWss hreg hw ≠ 𝔪 R hqN W hWss hreg hw' := by
    intro heq
    obtain ⟨b, hb, hb'⟩ := exists_mem_𝔪_notMem_𝔪 R hqN W hWss hreg hw hw' hne
    exact hb' (heq ▸ hb)
  exact Ideal.IsMaximal.coprime_of_ne (isMaximal_𝔪 R hqN W hWss hreg hw) (isMaximal_𝔪 R hqN W hWss hreg hw') hne'

private theorem _root_.AlgebraicCurve.Place.HasValue.sub' {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}
    {f g : F} {a b : K} (hf : v.HasValue f a) (hg : v.HasValue g b) : v.HasValue (f - g) (a - b) := by
  obtain ⟨h1, r1⟩ := hf
  obtain ⟨h2, r2⟩ := hg
  refine ⟨sub_mem h1 h2, ?_⟩
  have : (⟨f - g, sub_mem h1 h2⟩ : ↥v.toValuationSubring) = ⟨f, h1⟩ - ⟨g, h2⟩ := rfl
  rw [this, map_sub, r1, r2, map_sub]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg.AlgebraicCurve.Place.HasValue.sub'" "AlgebraicCurve.Place.HasValue.sub'"
private theorem _root_.AlgebraicCurve.Place.ord_pos_of_hasValue_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : v.HasValue f 0) (hf0 : f ≠ 0) : 0 < v.ord f := by
  obtain ⟨h1, r1⟩ := hf
  rw [map_zero, IsLocalRing.residue_eq_zero_iff] at r1
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, h1⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exfalso
    subst hn
    rw [pow_zero, mul_one] at hu
    rw [hu] at r1
    exact (IsLocalRing.mem_maximalIdeal _).mp r1 u.isUnit
  · exact_mod_cast hn

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg.AlgebraicCurve.Place.ord_pos_of_hasValue_zero" "AlgebraicCurve.Place.ord_pos_of_hasValue_zero"
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  have h1 : v.adicValuation f ≤ 1 := v.adicValuation_le_one_iff.mpr (Or.inr h)
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h1
  exact a.2

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg.AlgebraicCurve.Place.mem_of_ord_nonneg'" "AlgebraicCurve.Place.mem_of_ord_nonneg'"
private theorem _root_.AlgebraicCurve.Place.ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (f : F) (m : ℕ) : v.ord (f ^ m) = (m : ℤ) * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg.AlgebraicCurve.Place.ord_pow'" "AlgebraicCurve.Place.ord_pow'"

private theorem _root_.AlgebraicCurve.Place.ord_finset_prod {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Place.ord_one]
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, v.ord_mul (hf i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr fun j hj => hf j (Finset.mem_insert_of_mem hj)),
        ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg.AlgebraicCurve.Place.ord_finset_prod" "AlgebraicCurve.Place.ord_finset_prod"

theorem ord_nonneg_of_mem_BW {b : ↥(modularFunctionFieldBar (N * q))} (hb : b ∈ BW R W) (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) {w' : Place k (modularFunctionFieldC k N)} (hw' : w' ∈ W)
    (hV : P.reduceFst V = w') : 0 ≤ V.ord b :=
  V.ord_nonneg_of_mem (((mem_BW_iff R W b).mp hb w' hw').2.2 V hV)

include hO in

theorem exists_notMem_𝔪_ord_pos (hmodel : R.IsModel) (hval : R.NodeValueLaw W) {w w' : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (hw' : w' ∈ W)
    (hne : w ≠ w') (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w') :
    ∃ b : ↥(BW R W), b ∉ 𝔪 R hqN W hWss hreg hw ∧ 0 < V.ord (b : ↥(modularFunctionFieldBar (N * q))) := by
  classical
  obtain ⟨g, hgw', hgw⟩ := exists_mem_𝔪_notMem_𝔪 R hqN W hWss hreg hw' hw (Ne.symm hne)

  have hgN : (g : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegers w' := BW_le R W hw' g.2
  have hvalA : R.ValueIntegralityLaw w' := R.valueIntegralityLaw_of_orderLawFixed hqN hO w' (hWss w' hw')
  have hA : V.evalAt (g : ↥(modularFunctionFieldBar (N * q))) ∈ A := hvalA _ hgN V hV
  obtain ⟨K, hKfd, -, hgK⟩ := R.exists_le_mem_nodeIntegersOver_of_mem_nodeIntegers w' (g : ↥(modularFunctionFieldBar (N * q))) hgN ⊥
  haveI := hKfd
  have hcompat := R.hasValue_nodeResidueFst_red_evalAt_of_orderLawFixed hqN hmodel hO W hWss hreg hval K w' hw' hvalA
    ⟨_, hgK⟩ V hV
  have hzero : w'.HasValue (R.nodeResidue₁ w' ⟨(g : ↥(modularFunctionFieldBar (N * q))), hgK.1⟩ : ↥(modularFunctionFieldC k N)) (0 : k) := by
    have := (nodeEval_eq_zero_iff R hqN W hWss hreg hw' (Subring.inclusion (BW_le R W hw') g)).mp
      ((mem_𝔪_iff R hqN W hWss hreg hw' g).mp hgw')
    exact this
  have hred0 : red ⟨V.evalAt (g : ↥(modularFunctionFieldBar (N * q))), hA⟩ = 0 := (hcompat.unique hzero)

  let c : ↥(BW R W) := cst R W ⟨V.evalAt (g : ↥(modularFunctionFieldBar (N * q))), hA⟩
  refine ⟨g - c, ?_, ?_⟩
  · intro hmem
    apply hgw
    rw [mem_𝔪_iff] at hmem ⊢
    rw [map_sub, ψ_cst, hred0, map_zero, sub_zero] at hmem
    exact hmem
  · have hVrat : V.IsRational := ModularCurve.isRational_place_modularFunctionFieldBar (N * q) V
    have hgV : (g : ↥(modularFunctionFieldBar (N * q))) ∈ V.toValuationSubring := hgN.2.2 V hV
    have hval1 : V.HasValue (g : ↥(modularFunctionFieldBar (N * q))) (V.evalAt (g : ↥(modularFunctionFieldBar (N * q)))) := ⟨hgV, (V.algebraMap_evalAt hVrat hgV).symm⟩
    have hval2 : V.HasValue ((c : ↥(BW R W)) : ↥(modularFunctionFieldBar (N * q))) (V.evalAt (g : ↥(modularFunctionFieldBar (N * q)))) := by
      show V.HasValue (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (V.evalAt (g : ↥(modularFunctionFieldBar (N * q))))) _
      exact V.hasValue_algebraMap _
    have hval0 : V.HasValue (((g - c : ↥(BW R W)) : ↥(modularFunctionFieldBar (N * q)))) 0 := by
      have := hval1.sub' hval2
      rwa [sub_self] at this
    refine V.ord_pos_of_hasValue_zero hval0 ?_
    intro h0
    apply hgw
    rw [mem_𝔪_iff]
    have hgc : g - c = 0 := Subtype.ext h0
    have : ψ R hqN W hWss hreg hw (g - c) = 0 := by rw [hgc, map_zero]
    rw [map_sub, ψ_cst, hred0, map_zero, sub_zero] at this
    exact this

include hO in

theorem exists_notMem_𝔪_forall_le_ord (hmodel : R.IsModel) (hval : R.NodeValueLaw W) {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W)
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))) (hS : ∀ V ∈ S, P.reduceFst V ∈ W ∧ P.reduceFst V ≠ w) (m : ℕ) :
    ∃ b : ↥(BW R W), b ∉ 𝔪 R hqN W hWss hreg hw ∧ ∀ V ∈ S, (m : ℤ) ≤ V.ord (b : ↥(modularFunctionFieldBar (N * q))) := by
  classical

  have hex : ∀ V ∈ S, ∃ b : ↥(BW R W), b ∉ 𝔪 R hqN W hWss hreg hw ∧ 0 < V.ord (b : ↥(modularFunctionFieldBar (N * q))) := by
    intro V hVS
    obtain ⟨hVW, hVw⟩ := hS V hVS
    exact exists_notMem_𝔪_ord_pos R hqN W hWss hreg hO hmodel hval hw hVW (Ne.symm hVw) V rfl
  choose! h hh using hex
  refine ⟨∏ V ∈ S, (h V) ^ m, ?_, ?_⟩
  ·
    rw [mem_𝔪_iff, map_prod]
    rw [Finset.prod_eq_zero_iff]
    rintro ⟨V, hVS, h0⟩
    rw [map_pow] at h0
    exact (hh V hVS).1 ((mem_𝔪_iff R hqN W hWss hreg hw _).mpr (pow_eq_zero_iff'.mp h0).1)
  · intro V hVS
    have hcoe : (((∏ V' ∈ S, (h V') ^ m : ↥(BW R W))) : ↥(modularFunctionFieldBar (N * q))) = ∏ V' ∈ S, ((h V' : ↥(BW R W)) : ↥(modularFunctionFieldBar (N * q))) ^ m := by
      simp only [SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_pow]
    rw [hcoe]
    have hne : ∀ V' ∈ S, ((h V' : ↥(BW R W)) : ↥(modularFunctionFieldBar (N * q))) ^ m ≠ 0 := by
      intro V' hV'S
      apply pow_ne_zero
      intro h0
      have := (hh V' hV'S).2
      rw [h0, Place.ord_zero] at this
      exact lt_irrefl _ this
    rw [V.ord_finset_prod S _ hne]
    have hterm : ∀ V' ∈ S, 0 ≤ V.ord (((h V' : ↥(BW R W)) : ↥(modularFunctionFieldBar (N * q))) ^ m) := by
      intro V' hV'S
      rw [V.ord_pow']
      exact mul_nonneg (Int.natCast_nonneg m) (ord_nonneg_of_mem_BW R W (h V').2 V (hS V hVS).1 rfl)
    calc (m : ℤ) = (m : ℤ) * 1 := by ring
      _ ≤ (m : ℤ) * V.ord ((h V : ↥(BW R W)) : ↥(modularFunctionFieldBar (N * q))) :=
          mul_le_mul_of_nonneg_left (hh V hVS).2 (Int.natCast_nonneg m)
      _ = V.ord (((h V : ↥(BW R W)) : ↥(modularFunctionFieldBar (N * q))) ^ m) := (V.ord_pow' _ m).symm
      _ ≤ ∑ V' ∈ S, V.ord (((h V' : ↥(BW R W)) : ↥(modularFunctionFieldBar (N * q))) ^ m) :=
          Finset.single_le_sum hterm hVS

include hO in

theorem exists_corrector (hmodel : R.IsModel) (hval : R.NodeValueLaw W)
    (y : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldBar (N * q))) (n : Place k (modularFunctionFieldC k N) → ℕ)
    (hyS : ∀ w ∈ W, y w ∈ R.nodeIntegers w)
    (hy₁ : ∀ w ∈ W, ∃ h : y w ∈ R.R₁.integers, R.R₁.residue ⟨y w, h⟩ ≠ 0)
    (hyV : ∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.ord (y w) = 0)
    (hvert : ∀ w ∈ W, ∀ w' ∈ W,
      ∃ h : y w ^ n w * (y w' ^ n w')⁻¹ ∈ R.R₂.integers, R.R₂.residue ⟨y w ^ n w * (y w' ^ n w')⁻¹, h⟩ ≠ 0)
    {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) :
    ∃ b : ↥(BW R W), b ∉ 𝔪 R hqN W hWss hreg hw ∧
      ∀ (w') (_ : w' ∈ W), ((y w) ^ (n w))⁻¹ * (b : ↥(modularFunctionFieldBar (N * q))) * (y w') ^ (n w') ∈ R.nodeIntegers w' := by
  classical
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  have hy0 : ∀ w'' ∈ W, y w'' ≠ 0 := by
    intro w'' hw'' h0
    obtain ⟨h, hres⟩ := hy₁ w'' hw''
    apply hres
    have : (⟨y w'', h⟩ : ↥R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) (y w) (hy0 w hw)
  let S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :=
    D.support.filter (fun V => P.reduceFst V ∈ W ∧ P.reduceFst V ≠ w ∧ 0 < V.ord (y w))
  have hS : ∀ V ∈ S, P.reduceFst V ∈ W ∧ P.reduceFst V ≠ w := by
    intro V hV
    obtain ⟨-, h1, h2, -⟩ := Finset.mem_filter.mp hV
    exact ⟨h1, h2⟩
  let M : ℕ := S.sup (fun V => (V.ord (y w)).toNat)
  obtain ⟨b, hb, hbord⟩ := exists_notMem_𝔪_forall_le_ord R hqN W hWss hreg hO hmodel hval hw S hS (n w * M)
  have hb0 : (b : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro h0; apply hb; rw [mem_𝔪_iff]
    have : b = 0 := Subtype.ext h0
    rw [this, map_zero]
  refine ⟨b, hb, fun w' hw' => ?_⟩

  obtain ⟨hyw1, hyw1res⟩ := hy₁ w hw
  obtain ⟨hyw'1, -⟩ := hy₁ w' hw'
  have hunit1 : IsUnit (⟨(y w) ^ (n w), pow_mem hyw1 (n w)⟩ : ↥R.R₁.integers) := by
    apply R.R₁.isUnit_of_residue_ne_zero
    have : (⟨(y w) ^ (n w), pow_mem hyw1 (n w)⟩ : ↥R.R₁.integers) = ⟨y w, hyw1⟩ ^ (n w) := rfl
    rw [this, map_pow]
    exact pow_ne_zero _ hyw1res
  have hinv1 : ((y w) ^ (n w))⁻¹ ∈ R.R₁.integers :=
    inv_mem_of_isUnit_subring R.R₁.integers.toSubring (pow_mem hyw1 (n w)) hunit1
  have hmem1 : ((y w) ^ (n w))⁻¹ * (b : ↥(modularFunctionFieldBar (N * q))) * (y w') ^ (n w') ∈ R.R₁.integers :=
    mul_mem (mul_mem hinv1 (BW_le R W hw b.2).1) (pow_mem hyw'1 (n w'))

  obtain ⟨h2, -⟩ := hvert w' hw' w hw
  have hmem2 : ((y w) ^ (n w))⁻¹ * (b : ↥(modularFunctionFieldBar (N * q))) * (y w') ^ (n w') ∈ R.R₂.integers := by
    have : ((y w) ^ (n w))⁻¹ * (b : ↥(modularFunctionFieldBar (N * q))) * (y w') ^ (n w') = (b : ↥(modularFunctionFieldBar (N * q))) * ((y w') ^ (n w') * ((y w) ^ (n w))⁻¹) := by ring
    rw [this]
    exact mul_mem (BW_le R W hw b.2).2.1 h2
  refine ⟨hmem1, hmem2, fun V hV => ?_⟩
  by_cases hww : w' = w
  · subst hww
    have : ((y w') ^ (n w'))⁻¹ * (b : ↥(modularFunctionFieldBar (N * q))) * (y w') ^ (n w') = (b : ↥(modularFunctionFieldBar (N * q))) := by
      field_simp [pow_ne_zero (n w') (hy0 w' hw)]
    rw [this]
    exact (BW_le R W hw b.2).2.2 V hV
  · apply V.mem_of_ord_nonneg'
    have hyw0 : (y w) ^ (n w) ≠ 0 := pow_ne_zero _ (hy0 w hw)
    have hyw'0 : (y w') ^ (n w') ≠ 0 := pow_ne_zero _ (hy0 w' hw')
    rw [V.ord_mul (mul_ne_zero (inv_ne_zero hyw0) hb0) hyw'0, V.ord_mul (inv_ne_zero hyw0) hb0, V.ord_inv,
      V.ord_pow', V.ord_pow', hyV w' hw' V hV, mul_zero, add_zero]
    have hbnn : 0 ≤ V.ord (b : ↥(modularFunctionFieldBar (N * q))) := ord_nonneg_of_mem_BW R W b.2 V hw' hV
    by_cases hpos : 0 < V.ord (y w)
    ·
      have hVS : V ∈ S := by
        refine Finset.mem_filter.mpr ⟨?_, ?_, ?_, hpos⟩
        · rw [Finsupp.mem_support_iff, hD V]; exact hpos.ne'
        · rw [hV]; exact hw'
        · rw [hV]; exact hww
      have h1 : ((n w * M : ℕ) : ℤ) ≤ V.ord (b : ↥(modularFunctionFieldBar (N * q))) := hbord V hVS
      have h2 : (V.ord (y w)).toNat ≤ M := Finset.le_sup (f := fun V => (V.ord (y w)).toNat) hVS
      have h3 : V.ord (y w) = ((V.ord (y w)).toNat : ℤ) := (Int.toNat_of_nonneg hpos.le).symm
      rw [h3]
      push_cast at h1 ⊢
      nlinarith [h1, h2, Int.natCast_nonneg (n w), (Int.natCast_nonneg M), (Int.toNat_of_nonneg hpos.le)]
    · push Not at hpos
      nlinarith [hbnn, hpos, Int.natCast_nonneg (n w)]

include hO in

theorem exists_mul_eq_of_mem_nodeIntegers (hmodel : R.IsModel) (hval : R.NodeValueLaw W) {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W)
    (g : ↥(modularFunctionFieldBar (N * q))) (hg : g ∈ R.nodeIntegers w) :
    ∃ b s : ↥(BW R W), s ∉ 𝔪 R hqN W hWss hreg hw ∧ g * s = b := by
  classical
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * q)
  have hone : (1 : ↥(BW R W)) ∉ 𝔪 R hqN W hWss hreg hw := by
    rw [mem_𝔪_iff, map_one]; exact one_ne_zero
  rcases eq_or_ne g 0 with rfl | hg0
  · exact ⟨0, 1, hone, by simp⟩
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q))) g hg0
  let S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :=
    D.support.filter (fun V => P.reduceFst V ∈ W ∧ P.reduceFst V ≠ w ∧ V.ord g < 0)
  have hS : ∀ V ∈ S, P.reduceFst V ∈ W ∧ P.reduceFst V ≠ w := by
    intro V hV
    obtain ⟨-, h1, h2, -⟩ := Finset.mem_filter.mp hV
    exact ⟨h1, h2⟩
  let M : ℕ := S.sup (fun V => (-V.ord g).toNat)
  obtain ⟨s, hs, hsord⟩ := exists_notMem_𝔪_forall_le_ord R hqN W hWss hreg hO hmodel hval hw S hS M
  have hs0 : (s : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro h0; apply hs; rw [mem_𝔪_iff]
    have : s = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hmem : g * (s : ↥(modularFunctionFieldBar (N * q))) ∈ BW R W := by
    rw [mem_BW_iff]
    intro w' hw'
    refine ⟨mul_mem hg.1 (BW_le R W hw' s.2).1, mul_mem hg.2.1 (BW_le R W hw' s.2).2.1, fun V hV => ?_⟩
    by_cases hww : w' = w
    · subst hww
      exact mul_mem (hg.2.2 V hV) ((BW_le R W hw' s.2).2.2 V hV)
    · apply V.mem_of_ord_nonneg'
      rw [V.ord_mul hg0 hs0]
      have hsnn : 0 ≤ V.ord (s : ↥(modularFunctionFieldBar (N * q))) := ord_nonneg_of_mem_BW R W s.2 V hw' hV
      by_cases hneg : V.ord g < 0
      · have hVS : V ∈ S := by
          refine Finset.mem_filter.mpr ⟨?_, ?_, ?_, hneg⟩
          · rw [Finsupp.mem_support_iff, hD V]; exact hneg.ne
          · rw [hV]; exact hw'
          · rw [hV]; exact hww
        have h1 : (M : ℤ) ≤ V.ord (s : ↥(modularFunctionFieldBar (N * q))) := hsord V hVS
        have h2 : (-V.ord g).toNat ≤ M := Finset.le_sup (f := fun V => (-V.ord g).toNat) hVS
        have h3 : ((-V.ord g).toNat : ℤ) = -V.ord g := Int.toNat_of_nonneg (by omega)
        omega
      · push Not at hneg
        omega
  exact ⟨⟨_, hmem⟩, s, hs, rfl⟩

end PartB

section PartC

include hqN hWss hreg hO in

theorem isLocalRing_nodeIntegers {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) :
    IsLocalRing ↥(R.nodeIntegers w) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff_nodeEval_ne_zero R hqN W hWss hreg hO hw, not_not] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

include hqN hWss hreg hO in

theorem mem_maximalIdeal_iff {w : Place k (modularFunctionFieldC k N)} (hw : w ∈ W) (g : ↥(R.nodeIntegers w)) :
    haveI := isLocalRing_nodeIntegers R hqN W hWss hreg hO hw
    g ∈ maximalIdeal ↥(R.nodeIntegers w) ↔ nodeEval R hqN W hWss hreg hw g = 0 := by
  haveI := isLocalRing_nodeIntegers R hqN W hWss hreg hO hw
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_nodeEval_ne_zero R hqN W hWss hreg hO hw, not_not]

theorem exists_forall_isUnit_div_of_cartier'
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Subring F) (O : ι → Subring F) (hBO : ∀ i, B ≤ O i) [hloc : ∀ i, IsLocalRing ↥(O i)]
    (t : ι → F) (ht : ∀ i, t i ≠ 0)
    (hcop : ∀ i j, i ≠ j →
      (maximalIdeal ↥(O i)).comap (Subring.inclusion (hBO i)) ⊔ (maximalIdeal ↥(O j)).comap (Subring.inclusion (hBO j)) = ⊤)
    (hcart : ∀ i, ∃ b' : ↥B, b' ∉ (maximalIdeal ↥(O i)).comap (Subring.inclusion (hBO i)) ∧
      ∀ j, t i * (b' : F) * (t j)⁻¹ ∈ O j) :
    ∃ f : F, ∀ i, ∃ h : f * (t i)⁻¹ ∈ O i, IsUnit (⟨f * (t i)⁻¹, h⟩ : ↥(O i)) := by
  classical
  set 𝔫 : ι → Ideal ↥B := fun i => (maximalIdeal ↥(O i)).comap (Subring.inclusion (hBO i)) with h𝔫
  choose b' hb' hcart' using hcart
  have hcrt : ∀ i, ∃ e : ↥B, e - 1 ∈ 𝔫 i ∧ ∀ j, j ≠ i → e ∈ 𝔫 j := by
    intro i
    have hpair : ∀ j, j ≠ i → ∃ a b : ↥B, a ∈ 𝔫 i ∧ b ∈ 𝔫 j ∧ a + b = 1 := by
      intro j hji
      have htop : 𝔫 i ⊔ 𝔫 j = ⊤ := hcop i j hji.symm
      have h1 : (1 : ↥B) ∈ 𝔫 i ⊔ 𝔫 j := by rw [htop]; trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
      exact ⟨a, b, ha, hb, hab⟩
    choose! a b ha hb hab using hpair
    refine ⟨∏ j ∈ Finset.univ.erase i, b j, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq, map_prod]
      rw [Finset.prod_eq_one]
      · exact (map_one _).symm
      · intro j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        have hbj : b j = 1 - a j := by rw [← hab j hji]; ring
        rw [hbj, map_sub, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (ha j hji), sub_zero]
    · intro j hji
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem b (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      rw [hc]
      exact Ideal.mul_mem_right _ _ (hb j hji)
  choose e he1 he0 using hcrt
  refine ⟨∑ j, (e j : F) * (t j * (b' j : F)), fun i => ?_⟩
  have hmemj : ∀ j, (e j : F) * (t j * (b' j : F)) * (t i)⁻¹ ∈ O i := fun j => by
    have := hcart' j i
    have h := (O i).mul_mem (hBO i (e j).2) this
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hsum : (∑ j, (e j : F) * (t j * (b' j : F))) * (t i)⁻¹ = ∑ j, (e j : F) * (t j * (b' j : F)) * (t i)⁻¹ := by
    rw [Finset.sum_mul]
  have hmem : (∑ j, (e j : F) * (t j * (b' j : F))) * (t i)⁻¹ ∈ O i := by
    rw [hsum]; exact (O i).sum_mem fun j _ => hmemj j
  refine ⟨hmem, ?_⟩
  let s : ι → ↥(O i) := fun j => ⟨(e j : F) * (t j * (b' j : F)) * (t i)⁻¹, hmemj j⟩
  have hval : (⟨(∑ j, (e j : F) * (t j * (b' j : F))) * (t i)⁻¹, hmem⟩ : ↥(O i)) = ∑ j, s j := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [hsum, s]
  rw [hval, ← Finset.add_sum_erase Finset.univ s (Finset.mem_univ i)]
  have unit_add_mem : ∀ (u m : ↥(O i)), IsUnit u → m ∈ maximalIdeal ↥(O i) → IsUnit (u + m) := by
    intro u m hu hm
    by_contra hnu
    have h1 : u + m ∈ maximalIdeal ↥(O i) := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have h2 : u ∈ maximalIdeal ↥(O i) := by
      have := Ideal.sub_mem _ h1 hm
      simpa using this
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp h2)) hu
  apply unit_add_mem
  · have hti : s i = ⟨(e i : F), hBO i (e i).2⟩ * ⟨(b' i : F), hBO i (b' i).2⟩ := by
      apply Subtype.ext
      simp only [s, Subring.coe_mul]
      rw [mul_comm (t i) (b' i : F), mul_assoc, mul_assoc, mul_inv_cancel₀ (ht i), mul_one]
    rw [hti]
    refine IsUnit.mul ?_ ?_
    · have hm : (⟨(e i : F), hBO i (e i).2⟩ : ↥(O i)) - 1 ∈ maximalIdeal ↥(O i) := he1 i
      have := unit_add_mem 1 (⟨(e i : F), hBO i (e i).2⟩ - 1) isUnit_one hm
      simpa using this
    · by_contra hnu
      exact hb' i ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
  · refine Ideal.sum_mem _ fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hej : (⟨(e j : F), hBO i (e j).2⟩ : ↥(O i)) ∈ maximalIdeal ↥(O i) := he0 j i hji.symm
    have hsj : s j = ⟨(e j : F), hBO i (e j).2⟩ * ⟨t j * (b' j : F) * (t i)⁻¹, by
        have := hcart' j i
        simpa [mul_assoc, mul_left_comm, mul_comm] using this⟩ := by
      apply Subtype.ext; simp only [s, Subring.coe_mul]; ring
    rw [hsj]
    exact Ideal.mul_mem_right _ _ hej

include hO in

theorem exists_forall_isUnit_div
    (t : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldBar (N * q))) (ht : ∀ w ∈ W, t w ≠ 0)
    (hcop : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (w' : Place k (modularFunctionFieldC k N)) (hw' : w' ∈ W),
      w ≠ w' → 𝔪 R hqN W hWss hreg hw ⊔ 𝔪 R hqN W hWss hreg hw' = ⊤)
    (hcart : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ∃ b : ↥(BW R W), b ∉ 𝔪 R hqN W hWss hreg hw ∧
      ∀ (w' : Place k (modularFunctionFieldC k N)) (_ : w' ∈ W),
        t w * (b : ↥(modularFunctionFieldBar (N * q))) * (t w')⁻¹ ∈ R.nodeIntegers w') :
    ∃ f : ↥(modularFunctionFieldBar (N * q)), ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W),
      ∃ h : f * (t w)⁻¹ ∈ R.nodeIntegers w, IsUnit (⟨f * (t w)⁻¹, h⟩ : ↥(R.nodeIntegers w)) := by
  classical
  haveI hloc : ∀ i : ↥W, IsLocalRing ↥(R.nodeIntegers (i : Place k (modularFunctionFieldC k N))) :=
    fun i => isLocalRing_nodeIntegers R hqN W hWss hreg hO i.2

  have hcomap : ∀ i : ↥W, (maximalIdeal ↥(R.nodeIntegers (i : Place k (modularFunctionFieldC k N)))).comap
      (Subring.inclusion (BW_le R W i.2)) = 𝔪 R hqN W hWss hreg i.2 := by
    intro i
    ext b
    rw [Ideal.mem_comap, mem_𝔪_iff, ψ_apply, mem_maximalIdeal, mem_nonunits_iff,
      isUnit_iff_nodeEval_ne_zero R hqN W hWss hreg hO i.2, not_not]
  obtain ⟨f, hf⟩ := exists_forall_isUnit_div_of_cartier' (ι := ↥W) (BW R W)
    (fun i => R.nodeIntegers (i : Place k (modularFunctionFieldC k N))) (fun i => BW_le R W i.2)
    (fun i => t i) (fun i => ht i i.2)
    (fun i j hij => by
      rw [hcomap, hcomap]
      exact hcop i i.2 j j.2 (fun h => hij (Subtype.ext h)))
    (fun i => by
      obtain ⟨b, hb, hb'⟩ := hcart i i.2
      refine ⟨b, by rw [hcomap]; exact hb, fun j => hb' j j.2⟩)
  exact ⟨f, fun w hw => hf ⟨w, hw⟩⟩

end PartC

section PartD

omit [IsAlgClosed k] [DecidableEq k] in

private theorem ord_npow_nat {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (f : F) (n : ℕ) :
    v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]

include hO in

theorem seed_of_cop_of_correctors
    (y : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldBar (N * q)))
    (n : Place k (modularFunctionFieldC k N) → ℕ)
    (hyS : ∀ w ∈ W, y w ∈ R.nodeIntegers w)
    (hy₁ : ∀ w ∈ W, ∃ h : y w ∈ R.R₁.integers, R.R₁.residue ⟨y w, h⟩ ≠ 0)
    (hyV : ∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = w → V.ord (y w) = 0)
    (hy_ord1 : ∀ (w) (_ : w ∈ W) (h : y w ∈ R.R₁.integers),
      w.ord (R.residue₁ ⟨y w, h⟩ : ↥(modularFunctionFieldC k N)) = 1)
    (hcop : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) (w' : Place k (modularFunctionFieldC k N)) (hw' : w' ∈ W),
      w ≠ w' → 𝔪 R hqN W hWss hreg hw ⊔ 𝔪 R hqN W hWss hreg hw' = ⊤)
    (hcart : ∀ (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W), ∃ b : ↥(BW R W), b ∉ 𝔪 R hqN W hWss hreg hw ∧
      ∀ (w' : Place k (modularFunctionFieldC k N)) (_ : w' ∈ W),
        ((y w) ^ (n w))⁻¹ * (b : ↥(modularFunctionFieldBar (N * q))) * (y w') ^ (n w') ∈ R.nodeIntegers w') :
    ∃ f : ↥(modularFunctionFieldBar (N * q)), f ≠ 0 ∧
      (∃ h₁ : f ∈ R.R₁.integers, R.R₁.residue ⟨f, h₁⟩ ≠ 0 ∧
        (∀ (w) (_ : w ∈ W), w.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = -((n w : ℕ) : ℤ))) ∧
      (∀ (w) (hw : w ∈ W), ∃ h : f * y w ^ n w ∈ R.nodeIntegers w,
        IsUnit (⟨f * y w ^ n w, h⟩ : ↥(R.nodeIntegers w))) ∧
      (∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V = w → V.ord f = 0) := by
  classical

  by_cases hW0 : W = ∅
  · refine ⟨1, one_ne_zero, ⟨one_mem _, ?_, fun w hw => (Finset.notMem_empty w (hW0 ▸ hw)).elim⟩,
      fun w hw => (Finset.notMem_empty w (hW0 ▸ hw)).elim, fun w hw => (Finset.notMem_empty w (hW0 ▸ hw)).elim⟩
    have : (⟨(1 : ↥(modularFunctionFieldBar (N * q))), one_mem _⟩ : ↥R.R₁.integers) = 1 := rfl
    rw [this, map_one]; exact one_ne_zero
  obtain ⟨w₀, hw₀⟩ := Finset.nonempty_iff_ne_empty.mpr hW0

  have hy0 : ∀ w ∈ W, y w ≠ 0 := by
    intro w hw h0
    obtain ⟨h, hres⟩ := hy₁ w hw
    apply hres
    have : (⟨y w, h⟩ : ↥R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have ht : ∀ w ∈ W, ((y w) ^ (n w))⁻¹ ≠ 0 := fun w hw => inv_ne_zero (pow_ne_zero _ (hy0 w hw))

  obtain ⟨f, hf⟩ := exists_forall_isUnit_div R hqN W hWss hreg hO (fun w => ((y w) ^ (n w))⁻¹) ht hcop
    (fun w hw => by
      obtain ⟨b, hb, hb'⟩ := hcart w hw
      exact ⟨b, hb, fun w' hw' => by rw [inv_inv]; exact hb' w' hw'⟩)
  have hf' : ∀ (w) (hw : w ∈ W), ∃ h : f * y w ^ n w ∈ R.nodeIntegers w,
      IsUnit (⟨f * y w ^ n w, h⟩ : ↥(R.nodeIntegers w)) := by
    intro w hw
    obtain ⟨h, hu⟩ := hf w hw
    simp only [inv_inv] at h hu
    exact ⟨h, hu⟩

  obtain ⟨hmem₀, hu₀⟩ := hf' w₀ hw₀
  have hfy0 : f * y w₀ ^ n w₀ ≠ 0 := fun h0 => hu₀.ne_zero (Subtype.ext h0)
  have hf0 : f ≠ 0 := fun h0 => hfy0 (by rw [h0, zero_mul])

  obtain ⟨hy₁₀, hyres₀⟩ := hy₁ w₀ hw₀
  obtain ⟨yU, hyU⟩ := R.R₁.isUnit_of_residue_ne_zero hyres₀
  have hres₁u : R.R₁.residue ⟨f * y w₀ ^ n w₀, hmem₀.1⟩ ≠ 0 := by

    intro h0
    apply (isUnit_iff_nodeEval_ne_zero R hqN W hWss hreg hO hw₀ _).mp hu₀
    rw [nodeEval_apply]
    have hz0 : (R.nodeResidue₁ w₀ ⟨f * y w₀ ^ n w₀, hmem₀⟩ : ↥(modularFunctionFieldC k N)) = 0 := by
      rw [nodeResidue₁_apply, residue₁_apply]
      change R.ι (R.R₁.residue ⟨f * y w₀ ^ n w₀, hmem₀.1⟩) = 0
      rw [h0, map_zero]
    have hz : (⟨R.nodeResidue₁ w₀ ⟨f * y w₀ ^ n w₀, hmem₀⟩,
        residueFst_mem_of_mem_nodeIntegers R hqN W hWss hreg hw₀ ⟨f * y w₀ ^ n w₀, hmem₀⟩⟩ :
        ↥w₀.toValuationSubring) = 0 := Subtype.ext hz0
    rw [hz, map_zero]

  have hpowU : IsUnit (⟨y w₀ ^ n w₀, pow_mem hy₁₀ _⟩ : ↥R.R₁.integers) := by
    have : (⟨y w₀ ^ n w₀, pow_mem hy₁₀ _⟩ : ↥R.R₁.integers) = ⟨y w₀, hy₁₀⟩ ^ n w₀ := by
      apply Subtype.ext; simp
    rw [this]; exact (hyU ▸ yU.isUnit).pow _
  obtain ⟨hpow0, hpowinv⟩ := inv_mem_of_isUnit_vs R.R₁.integers (pow_mem hy₁₀ _) hpowU
  have hf₁ : f ∈ R.R₁.integers := by
    have : f = (f * y w₀ ^ n w₀) * (y w₀ ^ n w₀)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hpow0, mul_one]
    rw [this]; exact mul_mem hmem₀.1 hpowinv
  have hpowinvres : R.R₁.residue ⟨(y w₀ ^ n w₀)⁻¹, hpowinv⟩ ≠ 0 := by
    intro h0
    have h1 : (⟨y w₀ ^ n w₀, pow_mem hy₁₀ _⟩ : ↥R.R₁.integers) * ⟨(y w₀ ^ n w₀)⁻¹, hpowinv⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ hpow0)
    have := congrArg R.R₁.residue h1
    rw [map_mul, h0, mul_zero, map_one] at this
    exact zero_ne_one this
  have hfres : R.R₁.residue ⟨f, hf₁⟩ ≠ 0 := by
    have h1 : (⟨f, hf₁⟩ : ↥R.R₁.integers) = ⟨f * y w₀ ^ n w₀, hmem₀.1⟩ * ⟨(y w₀ ^ n w₀)⁻¹, hpowinv⟩ :=
      Subtype.ext (by simp only [MulMemClass.mk_mul_mk]; rw [mul_assoc, mul_inv_cancel₀ hpow0, mul_one])
    rw [h1, map_mul]
    exact mul_ne_zero hres₁u hpowinvres
  refine ⟨f, hf0, ⟨hf₁, hfres, ?_⟩, hf', ?_⟩
  ·
    intro w hw
    obtain ⟨hmem, hu⟩ := hf' w hw
    obtain ⟨hyw₁, -⟩ := hy₁ w hw
    have hordu := ord_residueFst_eq_zero_of_isUnit R hqN W hWss hreg hw hu
    rw [nodeResidue₁_apply] at hordu

    have hsplit : (⟨f * y w ^ n w, hmem.1⟩ : ↥R.R₁.integers) = ⟨f, hf₁⟩ * ⟨y w, hyw₁⟩ ^ n w := by
      apply Subtype.ext; simp
    change w.ord (R.residue₁ ⟨f * y w ^ n w, hmem.1⟩ : ↥(modularFunctionFieldC k N)) = 0 at hordu
    rw [hsplit, map_mul, map_pow] at hordu
    have hy1 := hy_ord1 w hw hyw₁
    have hyne : (R.residue₁ ⟨y w, hyw₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hy1; exact zero_ne_one hy1
    have hfne : (R.residue₁ ⟨f, hf₁⟩ : ↥(modularFunctionFieldC k N)) ≠ 0 := by
      intro h0
      apply hfres
      have : R.residue₁ ⟨f, hf₁⟩ = 0 := h0
      rw [residue₁_apply] at this
      exact (map_eq_zero_iff R.ι R.ι.injective).mp this
    rw [w.ord_mul hfne (pow_ne_zero _ hyne), ord_npow_nat, hy1, mul_one] at hordu
    omega
  ·
    intro w hw V hV
    obtain ⟨hmem, hu⟩ := hf' w hw
    have h0 := ord_eq_zero_of_isUnit R hu V hV
    change V.ord (f * y w ^ n w) = 0 at h0
    rw [V.ord_mul hf0 (pow_ne_zero _ (hy0 w hw)), ord_npow_nat, hyV w hw V hV, mul_zero, add_zero] at h0
    exact h0

end PartD

end P2mWs18Seed0
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg.P2mWs18Seed0"

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
        (∀ (w) (_ : w ∈ W), w.ord (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k N)) = -((n w : ℕ) : ℤ))) ∧
      (∀ (w) (hw : w ∈ W), ∃ h : f * y w ^ n w ∈ R.nodeIntegers w,
        IsUnit (⟨f * y w ^ n w, h⟩ : ↥(R.nodeIntegers w))) ∧
      (∀ w ∈ W, ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
        P.reduceFst V = w → V.ord f = 0) := by
  classical
  have hWss : ∀ w ∈ W, w ∈ ssPlaces q N k := fun w hw => (hW w).mp hw
  exact P2mWs18Seed0.seed_of_cop_of_correctors R hqN W hWss hreg hO y n hyS hy₁ hyV hy_ord1
    (fun w hw w' hw' hne => P2mWs18Seed0.𝔪_sup_𝔪_eq_top R hqN W hWss hreg hw hw' hne)
    (fun w hw => P2mWs18Seed0.exists_corrector R hqN W hWss hreg hO hmodel hval y n hyS hy₁ hyV hvert hw)

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg.P2mWs18Seed0"

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_isUnit_mul_pow_nodeIntegers_and_ord_residueFst_eq_neg (solution)
