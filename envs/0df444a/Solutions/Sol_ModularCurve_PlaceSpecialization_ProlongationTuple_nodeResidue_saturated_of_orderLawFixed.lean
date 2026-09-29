-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_saturated_of_orderLawFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/974b80f6-1be8-5995-92ef-d189ab7e2ec5

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_mem_closure_redRestrict
import Theorems.Thm_ModularCurve_exists_ne_zero_mul_eq_isIntegral_of_mem_closure_of_mem_valuationSubring
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_heckeAlphaBar_mem_nodeIntegersOver_and_nodeResidue_eq_coeffMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isUnit_of_not_hasValue_nodeResidue_zero_of_isLocalRing
import Theorems.Thm_ModularCurve_exists_fieldOver_lift_isIntegral_of_isIntegral
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces_univ
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_orderLawFixed
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace Ws18
namespace SatAssembly

section PlaceLemmas
variable {L F : Type*} [Field L] [Field F] [Algebra L F]

theorem mem_of_ord_nonneg (v : Place L F) {f : F} (hf0 : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem not_hasValue_zero_of_inv_mem (v : Place L F) {s : F} (hs0 : s ≠ 0) (_hs : s ∈ v.toValuationSubring)
    (hsi : s⁻¹ ∈ v.toValuationSubring) : ¬ v.HasValue s (0 : L) := by
  rintro ⟨h, hres⟩
  rw [map_zero] at hres
  have hunit : IsUnit (⟨s, h⟩ : v.toValuationSubring) :=
    isUnit_iff_exists_inv.mpr ⟨⟨s⁻¹, hsi⟩, Subtype.ext (mul_inv_cancel₀ hs0)⟩
  have hmem : (⟨s, h⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem hunit

end PlaceLemmas

section RangeField

theorem redRestrict_natCast_q {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    NodeLocalized.redRestrict red K (q : ↥(NodeLocalized.coeffSubring A K)) = 0 := by
  rw [map_natCast]; exact CharP.cast_eq_zero k q

theorem not_isUnit_natCast_q {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ¬ IsUnit (q : ↥(NodeLocalized.coeffSubring A K)) := by
  intro hu
  have h := hu.map (NodeLocalized.redRestrict red K)
  rw [redRestrict_natCast_q red K] at h
  exact not_isUnit_zero h

theorem isUnit_of_redRestrict_ne_zero {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (c : ↥(NodeLocalized.coeffSubring A K)) (hc : NodeLocalized.redRestrict red K c ≠ 0) :
    IsUnit c := by
  have hqQ : ((q : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := by
    rw [Subring.coe_natCast]; exact Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with heq | hdvr
  ·
    exfalso
    apply not_isUnit_natCast_q red K
    have hinvK : ((q : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)⁻¹ ∈ NodeLocalized.coeffSubring A K := by
      have hqK : ((q : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ∈ K := (q : ↥(NodeLocalized.coeffSubring A K)).2.2
      rw [heq]
      change ((q : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)⁻¹ ∈ K
      exact inv_mem hqK
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvK⟩, Subtype.ext (mul_inv_cancel₀ hqQ)⟩
  · haveI := hdvr
    by_contra hnu
    have hc0 : c ≠ 0 := by rintro rfl; exact hc (map_zero _)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(NodeLocalized.coeffSubring A K)
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc0 hϖ
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact hnu (hn.symm.isUnit isUnit_one)
    have hq0 : (q : ↥(NodeLocalized.coeffSubring A K)) ≠ 0 := by
      intro h0; apply hqQ; rw [h0]; rfl
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hq0 hϖ
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [pow_zero] at he
      exact not_isUnit_natCast_q red K (he.symm.isUnit isUnit_one)
    have hce : Associated (c ^ e) ((q : ↥(NodeLocalized.coeffSubring A K)) ^ n) := by
      have h1 : Associated (c ^ e) (ϖ ^ (n * e)) := by rw [pow_mul]; exact hn.pow_pow
      have h2 : Associated ((q : ↥(NodeLocalized.coeffSubring A K)) ^ n) (ϖ ^ (n * e)) := by
        rw [mul_comm, pow_mul]; exact he.pow_pow
      exact h1.trans h2.symm
    obtain ⟨u, hu⟩ := hce
    have hred := congrArg (NodeLocalized.redRestrict red K) hu
    rw [map_mul, map_pow, map_pow, redRestrict_natCast_q red K, zero_pow hn0] at hred
    have huu : IsUnit (NodeLocalized.redRestrict red K (u : ↥(NodeLocalized.coeffSubring A K))) := u.isUnit.map _
    have hce0 : NodeLocalized.redRestrict red K c ^ e = 0 := (mul_eq_zero.mp hred).resolve_right huu.ne_zero
    exact hc ((pow_eq_zero_iff he0).mp hce0)

noncomputable def rangeField {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] : Subfield k :=
  { (NodeLocalized.redRestrict red K).range with
    inv_mem' := by
      rintro x ⟨c, rfl⟩
      by_cases hc : NodeLocalized.redRestrict red K c = 0
      · refine ⟨0, ?_⟩
        rw [map_zero]; simp [hc]
      · obtain ⟨v, hv⟩ := (isUnit_of_redRestrict_ne_zero red K c hc).exists_right_inv
        refine ⟨v, ?_⟩
        have h := congrArg (NodeLocalized.redRestrict red K) hv
        rw [map_mul, map_one] at h
        change NodeLocalized.redRestrict red K v = (NodeLocalized.redRestrict red K c)⁻¹
        exact eq_inv_of_mul_eq_one_right h }

theorem mem_rangeField_iff {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (x : k) :
    x ∈ rangeField red K ↔ x ∈ Set.range (NodeLocalized.redRestrict red K) := by
  change x ∈ (NodeLocalized.redRestrict red K).range ↔ _
  rw [RingHom.mem_range]; rfl

theorem closure_range_redRestrict_le {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    ∀ x ∈ Subfield.closure (Set.range (NodeLocalized.redRestrict red K)), x ∈ Set.range (NodeLocalized.redRestrict red K) := by
  intro x hx
  have hle : Subfield.closure (Set.range (NodeLocalized.redRestrict red K)) ≤ rangeField red K :=
    Subfield.closure_le.mpr fun y hy => (mem_rangeField_iff red K y).mpr hy
  exact (mem_rangeField_iff red K x).mp (hle hx)

theorem exists_coeffMap_redRestrict_eq {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : LaurentSeries k) (hx : ∀ n : ℤ, x.coeff n ∈ Set.range (NodeLocalized.redRestrict red K)) :
    ∃ h₀ : LaurentSeries ↥(NodeLocalized.coeffSubring A K), coeffMap (NodeLocalized.redRestrict red K) h₀ = x := by
  classical
  choose c hc using hx
  let cf : ℤ → ↥(NodeLocalized.coeffSubring A K) := fun n => if x.coeff n = 0 then 0 else c n
  have hsupp : Function.support cf ⊆ Function.support x.coeff := by
    intro n hn
    simp only [Function.mem_support, cf] at hn ⊢
    intro h0; apply hn; simp [h0]
  refine ⟨⟨cf, x.isPWO_support'.mono hsupp⟩, ?_⟩
  ext n
  rw [coeffMap_coeff]
  change NodeLocalized.redRestrict red K (cf n) = x.coeff n
  simp only [cf]
  split_ifs with h0
  · rw [map_zero, h0]
  · exact hc n

end RangeField

section Branch
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}

theorem branch (R : ProlongationTuple P) (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N))
    (v : Place k (modularFunctionFieldC k N)) (hjv : (jGeomGen k N : ↥(modularFunctionFieldC k N)) ∈ v.toValuationSubring)
    (ρ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N))
    (hρrat : ∀ x : ↥(R.nodeIntegersOver K w), ρ x ∈ Subfield.closure (Set.range (fun c : ↥(Subfield.closure (Set.range (NodeLocalized.redRestrict red K))) => algebraMap k ↥(modularFunctionFieldC k N) (Subtype.val c)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}))
    (hlift : ∀ (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g : ↥(modularFunctionFieldBar N)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap (NodeLocalized.coeffSubring A K).subtype y →
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver N K →
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) g →
      ∃ x : ↥(R.nodeIntegersOver K w), ((ρ x : ↥(modularFunctionFieldC k N)) : LaurentSeries k) = coeffMap (NodeLocalized.redRestrict red K) y)
    (hunit : ∀ s : ↥(R.nodeIntegersOver K w), ¬ v.HasValue (ρ s) (0 : k) → IsUnit s) :
    ∀ g g' : ↥(R.nodeIntegersOver K w), 0 < v.ord (ρ g) → v.ord (ρ g') = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w), ρ g = ρ g' * ρ b := by
  intro g g' hg hg'
  have hg'0 : ρ g' ≠ 0 := by intro h; rw [h, Place.ord_zero] at hg'; exact zero_ne_one hg'
  have hg0 : ρ g ≠ 0 := by intro h; rw [h, Place.ord_zero] at hg; exact lt_irrefl _ hg
  set f : ↥(modularFunctionFieldC k N) := ρ g * (ρ g')⁻¹ with hf
  have hf0 : f ≠ 0 := mul_ne_zero hg0 (inv_ne_zero hg'0)
  have hford : 0 ≤ v.ord f := by
    rw [hf, v.ord_mul hg0 (inv_ne_zero hg'0), v.ord_inv, hg']
    omega
  have hfv : f ∈ v.toValuationSubring := mem_of_ord_nonneg v hf0 hford
  have hfF : f ∈ Subfield.closure (Set.range (fun c : ↥(Subfield.closure (Set.range (NodeLocalized.redRestrict red K))) => algebraMap k ↥(modularFunctionFieldC k N) (Subtype.val c)) ∪
          {(jGeomGen k N : ↥(modularFunctionFieldC k N)), (jNGeomGen k N : ↥(modularFunctionFieldC k N))}) :=
    Subfield.mul_mem _ (hρrat g) (Subfield.inv_mem _ (hρrat g'))

  obtain ⟨abar, sbar, haint, hsint, -, -, hacoeff, hscoeff, hs0, hsw, hsiw, hfs⟩ :=
    ModularCurve.exists_ne_zero_mul_eq_isIntegral_of_mem_closure_of_mem_valuationSubring (N := N) hqN
      (Subfield.closure (Set.range (NodeLocalized.redRestrict red K))) v hjv f hfF hfv

  obtain ⟨ha0, hha0⟩ := exists_coeffMap_redRestrict_eq red K ((abar : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
    (fun n => closure_range_redRestrict_le red K _ (hacoeff n))
  obtain ⟨hs0', hhs0⟩ := exists_coeffMap_redRestrict_eq red K ((sbar : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
    (fun n => closure_range_redRestrict_le red K _ (hscoeff n))

  obtain ⟨ya, a, hay, hared, haK, haint0⟩ :=
    ModularCurve.exists_fieldOver_lift_isIntegral_of_isIntegral red hqN K ha0 abar hha0 haint
  obtain ⟨ys, s, hsy, hsred, hsK, hsint0⟩ :=
    ModularCurve.exists_fieldOver_lift_isIntegral_of_isIntegral red hqN K hs0' sbar hhs0 hsint

  obtain ⟨aS, haS⟩ := hlift ya a hay haK haint0
  obtain ⟨sS, hsS⟩ := hlift ys s hsy hsK hsint0
  have hra : ρ aS = abar := Subtype.ext (by rw [haS, hared])
  have hrs : ρ sS = sbar := Subtype.ext (by rw [hsS, hsred])

  have hsunit : IsUnit sS := hunit sS (by rw [hrs]; exact not_hasValue_zero_of_inv_mem v hs0 hsw hsiw)
  obtain ⟨u, hu⟩ := hsunit
  refine ⟨aS * ↑u⁻¹, ?_⟩
  have hinv : ρ (↑u⁻¹ : ↥(R.nodeIntegersOver K w)) = sbar⁻¹ := by
    have h1 : ρ (↑u⁻¹ : ↥(R.nodeIntegersOver K w)) * ρ sS = 1 := by
      rw [← map_mul, ← hu, Units.inv_mul, map_one]
    rw [hrs] at h1
    exact eq_inv_of_mul_eq_one_left h1
  rw [map_mul, hra, hinv, ← hfs, hf]
  field_simp

end Branch

end Ws18.SatAssembly

section Solution

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel) (hO : R.OrderLawFixed)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩) ∧
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩) := by

  haveI : IsLocalRing ↥(R.nodeIntegersOver K w) :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.isLocalRing_nodeIntegersOver_of_orderLawFixed_of_regularityLaw
      R hqN hO W hW hreg K w hw
  have hwss : w ∈ ssPlaces q N k := hW w hw
  have hwss2 : arithFrobC q k N • w ∈ ssPlaces q N k := ModularCurve.arithFrobC_smul_mem_ssPlaces_univ q N k w hwss
  have hjw : (jGeomGen k N : ↥(modularFunctionFieldC k N)) ∈ w.toValuationSubring := hwss.2.1.1
  have hjw2 : (jGeomGen k N : ↥(modularFunctionFieldC k N)) ∈ (arithFrobC q k N • w).toValuationSubring := hwss2.2.1.1

  let ρ₁ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
    (R.nodeResidue₁ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))
  let ρ₂ : ↥(R.nodeIntegersOver K w) →+* ↥(modularFunctionFieldC k N) :=
    (R.nodeResidue₂ w).comp (Subring.inclusion (R.nodeIntegersOver_le K w))
  have hρ₁ : ∀ x : ↥(R.nodeIntegersOver K w), ρ₁ x = R.nodeResidue₁ w ⟨x, x.2.1⟩ := fun _ => rfl
  have hρ₂ : ∀ x : ↥(R.nodeIntegersOver K w), ρ₂ x = R.nodeResidue₂ w ⟨x, x.2.1⟩ := fun _ => rfl
  refine ⟨?_, ?_⟩
  ·
    intro g g' hg hg'
    exact Ws18.SatAssembly.branch R hqN K w w hjw ρ₁
      (fun x => (ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_mem_closure_redRestrict R hqN K w x).1)
      (fun y a hay haK haint => by
        obtain ⟨⟨h, hres⟩, -⟩ :=
          ModularCurve.PlaceSpecialization.ProlongationTuple.heckeAlphaBar_mem_nodeIntegersOver_and_nodeResidue_eq_coeffMap
            R hqN K w hwss y a hay haK haint
        exact ⟨⟨heckeAlphaBar (AlgebraicClosure ℚ) N q a, h⟩, hres⟩)
      (fun s hs =>
        ModularCurve.PlaceSpecialization.ProlongationTuple.isUnit_of_not_hasValue_nodeResidue_zero_of_isLocalRing
          R hqN W hW hreg K w hw s (Or.inl hs))
      g g' hg hg'
  ·
    intro g g' hg hg'
    exact Ws18.SatAssembly.branch R hqN K w (arithFrobC q k N • w) hjw2 ρ₂
      (fun x => (ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_mem_closure_redRestrict R hqN K w x).2)
      (fun y a hay haK haint => by
        obtain ⟨-, ⟨h, hres⟩⟩ :=
          ModularCurve.PlaceSpecialization.ProlongationTuple.heckeAlphaBar_mem_nodeIntegersOver_and_nodeResidue_eq_coeffMap
            R hqN K w hwss y a hay haK haint
        exact ⟨⟨heckeBetaBar (AlgebraicClosure ℚ) N q a, h⟩, hres⟩)
      (fun s hs =>
        ModularCurve.PlaceSpecialization.ProlongationTuple.isUnit_of_not_hasValue_nodeResidue_zero_of_isLocalRing
          R hqN W hW hreg K w hw s (Or.inr hs))
      g g' hg hg'

end Solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_orderLawFixed
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_orderLawFixed (solution)
