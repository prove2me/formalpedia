-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_field_nonempty_nodeCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/222c9d92-1672-5972-b1c9-d711fbf5206d

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_FinFlatHopf_inertiaFixed_valuationSubring_dvr_fixer_le_inertia
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_nonempty_nodeCoordinates
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_field_nonempty_nodeCoordinates
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl"
p2m_attr_erase "simp" "ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace InertiaFixedNodeCoordinates

private theorem liesOverPrime_of_ringHom {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) : A.LiesOverPrime q := by
  have hmem : ((q : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
    intro hu
    have h1 : IsUnit (red ((q : ℕ) : ↥A)) := hu.map red
    rw [map_natCast, CharP.cast_eq_zero k q] at h1
    exact not_isUnit_zero h1
  have h2 : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr hmem
  have h3 : (((q : ℕ) : ↥A) : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) := rfl
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [← h3]
  exact h2

private def inertiaFixedSubring (A : ValuationSubring (AlgebraicClosure ℚ)) : Subring (AlgebraicClosure ℚ) where
  carrier := {x | x ∈ A ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ x = x}
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨mul_mem hx hy, fun σ hσ => by rw [map_mul, hx' σ hσ, hy' σ hσ]⟩
  one_mem' := ⟨one_mem _, fun σ _ => map_one σ⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨add_mem hx hy, fun σ hσ => by rw [map_add, hx' σ hσ, hy' σ hσ]⟩
  zero_mem' := ⟨zero_mem _, fun σ _ => map_zero σ⟩
  neg_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨neg_mem hx, fun σ hσ => by rw [map_neg, hx' σ hσ]⟩

private theorem mem_inertiaFixedSubring_iff (A : ValuationSubring (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) :
    x ∈ inertiaFixedSubring A ↔ x ∈ A ∧ ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ x = x :=
  Iff.rfl

private theorem mem_coeffSubring_iff (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : AlgebraicClosure ℚ) : x ∈ NodeLocalized.coeffSubring A K ↔ x ∈ A ∧ x ∈ K :=
  Iff.rfl

private theorem redRestrict_eq_zero_iff {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K, σ z = z) (d : ↥(NodeLocalized.coeffSubring A K)) :
    NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) * d' := by
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  constructor
  · intro hd
    have hdA : (d : AlgebraicClosure ℚ) ∈ A := ((mem_coeffSubring_iff A K _).mp d.2).1
    have hdK : (d : AlgebraicClosure ℚ) ∈ K := ((mem_coeffSubring_iff A K _).mp d.2).2
    have hred : red ⟨(d : AlgebraicClosure ℚ), hdA⟩ = 0 := hd
    by_cases hd0 : d = 0
    · exact ⟨0, by rw [hd0, mul_zero]⟩

    obtain ⟨⟨-, hstruct⟩, -, -⟩ := FinFlatHopf.inertiaFixed_valuationSubring_dvr_fixer_le_inertia q A
      (liesOverPrime_of_ringHom red) (inertiaFixedSubring A) (fun _ => Iff.rfl)
    have hdB : (d : AlgebraicClosure ℚ) ∈ inertiaFixedSubring A := ⟨hdA, fun σ hσ => hfix σ hσ _ hdK⟩
    have hne : (⟨(d : AlgebraicClosure ℚ), hdB⟩ : ↥(inertiaFixedSubring A)) ≠ 0 := by
      intro h
      apply hd0
      have h' : (d : AlgebraicClosure ℚ) = 0 := by
        have h'' := congrArg Subtype.val h
        rwa [Subring.coe_zero] at h''
      exact Subtype.ext (by rw [h', Subring.coe_zero])
    obtain ⟨n, u, hx⟩ := hstruct _ hne
    cases n with
    | zero =>

      exfalso
      rw [pow_zero, mul_one] at hx
      have hdu : IsUnit (⟨(d : AlgebraicClosure ℚ), hdB⟩ : ↥(inertiaFixedSubring A)) := by
        rw [hx]
        exact Units.isUnit u
      obtain ⟨v, hv⟩ := hdu.exists_right_inv
      have hval : (d : AlgebraicClosure ℚ) * ((v : ↥(inertiaFixedSubring A)) : AlgebraicClosure ℚ) = 1 := by
        have h := congrArg Subtype.val hv
        simpa only [Subring.coe_mul, Subring.coe_one, Subtype.coe_mk] using h
      have hvA : ((v : ↥(inertiaFixedSubring A)) : AlgebraicClosure ℚ) ∈ A :=
        ((mem_inertiaFixedSubring_iff A _).mp v.2).1
      have hunit : IsUnit (⟨(d : AlgebraicClosure ℚ), hdA⟩ : ↥A) :=
        IsUnit.of_mul_eq_one (⟨((v : ↥(inertiaFixedSubring A)) : AlgebraicClosure ℚ), hvA⟩ : ↥A) (Subtype.ext hval)
      exact (hunit.map red).ne_zero hred
    | succ m =>

      have hxval : (d : AlgebraicClosure ℚ)
          = ((u : ↥(inertiaFixedSubring A)) : AlgebraicClosure ℚ) * ((q : ℕ) : AlgebraicClosure ℚ) ^ (m + 1) := by
        have h := congrArg Subtype.val hx
        simpa only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, Subtype.coe_mk] using h
      have huA : ((u : ↥(inertiaFixedSubring A)) : AlgebraicClosure ℚ) ∈ A :=
        ((mem_inertiaFixedSubring_iff A _).mp (u : ↥(inertiaFixedSubring A)).2).1
      have huK : ((u : ↥(inertiaFixedSubring A)) : AlgebraicClosure ℚ) ∈ K := by
        have h : ((u : ↥(inertiaFixedSubring A)) : AlgebraicClosure ℚ)
            = (d : AlgebraicClosure ℚ) * (((q : ℕ) : AlgebraicClosure ℚ) ^ (m + 1))⁻¹ := by
          rw [hxval, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]
        rw [h]
        exact mul_mem hdK (inv_mem (pow_mem (natCast_mem K q) _))
      refine ⟨⟨((u : ↥(inertiaFixedSubring A)) : AlgebraicClosure ℚ) * ((q : ℕ) : AlgebraicClosure ℚ) ^ m,
        (mem_coeffSubring_iff A K _).mpr ⟨?_, ?_⟩⟩, ?_⟩
      · exact mul_mem huA (pow_mem (natCast_mem A q) m)
      · exact mul_mem huK (pow_mem (natCast_mem K q) m)
      · apply Subtype.ext
        show (d : AlgebraicClosure ℚ)
          = (((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ)
            * (((u : ↥(inertiaFixedSubring A)) : AlgebraicClosure ℚ) * ((q : ℕ) : AlgebraicClosure ℚ) ^ m)
        rw [Subring.coe_natCast, hxval]
        ring
  · rintro ⟨d', rfl⟩
    rw [map_mul, map_natCast, CharP.cast_eq_zero k q, zero_mul]

end InertiaFixedNodeCoordinates

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N)
    (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k N))) (hW : ∀ w ∈ W, w ∈ ssPlaces q N k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ z ∈ K, σ z = z) ∧
      (∀ d : ↥(NodeLocalized.coeffSubring A K),
          NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) * d') ∧
      Nonempty (R.NodeCoordinates K w) := by
  have hcore :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.exists_inertiaFixed_nonempty_nodeCoordinates
      R hqN hmodel W hW hreg hval w hw
  obtain ⟨K, hK, hfix, hc⟩ := hcore
  exact ⟨K, hK, hfix, fun d => InertiaFixedNodeCoordinates.redRestrict_eq_zero_iff red K hfix d, hc⟩

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_field_nonempty_nodeCoordinates
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_inertiaFixed_field_nonempty_nodeCoordinates (solution)
