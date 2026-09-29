-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7c1affb5-c199-511d-8eee-8320719c2aec

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Pic0_subsingleton_of_genusFF_eq_zero
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective_of_level
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.cuspCount_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option Elab.async false
set_option autoImplicit false

p2m_open "AlgebraicCurve~genus"
p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel.ModularCurve.PlaceSpecialization"

section Counting

variable {α β : Type*}

private theorem mapDomain_apply_eq_sum [DecidableEq β] (h : α → β) (x : α →₀ ℤ) (b : β) :
    Finsupp.mapDomain h x b = ∑ a ∈ x.support, (if h a = b then x a else 0) := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.single_apply, Finsupp.sum]

private theorem mapDomain_apply_eq_zero (h : α → β) (x : α →₀ ℤ) (b : β)
    (hb : ∀ a ∈ x.support, h a ≠ b) : Finsupp.mapDomain h x b = 0 := by
  classical
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_eq_zero fun a ha => if_neg (hb a ha)

private theorem mapDomain_apply_pos (h : α → β) (x : α →₀ ℤ) (b : β)
    (hnn : ∀ a ∈ x.support, h a = b → 0 < x a) (a₀ : α) (ha₀ : a₀ ∈ x.support)
    (hb₀ : h a₀ = b) : 0 < Finsupp.mapDomain h x b := by
  classical
  rw [mapDomain_apply_eq_sum]
  have hle : ∀ a ∈ x.support, (0 : ℤ) ≤ (if h a = b then x a else 0) := fun a ha => by
    split_ifs with hab
    · exact (hnn a ha hab).le
    · exact le_rfl
  have hone := Finset.single_le_sum hle ha₀
  rw [if_pos hb₀] at hone
  exact (hnn a₀ ha₀ hb₀).trans_le hone

private theorem mapDomain_apply_ne (h h' : α → β) (x x' : α →₀ ℤ) (b : β)
    (hkey : Finsupp.mapDomain h x b = Finsupp.mapDomain h' x' b)
    (hz : ∀ a ∈ x'.support, h' a ≠ b) (hnn : ∀ a ∈ x.support, h a = b → 0 < x a)
    (a₀ : α) (ha₀ : a₀ ∈ x.support) (hb₀ : h a₀ = b) : False := by
  have h0 := mapDomain_apply_eq_zero h' x' b hz
  have h1 := mapDomain_apply_pos h x b hnn a₀ ha₀ hb₀
  rw [hkey, h0] at h1
  exact lt_irrefl _ h1

end Counting

section Transfer

variable
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P P' : PlaceSpecialization A q N data hKr k red hα hβ}

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₁_indep (R : ProlongationTuple P) (R' : ProlongationTuple P')
    (f : modularFunctionFieldBar (N * q)) (h : f ∈ R.R₁.integers) (h' : f ∈ R'.R₁.integers) :
    R.residue₁ ⟨f, h⟩ = R'.residue₁ ⟨f, h'⟩ := by
  have hf : (f : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring red := (R.mem_integersFst_iff f).mp h
  obtain ⟨_, e⟩ := R.residue₁_eq_modularRedLocHom f hf
  obtain ⟨_, e'⟩ := R'.residue₁_eq_modularRedLocHom f hf
  apply Subtype.ext
  rw [ProlongationTuple.residue₁_apply, ProlongationTuple.residue₁_apply]
  exact e.trans e'.symm

set_option synthInstance.maxHeartbeats 1600000 in

private theorem residue₂_indep (R : ProlongationTuple P) (R' : ProlongationTuple P')
    (f : modularFunctionFieldBar (N * q)) (h : f ∈ R.R₂.integers) (h' : f ∈ R'.R₂.integers) :
    R.residue₂ ⟨f, h⟩ = R'.residue₂ ⟨f, h'⟩ := by
  have key := residue₁_indep R R' (ProlongationTuple.atkinLehnerBar N q f)
    ((R.mem_integers₂_iff f).mp h) ((R'.mem_integers₂_iff f).mp h')
  rw [ProlongationTuple.residue₁_apply, ProlongationTuple.residue₁_apply] at key
  rw [ProlongationTuple.residue₂_apply, ProlongationTuple.residue₂_apply, R.residue₂_eq f h, R'.residue₂_eq f h']
  exact key

end Transfer

private theorem g0_genusFF_modularFunctionFieldBar_eq_zero
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k]
    (hng : ¬ (0 < genusFF k ↥(ModularCurve.modularFunctionFieldC k N))) (hqN : ¬ q ∣ N) :
    genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) = 0 := by
  have h0 : genusFF k ↥(ModularCurve.modularFunctionFieldC k N) = 0 := Nat.eq_zero_of_not_pos hng
  have hN : (N : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N).mp h)
  rw [← ModularCurve.genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar k N hN,
    ← ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q N hqN]
  exact h0

private theorem g0_isPrincipal_single_sub_single_of_genusFF_eq_zero {N : ℕ} [NeZero N]
    (hg : genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) = 0)
    (w₀ w₁ : Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N)) :
    Divisor.IsPrincipal (Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1) := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar N
  haveI := ModularCurve.essFiniteType_modularFunctionFieldBar N
  haveI : Subsingleton (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N)) :=
    AlgebraicCurve.Pic0.subsingleton_of_genusFF_eq_zero hg
  have hdeg : Divisor.degree (Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1) = 0 := by
    rw [map_sub, Divisor.degree_single, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed w₀,
      IsCurveOver.deg_eq_one_of_isAlgClosed w₁]
    simp
  let D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar N)) :=
    ⟨Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1, Divisor.mem_degZero.mpr hdeg⟩
  have hD : Pic0.mk D = 0 := Subsingleton.elim _ _
  have hmem : D ∈ (Divisor.principal (K := AlgebraicClosure ℚ)
      (F := ↥(ModularCurve.modularFunctionFieldBar N))).addSubgroupOf Divisor.degZero :=
    (QuotientAddGroup.eq_zero_iff D).mp hD
  exact Divisor.mem_principal.mp (AddSubgroup.mem_addSubgroupOf.mp hmem)

private theorem g0_exists_ord_eq_single_sub_single
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k]
    (hng : ¬ (0 < genusFF k ↥(ModularCurve.modularFunctionFieldC k N))) (hqN : ¬ q ∣ N)
    (w₀ w₁ : Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N)) :
    ∃ g : ModularCurve.modularFunctionFieldBar N, g ≠ 0 ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
        W.ord g = (Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1 :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) W := by
  obtain ⟨g, hg0, hg⟩ := g0_isPrincipal_single_sub_single_of_genusFF_eq_zero
    (g0_genusFF_modularFunctionFieldBar_eq_zero hng hqN) w₀ w₁
  exact ⟨g, hg0, fun W => (hg W).symm⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem atkinLehnerBar_heckeAlphaBar_and_heckeBetaBar {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N)
    (x : modularFunctionFieldBar N) :
    ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q x) =
        heckeBetaBar (AlgebraicClosure ℚ) N q x ∧
      ProlongationTuple.atkinLehnerBar N q (heckeBetaBar (AlgebraicClosure ℚ) N q x) =
        heckeAlphaBar (AlgebraicClosure ℚ) N q x := by
  have hσ : IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
      (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)
  obtain ⟨h₁, h₂⟩ :=
    geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) N q (atkinLehnerInvolutionFull N q) hσ
  exact ⟨AlgHom.congr_fun h₁ x, AlgHom.congr_fun h₂ x⟩

set_option synthInstance.maxHeartbeats 1600000 in

private theorem exists_smul_commonUnit_of_atkinLehnerBar_eq
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : PlaceSpecialization.ProlongationTuple P)
    (H : modularFunctionFieldBar (N * q)) (hH : H ≠ 0) (hinv : ProlongationTuple.atkinLehnerBar N q H = H) :
    ∃ (c : AlgebraicClosure ℚ) (_ : c ≠ 0) (h₁ : c • H ∈ R.R₁.integers) (h₂ : c • H ∈ R.R₂.integers),
      R.R₁.residue ⟨c • H, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨c • H, h₂⟩ ≠ 0 := by
  obtain ⟨c, h₁, hres₁⟩ := R.R₁.exists_smul_mem H hH
  have hc : c ≠ 0 := R.R₁.smul_const_ne_zero h₁ hres₁
  have hinv' : ProlongationTuple.atkinLehnerBar N q (c • H) = c • H := by
    rw [Algebra.smul_def, map_mul, hinv, AlgEquiv.commutes]
  have h₂ : c • H ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, hinv']
    exact h₁
  refine ⟨c, hc, h₁, h₂, hres₁, ?_⟩
  rw [R.residue₂_eq (c • H) h₂]
  have hsub : (⟨ProlongationTuple.atkinLehnerBar N q (c • H),
      (R.mem_integersFst_iff _).mpr ((R.mem_integersSnd_iff _).mp h₂)⟩ : R.R₁.integers) = ⟨c • H, h₁⟩ :=
    Subtype.ext hinv'
  rw [hsub]
  exact hres₁

set_option synthInstance.maxHeartbeats 1600000 in

private theorem commonUnit_transfer
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P P' : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : PlaceSpecialization.ProlongationTuple P) (R' : PlaceSpecialization.ProlongationTuple P')
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0) :
    ∃ (h₁' : f ∈ R'.R₁.integers) (h₂' : f ∈ R'.R₂.integers),
      R'.R₁.residue ⟨f, h₁'⟩ ≠ 0 ∧ R'.R₂.residue ⟨f, h₂'⟩ ≠ 0 := by
  have h₁' : f ∈ R'.R₁.integers := (R'.mem_integersFst_iff f).mpr ((R.mem_integersFst_iff f).mp h₁)
  have h₂' : f ∈ R'.R₂.integers := (R'.mem_integersSnd_iff f).mpr ((R.mem_integersSnd_iff f).mp h₂)
  refine ⟨h₁', h₂', ?_, ?_⟩
  · intro h0
    apply hr₁
    apply R.ι.injective
    have e := residue₁_indep R R' f h₁ h₁'
    rw [ProlongationTuple.residue₁_apply, ProlongationTuple.residue₁_apply, h0, map_zero] at e
    rw [e, map_zero]
  · intro h0
    apply hr₂
    apply R.ι.injective
    have e := residue₂_indep R R' f h₂ h₂'
    rw [ProlongationTuple.residue₂_apply, ProlongationTuple.residue₂_apply, h0, map_zero] at e
    rw [e, map_zero]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem commonUnit_standin
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (R' : PlaceSpecialization.ProlongationTuple P')
    (g : modularFunctionFieldBar N) (hg : g ≠ 0)
    (w₀ w₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hdiv : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      w.ord g = (Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1 :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) w) :
    ∃ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
      (h₁' : f ∈ R'.R₁.integers) (h₂' : f ∈ R'.R₂.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨f, h₂⟩ ≠ 0 ∧
      R'.R₁.residue ⟨f, h₁'⟩ ≠ 0 ∧ R'.R₂.residue ⟨f, h₂'⟩ ≠ 0 ∧
      ∃ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ W, D W = W.ord f) ∧
        (∀ W, D W =
          (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) *
              (Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1 :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
                (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) +
            (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ) *
              (Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1 :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
                (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)) ∧
        (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          0 < W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)) ∧
        (∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          0 < W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q)) := by

  have hαg : heckeAlphaBar (AlgebraicClosure ℚ) N q g ≠ 0 :=
    (map_eq_zero_iff _ (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.injective).not.mpr hg
  have hβg : heckeBetaBar (AlgebraicClosure ℚ) N q g ≠ 0 :=
    (map_eq_zero_iff _ (heckeBetaBar (AlgebraicClosure ℚ) N q).toRingHom.injective).not.mpr hg
  set H : modularFunctionFieldBar (N * q) :=
    heckeAlphaBar (AlgebraicClosure ℚ) N q g * heckeBetaBar (AlgebraicClosure ℚ) N q g with hHdef
  have hH : H ≠ 0 := mul_ne_zero hαg hβg
  have hinv : ProlongationTuple.atkinLehnerBar N q H = H := by
    obtain ⟨e₁, e₂⟩ := atkinLehnerBar_heckeAlphaBar_and_heckeBetaBar hqN g
    rw [hHdef, map_mul, e₁, e₂]
    exact mul_comm _ _

  obtain ⟨c, hc, h₁, h₂, hr₁, hr₂⟩ := exists_smul_commonUnit_of_atkinLehnerBar_eq R H hH hinv
  obtain ⟨h₁', h₂', hr₁', hr₂'⟩ := commonUnit_transfer R R' (c • H) h₁ h₂ hr₁ hr₂
  refine ⟨c • H, h₁, h₂, h₁', h₂', hr₁, hr₂, hr₁', hr₂', ?_⟩

  haveI := isCurveOver_modularFunctionFieldBar (N * q)
  have hcH : c • H ≠ 0 := smul_ne_zero hc hH
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    (F := ↥(modularFunctionFieldBar (N * q))) (c • H) hcH
  refine ⟨D, hD, ?_, ?_, ?_⟩
  · intro W
    rw [hD W, Algebra.smul_def, W.ord_mul ((map_ne_zero _).mpr hc) hH, ConstantReduction.ord_algebraMap W hc,
      zero_add, hHdef, W.ord_mul hαg hβg, Place.ord_restrictAlong _ hα W g, Place.ord_restrictAlong _ hβ W g,
      hdiv, hdiv]
  · intro W
    show 0 < (letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q); W.ramificationIndex _)
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    haveI := isIntegral_along (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα
    exact W.ramificationIndex_pos
  · intro W
    show 0 < (letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N q); W.ramificationIndex _)
    letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N q)
    haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
    exact W.ramificationIndex_pos

private theorem exists_pos_of_degree_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (D : Divisor K F) (hdeg : Divisor.degree D = 0)
    {w : Place K F} (hw : D w < 0) : ∃ w' : Place K F, 0 < D w' := by
  classical
  by_contra hcon
  push Not at hcon
  have hsum : Divisor.degree D = ∑ u ∈ D.support, D u := by
    simp only [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum, AddMonoidHom.mulRight_apply,
      IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one]
  have hwmem : w ∈ D.support := Finsupp.mem_support_iff.mpr hw.ne
  have hsplit : D w + ∑ u ∈ D.support.erase w, D u = ∑ u ∈ D.support, D u :=
    Finset.add_sum_erase D.support (fun u => D u) hwmem
  have hle : ∑ u ∈ D.support.erase w, D u ≤ 0 := Finset.sum_nonpos fun u _ => hcon u
  omega

private theorem eq_of_ord_sub_algebraMap_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (x : F) {c c' : K} (h : 0 < v.ord (x - algebraMap K F c))
    (h' : 0 < v.ord (x - algebraMap K F c')) : c = c' := by
  by_contra hne
  have hx0 : x - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hy0 : x - algebraMap K F c' ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h'; exact lt_irrefl _ h'
  have hxm := v.mem_of_ord_nonneg hx0 (le_of_lt h)
  have hym := v.mem_of_ord_nonneg hy0 (le_of_lt h')
  have hxI := (v.mem_maximalIdeal_iff_ord_pos hx0 hxm).mpr h
  have hyI := (v.mem_maximalIdeal_iff_ord_pos hy0 hym).mpr h'
  have hd0 : algebraMap K F (c - c') ≠ 0 := (map_ne_zero _).mpr (sub_ne_zero.mpr hne)
  have hdm : algebraMap K F (c - c') ∈ v.toValuationSubring := v.algebraMap_mem' _
  have hdI : (⟨algebraMap K F (c - c'), hdm⟩ : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    have hsub := Ideal.sub_mem _ hyI hxI
    have heq : (⟨algebraMap K F (c - c'), hdm⟩ : v.toValuationSubring) =
        ⟨x - algebraMap K F c', hym⟩ - ⟨x - algebraMap K F c, hxm⟩ := by
      apply Subtype.ext
      show algebraMap K F (c - c') = (x - algebraMap K F c') - (x - algebraMap K F c)
      rw [map_sub]; ring
    rw [heq]; exact hsub
  have hpos := (v.mem_maximalIdeal_iff_ord_pos hd0 hdm).mp hdI
  rw [ConstantReduction.ord_algebraMap v (sub_ne_zero.mpr hne)] at hpos
  exact lt_irrefl _ hpos

private noncomputable def valueSet {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F) (v : Place K F) :
    Finset K := by
  classical
  exact if h : ∃ c : K, 0 < v.ord (x - algebraMap K F c) then {h.choose} else ∅

private theorem mem_valueSet {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F) (v : Place K F) {c : K}
    (hc : 0 < v.ord (x - algebraMap K F c)) : c ∈ valueSet x v := by
  classical
  have h : ∃ c : K, 0 < v.ord (x - algebraMap K F c) := ⟨c, hc⟩
  simp only [valueSet, dif_pos h, Finset.mem_singleton]
  exact eq_of_ord_sub_algebraMap_pos v x hc h.choose_spec

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple PlaceSpecialization.reduceFst PlaceSpecialization.reduceSnd modularFunctionFieldBar jq ModularPolynomialData jq_mem modularFunctionField_le_full coeffEmb coeffEmb_mem_laurentBaseChange jqModC modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull cuspInftyBar CharPReduction.modularLocalized modularFunctionFieldC_eq_modularFunctionFieldFullC genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar isCurveOver_modularFunctionFieldBar essFiniteType_modularFunctionFieldBar ord_cuspInftyBar_coeffEmb_jq exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst reduceSnd IsStrictFst IsStrictSnd sp mk d0_j d2 red_surjective_of_level" end ModularCurve.PlaceSpecialization
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in

private theorem ModularCurve.PlaceSpecialization.exists_isStrictSnd_restrictAlong_heckeBetaBar_eq_of_sp_not_fixed
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw₀ : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp w₀)) ≠ P.sp w₀) :
    ∃ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = w₀ ∧ P.IsStrictSnd W ∧
        W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) = 1 := by
  have _ := hqN
  obtain ⟨W₀, hWβ, hWα, he, -⟩ := P.d2 w₀ hw₀
  refine ⟨W₀, hWβ, ⟨?_, ?_⟩, he⟩
  · show P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) =
      frobOnPlacesGeomLevel k N data hKr (P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ))
    rw [hWβ]
    exact hWα
  · show frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
        (P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ))) ≠
      P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
    rw [hWβ]
    exact hw₀

p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization" in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem ModularCurve.PlaceSpecialization.exists_notMem_and_forall_sp_notMem
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    (hqN : ¬ q ∣ N) (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (T : Finset (Place k (modularFunctionFieldC k N)))
    (T₀ : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))) :
    ∃ w₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w₁ ∉ T₀ ∧
      ∀ Q : PlaceSpecialization A q N data hKr k red hα hβ, Q.sp w₁ ∉ T := by
  have _ := hqN
  classical

  set jB : modularFunctionFieldBar N :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))⟩
    with hjB
  set jt : modularFunctionFieldC k N := ⟨jqModC k, jqModC_mem k N⟩ with hjt
  have hd0j : ∀ (Q : PlaceSpecialization A q N data hKr k red hα hβ)
      (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (b : A),
      0 < w.ord (jB - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (b : AlgebraicClosure ℚ)) →
      0 < (Q.sp w).ord (jt - algebraMap k (modularFunctionFieldC k N) (red b)) :=
    fun Q w b hw => Q.d0_j w b hw
  have hpole : (cuspInftyBar N).ord jB = -1 := ord_cuspInftyBar_coeffEmb_jq N

  obtain ⟨c, hc⟩ := (T.biUnion (valueSet jt)).exists_notMem
  obtain ⟨a₀, ha₀⟩ := P.red_surjective_of_level c

  have hred : ∀ n : ℕ, red (a₀ + (q : A) ^ (n + 1)) = c := by
    intro n
    rw [map_add, map_pow, map_natCast, CharP.cast_eq_zero k q, zero_pow (Nat.succ_ne_zero n), add_zero, ha₀]
  have hinj : Function.Injective fun n : ℕ => ((a₀ + (q : A) ^ (n + 1) : A) : AlgebraicClosure ℚ) := by
    intro m n hmn
    have h1 : ((q : AlgebraicClosure ℚ)) ^ (m + 1) = (q : AlgebraicClosure ℚ) ^ (n + 1) := by
      have := congrArg (fun z : AlgebraicClosure ℚ => z - (a₀ : AlgebraicClosure ℚ)) hmn
      simpa using this
    have hq1 : (1 : ℕ) < q := (Fact.out : q.Prime).one_lt
    have h2 : (q : ℕ) ^ (m + 1) = q ^ (n + 1) := by
      exact_mod_cast h1
    exact Nat.succ_injective (Nat.pow_right_injective (Nat.succ_le_of_lt hq1) h2)
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finset
    (T₀.biUnion (valueSet jB))
  set a : A := a₀ + (q : A) ^ (n + 1) with ha

  have hf0 : jB - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    have hj := sub_eq_zero.mp h0
    by_cases haz : (a : AlgebraicClosure ℚ) = 0
    · rw [hj, haz, map_zero, Place.ord_zero] at hpole; omega
    · rw [hj, ConstantReduction.ord_algebraMap _ haz] at hpole; omega
  have hfneg : (cuspInftyBar N).ord
      (jB - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) < 0 := by
    by_contra hnn
    push Not at hnn
    have hfm := (cuspInftyBar N).mem_of_ord_nonneg hf0 hnn
    have hjm : jB ∈ (cuspInftyBar N).toValuationSubring := by
      have hrw : jB = (jB - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) +
          algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) := by ring
      rw [hrw]
      exact add_mem hfm ((cuspInftyBar N).algebraMap_mem' _)
    have := (cuspInftyBar N).ord_nonneg_of_mem hjm
    omega
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    IsCurveOver.hasPrincipalDivisors
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    (F := ↥(modularFunctionFieldBar N))
    (jB - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) hf0
  have hDneg : D (cuspInftyBar N) < 0 := by rw [hD]; exact hfneg
  obtain ⟨w₁, hw₁⟩ := exists_pos_of_degree_eq_zero D hdeg hDneg
  rw [hD] at hw₁

  refine ⟨w₁, fun hmem => hn ?_, fun Q hmem => hc ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨w₁, hmem, mem_valueSet jB w₁ hw₁⟩
  · have hv := hd0j Q w₁ a hw₁
    rw [hred n] at hv
    exact Finset.mem_biUnion.mpr ⟨Q.sp w₁, hmem, mem_valueSet jt (Q.sp w₁) hv⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem count_core
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    (hqN : ¬ q ∣ N)
    (Y Z : PlaceSpecialization A q N data hKr k red hα hβ)
    (RY : PlaceSpecialization.ProlongationTuple Y) (hY : RY.IsModel)
    (RZ : PlaceSpecialization.ProlongationTuple Z) (hZ : RZ.IsModel)
    (w₀ w₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (u : Place k (modularFunctionFieldC k N))
    (hu : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr u) ≠ u) (hYw₀ : Y.sp w₀ = u)
    (hYα₁ : Y.sp w₁ ≠ frobOnPlacesGeomLevel k N data hKr u) (hYβ₁ : Y.sp w₁ ≠ u)
    (hZα₀ : Z.sp w₀ ≠ frobOnPlacesGeomLevel k N data hKr u) (hZα₁ : Z.sp w₁ ≠ frobOnPlacesGeomLevel k N data hKr u)
    (hZβ₀ : Z.sp w₀ ≠ u) (hZβ₁ : Z.sp w₁ ≠ u)
    (f : modularFunctionFieldBar (N * q))
    (hY₁ : f ∈ RY.R₁.integers) (hY₂ : f ∈ RY.R₂.integers)
    (hZ₁ : f ∈ RZ.R₁.integers) (hZ₂ : f ∈ RZ.R₂.integers)
    (rY₁ : RY.R₁.residue ⟨f, hY₁⟩ ≠ 0) (rY₂ : RY.R₂.residue ⟨f, hY₂⟩ ≠ 0)
    (rZ₁ : RZ.R₁.residue ⟨f, hZ₁⟩ ≠ 0) (rZ₂ : RZ.R₂.residue ⟨f, hZ₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) (hD : ∀ W, D W = W.ord f)
    (hDf : ∀ W, D W =
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) *
          (Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1 :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
            (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) +
        (W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) : ℤ) *
          (Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1 :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
            (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ))
    (heβ : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      0 < W.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N q)) : False := by
  classical
  have hw : w₀ ≠ w₁ := fun h => hYβ₁ (by rw [← h, hYw₀])
  have hδ : ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), x ≠ w₀ → x ≠ w₁ →
      (Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1 :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) x = 0 := fun x h0 h1 => by
    rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (Ne.symm h0),
      if_neg (Ne.symm h1), sub_zero]
  have hδ₀ : (Finsupp.single w₀ (1 : ℤ) - Finsupp.single w₁ 1 :
          Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) w₀ = 1 := by
    rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_pos rfl, if_neg (Ne.symm hw), sub_zero]
  have hYα₀ : Y.sp w₀ ≠ frobOnPlacesGeomLevel k N data hKr u := by
    rw [hYw₀]; intro h; apply hu; rw [← h, ← h]
  obtain ⟨-, hLY, -, -⟩ := hY
  obtain ⟨-, hLZ, -, -⟩ := hZ
  have lawY := hLY f hY₁ hY₂ rY₁ rY₂ D hD u hu
  have lawZ := hLZ f hZ₁ hZ₂ rZ₁ rZ₂ D hD u hu
  have hres : u.ord (RY.residue₂ ⟨f, hY₂⟩) = u.ord (RZ.residue₂ ⟨f, hZ₂⟩) := by
    rw [residue₂_indep RY RZ f hY₂ hZ₂]
  obtain ⟨W₀, hW₀β, hW₀s, -⟩ :=
    ModularCurve.PlaceSpecialization.exists_isStrictSnd_restrictAlong_heckeBetaBar_eq_of_sp_not_fixed
      hqN Y w₀ (by rw [hYw₀]; exact hu)

  have key : ∀ (Q : PlaceSpecialization A q N data hKr k red hα hβ)
      (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
      Q.IsStrictSnd W → Q.reduceSnd W = u →
      Q.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = frobOnPlacesGeomLevel k N data hKr u ∧
        Q.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) = u := fun Q W hs hred => by
    have h1 : Q.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) = u := hred
    obtain ⟨h2, -⟩ := hs
    have h3 : Q.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) =
        frobOnPlacesGeomLevel k N data hKr (Q.sp (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)) := h2
    refine ⟨?_, h1⟩
    rw [h3, h1]

  have hsupp : ∀ W, D W ≠ 0 →
      (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = w₀ ∨
        W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα = w₁) ∨
      (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = w₀ ∨
        W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = w₁) := fun W hW => by
    by_contra hcon
    push Not at hcon
    apply hW
    rw [hDf W, hδ _ hcon.1.1 hcon.1.2, hδ _ hcon.2.1 hcon.2.2, mul_zero, mul_zero, add_zero]

  have memf : ∀ (Q : PlaceSpecialization A q N data hKr k red hα hβ) W,
      W ∈ (D.filter Q.IsStrictSnd).support → Q.IsStrictSnd W ∧ D W ≠ 0 := fun Q W hW => by
    by_cases hp : Q.IsStrictSnd W
    · refine ⟨hp, fun h0 => Finsupp.mem_support_iff.mp hW ?_⟩
      rw [Finsupp.filter_apply_pos _ _ hp]; exact h0
    · exact absurd (Finsupp.filter_apply_neg _ _ hp) (Finsupp.mem_support_iff.mp hW)
  refine mapDomain_apply_ne Y.reduceSnd Z.reduceSnd _ _ u (lawY.trans (hres.trans lawZ.symm))
    ?_ ?_ W₀ ?_ ?_
  ·
    intro W hW habs
    obtain ⟨hs, hD0⟩ := memf Z W hW
    obtain ⟨hαu, hβu⟩ := key Z W hs habs
    rcases hsupp W hD0 with (h | h) | (h | h)
    · exact hZα₀ (by rw [← h]; exact hαu)
    · exact hZα₁ (by rw [← h]; exact hαu)
    · exact hZβ₀ (by rw [← h]; exact hβu)
    · exact hZβ₁ (by rw [← h]; exact hβu)
  ·
    intro W hW habs
    obtain ⟨hs, hD0⟩ := memf Y W hW
    obtain ⟨hαu, hβu⟩ := key Y W hs habs
    rw [Finsupp.filter_apply_pos _ _ hs]
    have hα0 : W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ≠ w₀ :=
      fun h => hYα₀ (by rw [← h]; exact hαu)
    have hα1 : W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ≠ w₁ :=
      fun h => hYα₁ (by rw [← h]; exact hαu)
    have hβ1 : W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ ≠ w₁ :=
      fun h => hYβ₁ (by rw [← h]; exact hβu)
    have hβ0 : W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ = w₀ := by
      rcases hsupp W hD0 with (h | h) | (h | h)
      · exact absurd h hα0
      · exact absurd h hα1
      · exact h
      · exact absurd h hβ1
    rw [hDf W, hδ _ hα0 hα1, hβ0, hδ₀, mul_zero, zero_add, mul_one]
    exact Nat.cast_pos.mpr (heβ W)
  ·
    have hred : Y.reduceSnd W₀ = u := by
      show Y.sp (W₀.restrictAlong _ hβ) = u
      rw [hW₀β, hYw₀]
    obtain ⟨hαu, -⟩ := key Y W₀ hW₀s hred
    have hα0 : W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ≠ w₀ :=
      fun h => hYα₀ (by rw [← h]; exact hαu)
    have hα1 : W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα ≠ w₁ :=
      fun h => hYα₁ (by rw [← h]; exact hαu)
    rw [Finsupp.mem_support_iff, Finsupp.filter_apply_pos _ _ hW₀s, hDf W₀, hδ _ hα0 hα1, hW₀β, hδ₀, mul_zero,
      zero_add, mul_one]
    exact (Nat.cast_pos.mpr (heβ W₀)).ne'
  · show Y.sp (W₀.restrictAlong _ hβ) = u
    rw [hW₀β, hYw₀]

set_option synthInstance.maxHeartbeats 1600000 in

private theorem sp_eq_of_not_fixed
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    (hng : ¬ (0 < genusFF k ↥(modularFunctionFieldC k N))) (hqN : ¬ q ∣ N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (R' : PlaceSpecialization.ProlongationTuple P') (hmodel' : R'.IsModel)
    (w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp w₀)) ≠ P.sp w₀) :
    P'.sp w₀ = P.sp w₀ := by
  classical
  by_contra hne
  have hinj := frobOnPlacesGeomLevel_injective k N data hKr
  have hfix1 :
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr
        (frobOnPlacesGeomLevel k N data hKr (P.sp w₀))) ≠ frobOnPlacesGeomLevel k N data hKr (P.sp w₀) :=
    fun h => hfix (hinj h)
  obtain ⟨w₁, -, hw₁⟩ :=
    ModularCurve.PlaceSpecialization.exists_notMem_and_forall_sp_notMem hqN P
      ({P.sp w₀, frobOnPlacesGeomLevel k N data hKr (P.sp w₀),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp w₀))} : Finset _) (∅ : Finset _)
  have hT : ∀ Q : PlaceSpecialization A q N data hKr k red hα hβ,
      Q.sp w₁ ≠ P.sp w₀ ∧ Q.sp w₁ ≠ frobOnPlacesGeomLevel k N data hKr (P.sp w₀) ∧
        Q.sp w₁ ≠ frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp w₀)) := fun Q => by
    refine ⟨fun h => hw₁ Q ?_, fun h => hw₁ Q ?_, fun h => hw₁ Q ?_⟩ <;> rw [h] <;> simp
  obtain ⟨g, hg, hdivg⟩ := g0_exists_ord_eq_single_sub_single hng hqN w₀ w₁
  obtain ⟨f, h₁, h₂, h₁', h₂', hr₁, hr₂, hr₁', hr₂', D, hD, hDf, -, heβ⟩ :=
    commonUnit_standin hqN P P' R R' g hg w₀ w₁ hdivg
  by_cases hA : P'.sp w₀ = frobOnPlacesGeomLevel k N data hKr (P.sp w₀)
  · exact count_core hqN P' P R' hmodel' R hmodel w₀ w₁ (frobOnPlacesGeomLevel k N data hKr (P.sp w₀)) hfix1 hA
      (hT P').2.2 (hT P').2.1 (fun h => hfix h.symm) (hT P).2.2 (fun h => hfix (by rw [← h, ← h])) (hT P).2.1
      f h₁' h₂' h₁ h₂ hr₁' hr₂' hr₁ hr₂ D hD hDf heβ
  · exact count_core hqN P P' R hmodel R' hmodel' w₀ w₁ (P.sp w₀) hfix rfl (hT P).2.1 (hT P).1 hA (hT P').2.1
      hne (hT P').1 f h₁ h₂ h₁' h₂' hr₁ hr₂ hr₁' hr₂' D hD hDf heβ

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    (hng : ¬ (0 < genusFF k ↥(modularFunctionFieldC k N))) (hqN : ¬ q ∣ N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel)
    (R' : PlaceSpecialization.ProlongationTuple P') (hmodel' : R'.IsModel) :
    (∀ V, P.IsStrictFst V ↔ P'.IsStrictFst V) ∧ (∀ V, P.IsStrictSnd V ↔ P'.IsStrictSnd V) := by
  have hinj := frobOnPlacesGeomLevel_injective k N data hKr
  have hsp : ∀ w, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P.sp w)) ≠ P.sp w →
      P'.sp w = P.sp w := fun w hw => sp_eq_of_not_fixed hng hqN P P' R hmodel R' hmodel' w hw
  have hsp' : ∀ w, frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr (P'.sp w)) ≠ P'.sp w →
      P.sp w = P'.sp w := fun w hw => sp_eq_of_not_fixed hng hqN P' P R' hmodel' R hmodel w hw

  have htr : ∀ x y : Place k (modularFunctionFieldC k N), frobOnPlacesGeomLevel k N data hKr x = y →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr x) ≠ x →
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr y) ≠ y := by
    rintro x y rfl hx h
    exact hx (hinj h)
  refine ⟨fun V => ?_, fun V => ?_⟩
  · show (_ = _ ∧ _ ≠ _) ↔ (_ = _ ∧ _ ≠ _)
    simp only [PlaceSpecialization.reduceFst, PlaceSpecialization.reduceSnd]
    constructor
    · rintro ⟨h1, h2⟩
      have ha := hsp _ h2
      have hb := hsp _ (htr _ _ h1 h2)
      rw [ha, hb]; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have ha := hsp' _ h2
      have hb := hsp' _ (htr _ _ h1 h2)
      rw [ha, hb]; exact ⟨h1, h2⟩
  · show (_ = _ ∧ _ ≠ _) ↔ (_ = _ ∧ _ ≠ _)
    simp only [PlaceSpecialization.reduceFst, PlaceSpecialization.reduceSnd]
    constructor
    · rintro ⟨h1, h2⟩
      have hb := hsp _ h2
      have ha := hsp _ (htr _ _ h1.symm h2)
      rw [ha, hb]; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hb := hsp' _ h2
      have ha := hsp' _ (htr _ _ h1.symm h2)
      rw [ha, hb]; exact ⟨h1, h2⟩

#print axioms solution

end S_ModularCurve_PlaceSpecialization_isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_isStrictFst_iff_and_isStrictSnd_iff_of_isModel_of_isModel (solution)
