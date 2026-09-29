-- Prove2me | solution 1 for ModularCurve.exists_fieldOver_lift_isIntegral_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3bbdabf1-30e4-5967-8d6c-0c4b61beb153

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_CharPModel_exists_integral_lift_jChart_and_jInvChart
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap
import Theorems.Thm_ModularCurve_CharPReduction_exists_coeffMap_eq_of_mem_modularLocalized_of_monic
import Theorems.Thm_ModularCurve_NodeLocalized_exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral
import Theorems.Thm_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_fieldOver_lift_isIntegral_of_isIntegral
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix"
p2m_attr_erase "simp" "ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false

namespace J3R1

open ModularCurve

section SMulHelpers

variable {R : Type*} [CommRing R]

private theorem mul_smul_comm_j3 (c : R) (x y : LaurentSeries R) : x * (c • y) = c • (x * y) := by
  rw [← HahnSeries.single_zero_mul_eq_smul, mul_left_comm, HahnSeries.single_zero_mul_eq_smul]

private theorem smul_mul_assoc_j3 (c : R) (x y : LaurentSeries R) : c • x * y = c • (x * y) := by
  rw [← HahnSeries.single_zero_mul_eq_smul, mul_assoc, HahnSeries.single_zero_mul_eq_smul]

private theorem coeffMap_injective_j3 {S : Type*} [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  exact hf (by simpa only [coeffMap_coeff] using congrArg (fun z : LaurentSeries S => z.coeff n) h)

end SMulHelpers

section Descent

variable {k₀ k : Type*} [Field k₀] [Field k] (φ : k₀ →+* k) (N : ℕ) [NeZero N]

private noncomputable def spanImg_j3 : Submodule k (LaurentSeries k) :=
  Submodule.span k (Set.range fun u : ↥(Algebra.adjoin k₀ ({jqModC k₀, jqNModC k₀ N} : Set (LaurentSeries k₀))) =>
    coeffMap φ (u : LaurentSeries k₀))

private theorem spanImg_mul_mem_j3 {w : LaurentSeries k} (hw : w ∈ spanImg_j3 φ N) :
    ∀ w' ∈ spanImg_j3 φ N, w * w' ∈ spanImg_j3 φ N := by
  refine Submodule.span_induction
    (p := fun (w : LaurentSeries k) _ => ∀ w' ∈ spanImg_j3 φ N, w * w' ∈ spanImg_j3 φ N) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨u, rfl⟩ w' hw'
    refine Submodule.span_induction
      (p := fun (w' : LaurentSeries k) _ => coeffMap φ (u : LaurentSeries k₀) * w' ∈ spanImg_j3 φ N)
      ?_ ?_ ?_ ?_ hw'
    · rintro _ ⟨u', rfl⟩
      refine Submodule.subset_span ⟨u * u', ?_⟩
      show coeffMap φ ((u : LaurentSeries k₀) * u') = _
      rw [map_mul]
    · show coeffMap φ (u : LaurentSeries k₀) * 0 ∈ spanImg_j3 φ N
      rw [mul_zero]; exact zero_mem _
    · intro x y _ _ hx hy
      rw [mul_add]; exact add_mem hx hy
    · intro c x _ hx
      rw [mul_smul_comm_j3]; exact Submodule.smul_mem _ _ hx
  · intro w' _
    rw [zero_mul]; exact zero_mem _
  · intro x y _ _ hx hy w' hw'
    rw [add_mul]; exact add_mem (hx w' hw') (hy w' hw')
  · intro c x _ hx w' hw'
    rw [smul_mul_assoc_j3]; exact Submodule.smul_mem _ _ (hx w' hw')

private theorem one_mem_spanImg_j3 : (1 : LaurentSeries k) ∈ spanImg_j3 φ N := by
  refine Submodule.subset_span ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, map_one]

private theorem adjoin_le_spanImg_j3 {z : LaurentSeries k}
    (hz : z ∈ Algebra.adjoin k ({jqModC k, jqNModC k N} : Set (LaurentSeries k))) :
    z ∈ spanImg_j3 φ N := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
  · rintro t (rfl | rfl)
    · refine Submodule.subset_span ⟨⟨jqModC k₀, Algebra.subset_adjoin (Set.mem_insert _ _)⟩, ?_⟩
      exact coeffMap_jqModC φ
    · refine Submodule.subset_span ⟨⟨jqNModC k₀ N, Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)⟩, ?_⟩
      exact coeffMap_jqNModC φ N
  · intro c
    rw [algebraMap_laurentSeries_eq_single, ← mul_one (HahnSeries.single (0 : ℤ) c),
      HahnSeries.single_zero_mul_eq_smul]
    exact Submodule.smul_mem _ _ (one_mem_spanImg_j3 φ N)
  · intro x y _ _ hx hy
    exact add_mem hx hy
  · intro x y _ _ hx hy
    exact spanImg_mul_mem_j3 φ N hx _ hy

private theorem transfer_j3 [Algebra k₀ k] (hφ : algebraMap k₀ k = φ) (lam : Module.Dual k₀ k)
    {ι : Type*} (s : Finset ι) (c : ι → k) (g : ι → LaurentSeries k₀) (m : ℤ) :
    lam ((∑ i ∈ s, c i • coeffMap φ (g i)).coeff m) = (∑ i ∈ s, lam (c i) • g i).coeff m := by
  rw [HahnSeries.coeff_sum, HahnSeries.coeff_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul, smul_eq_mul,
    show c i * φ ((g i).coeff m) = (g i).coeff m • c i by rw [Algebra.smul_def, hφ, mul_comm],
    map_smul, smul_eq_mul, mul_comm]

private theorem mem_modularFunctionFieldC_of_coeffMap_mem_j3 (x : LaurentSeries k₀)
    (hx : coeffMap φ x ∈ modularFunctionFieldC k N) : x ∈ modularFunctionFieldC k₀ N := by
  classical
  obtain ⟨r, hr, s, hs, hrs⟩ := IntermediateField.mem_adjoin_iff_div.mp hx
  by_cases hs0 : s = 0
  · rw [hs0, div_zero, map_eq_zero_iff _ (coeffMap_injective_j3 φ φ.injective)] at hrs
    rw [hrs]
    exact zero_mem _
  obtain ⟨c₁, hc₁⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (adjoin_le_spanImg_j3 φ N hr)
  obtain ⟨c₂, hc₂⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (adjoin_le_spanImg_j3 φ N hs)
  rw [Finsupp.sum] at hc₁ hc₂

  obtain ⟨m, hm⟩ : ∃ m, s.coeff m ≠ 0 := by
    by_contra h
    apply hs0
    ext m
    exact not_not.mp (not_exists.mp h m)
  letI : Algebra k₀ k := φ.toAlgebra
  have hφ : algebraMap k₀ k = φ := RingHom.algebraMap_toAlgebra φ
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual k₀ k, lam (s.coeff m) ≠ 0 :=
    not_forall.mp ((Module.forall_dual_apply_eq_zero_iff k₀ (s.coeff m)).not.mpr hm)

  let U : LaurentSeries k₀ := ∑ u ∈ c₂.support, lam (c₂ u) • (u : LaurentSeries k₀)
  let V : LaurentSeries k₀ := ∑ u ∈ c₁.support, lam (c₁ u) • (u : LaurentSeries k₀)
  have hmemC : ∀ (t : Finset ↥(Algebra.adjoin k₀ ({jqModC k₀, jqNModC k₀ N} : Set (LaurentSeries k₀))))
      (d : ↥(Algebra.adjoin k₀ ({jqModC k₀, jqNModC k₀ N} : Set (LaurentSeries k₀))) → k₀),
      (∑ u ∈ t, d u • (u : LaurentSeries k₀)) ∈ modularFunctionFieldC k₀ N := by
    intro t d
    refine sum_mem fun u _ => ?_
    rw [← HahnSeries.single_zero_mul_eq_smul, ← algebraMap_laurentSeries_eq_single]
    exact mul_mem ((modularFunctionFieldC k₀ N).algebraMap_mem (d u))
      (IntermediateField.algebra_adjoin_le_adjoin _ _ u.2)
  have hU : U ∈ modularFunctionFieldC k₀ N := hmemC c₂.support fun u => lam (c₂ u)
  have hV : V ∈ modularFunctionFieldC k₀ N := hmemC c₁.support fun u => lam (c₁ u)
  have hxs : coeffMap φ x * s = r := by
    rw [hrs, div_mul_cancel₀ _ hs0]
  have hUV : x * U = V := by
    ext n
    have h1 : lam ((coeffMap φ x * s).coeff n) = (x * U).coeff n := by
      rw [← hc₂, Finset.mul_sum]
      have h2 : ∑ u ∈ c₂.support, coeffMap φ x * (c₂ u • coeffMap φ (u : LaurentSeries k₀)) =
          ∑ u ∈ c₂.support, c₂ u • coeffMap φ (x * (u : LaurentSeries k₀)) :=
        Finset.sum_congr rfl fun u _ => by rw [mul_smul_comm_j3, map_mul]
      rw [h2, transfer_j3 φ hφ lam, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun u _ => by rw [mul_smul_comm_j3]
    have h3 : lam (r.coeff n) = V.coeff n := by
      rw [← hc₁, transfer_j3 φ hφ lam]
    rw [← h1, ← h3, hxs]
  have hU0 : U ≠ 0 := by
    intro h0
    apply hlam
    have h := transfer_j3 φ hφ lam c₂.support (fun u => c₂ u) (fun u => (u : LaurentSeries k₀)) m
    rw [hc₂] at h
    rw [h, show (∑ i ∈ c₂.support, lam (c₂ i) • ((i : LaurentSeries k₀))) = U from rfl, h0,
      HahnSeries.coeff_zero]
  rw [(eq_div_iff hU0).mpr hUV]
  exact div_mem hV hU

end Descent

section ModularEquation

private theorem coeffMap_int_injective_j3 :
    Function.Injective (coeffMap (Int.castRingHom ℚ) : LaurentSeries ℤ → LaurentSeries ℚ) := by
  intro x y h
  ext n
  have hn := congrArg (fun s : LaurentSeries ℚ => s.coeff n) h
  simpa only [coeffMap_coeff, eq_intCast, Int.cast_inj] using hn

private theorem ringHom_ext_intPoly_j3 {S : Type*} [CommRing S] {f g : Polynomial ℤ →+* S}
    (hX : f Polynomial.X = g Polynomial.X) : f = g :=
  Polynomial.ringHom_ext (fun z => RingHom.congr_fun (RingHom.ext_int (f.comp Polynomial.C)
    (g.comp Polynomial.C)) z) hX

private theorem modularEquation_j3 (k : Type*) [Field k] (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqModC k)) (jqNModC k N) = 0 := by

  have hZ : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) (jqModC ℤ))
      (jqNModC ℤ N) = 0 := by
    apply coeffMap_int_injective_j3
    rw [Polynomial.hom_eval₂, map_zero, coeffMap_jqNModC]
    have hcomp : (coeffMap (Int.castRingHom ℚ)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) (jqModC ℤ)) = evalAtJ := by
      refine ringHom_ext_intPoly_j3 ?_
      rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, coeffMap_jqModC,
        evalAtJ_X, jqModC_rat]
    have hN : jqNModC ℚ N = jqN N := by
      rw [jqNModC, jqModC_rat]
      rfl
    rw [hcomp, hN]
    exact data.eval_eq_zero

  have h := congrArg (coeffMap (Int.castRingHom k)) hZ
  rw [Polynomial.hom_eval₂, map_zero, coeffMap_jqNModC] at h
  have hcomp : (coeffMap (Int.castRingHom k)).comp
      (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) (jqModC ℤ)) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqModC k) := by
    refine ringHom_ext_intPoly_j3 ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, coeffMap_jqModC,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rwa [hcomp] at h

end ModularEquation

section KIntegrality

variable (k : Type*) [Field k] (N : ℕ) [NeZero N]

private theorem isIntegral_adjoin_jqModC_j3 (gbar : ↥(modularFunctionFieldC k N))
    (hint : IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) gbar) :
    IsIntegral ↥(Algebra.adjoin k ({jqModC k} : Set (LaurentSeries k))) (gbar : LaurentSeries k) := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  let S₂' : Subalgebra k (LaurentSeries k) := Algebra.adjoin k {jqModC k, jqNModC k N}
  let S₁' : Subalgebra k (LaurentSeries k) := Algebra.adjoin k {jqModC k}

  have hval : ∀ s : ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))),
      ((s : ↥(modularFunctionFieldC k N)) : LaurentSeries k) ∈ S₂' := by
    intro s
    refine Algebra.adjoin_induction
      (p := fun (t : ↥(modularFunctionFieldC k N)) _ => (t : LaurentSeries k) ∈ S₂') ?_ ?_ ?_ ?_ s.2
    · rintro t (rfl | rfl)
      · exact Algebra.subset_adjoin (Set.mem_insert _ _)
      · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
    · intro r; exact Subalgebra.algebraMap_mem _ r
    · intro t t' _ _ ht ht'; exact add_mem ht ht'
    · intro t t' _ _ ht ht'; exact mul_mem ht ht'
  let χ : ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) →+* ↥S₂' :=
    ((modularFunctionFieldC k N).val.toRingHom.comp
      (Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))).val.toRingHom).codRestrict
      S₂' hval
  have hi₂ : IsIntegral ↥S₂' (gbar : LaurentSeries k) :=
    hint.map_of_comp_eq χ (modularFunctionFieldC k N).val.toRingHom (RingHom.ext fun _ => rfl)

  have hle : S₁' ≤ S₂' := Algebra.adjoin_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  letI : Algebra ↥S₁' ↥S₂' := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower ↥S₁' ↥S₂' (LaurentSeries k) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hJmem : jqModC k ∈ S₁' := Algebra.subset_adjoin rfl
  have hJNint : IsIntegral ↥S₁' (jqNModC k N) := by
    refine ⟨data.Φ.map (Polynomial.aeval (R := ℤ) (⟨jqModC k, hJmem⟩ : ↥S₁')).toRingHom,
      data.monic.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥S₁' (LaurentSeries k)).comp
        (Polynomial.aeval (R := ℤ) (⟨jqModC k, hJmem⟩ : ↥S₁')).toRingHom =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries k)) (jqModC k) := by
      refine ringHom_ext_intPoly_j3 ?_
      rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.aeval_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
    rw [hcomp]
    exact modularEquation_j3 k N data
  haveI : Algebra.IsIntegral ↥S₁' ↥S₂' := by
    refine ⟨fun s => ?_⟩
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥S₁' ↥S₂' (LaurentSeries k))
      (fun a b hab => Subtype.ext hab)]
    show IsIntegral ↥S₁' (s : LaurentSeries k)
    refine Algebra.adjoin_induction
      (p := fun (t : LaurentSeries k) _ => IsIntegral ↥S₁' t) ?_ ?_ ?_ ?_ s.2
    · rintro t (rfl | rfl)
      · exact isIntegral_algebraMap (x := (⟨jqModC k, hJmem⟩ : ↥S₁'))
      · exact hJNint
    · intro r
      exact isIntegral_algebraMap (x := algebraMap k ↥S₁' r)
    · intro t t' _ _ ht ht'
      exact ht.add ht'
    · intro t t' _ _ ht ht'
      exact ht.mul ht'
  exact isIntegral_trans _ hi₂

end KIntegrality

section PolyPoly

variable {κ : Type*} [Field κ]

private theorem exists_monic_polyPoly_j3 {y : LaurentSeries κ}
    (h : IsIntegral ↥(Algebra.adjoin κ ({jqModC κ} : Set (LaurentSeries κ))) y) :
    ∃ P : Polynomial (Polynomial κ), P.Monic ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap κ (LaurentSeries κ)) (jqModC κ)) y P = 0 := by
  obtain ⟨P₀, hm, he⟩ := h
  let θ : Polynomial κ →+* LaurentSeries κ := (Polynomial.aeval (jqModC κ)).toRingHom
  have hlifts : P₀.map (algebraMap _ (LaurentSeries κ)) ∈ Polynomial.lifts θ := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ?_
    rw [Polynomial.coeff_map]
    have hmem : algebraMap (↥(Algebra.adjoin κ ({jqModC κ} : Set (LaurentSeries κ)))) (LaurentSeries κ)
        (P₀.coeff n) ∈ (Polynomial.aeval (R := κ) (jqModC κ)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval κ (jqModC κ)]
      exact (P₀.coeff n).2
    exact (AlgHom.mem_range _).mp hmem
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hm.map _)
  refine ⟨P, hPm, ?_⟩
  have hθ : Polynomial.eval₂RingHom (algebraMap κ (LaurentSeries κ)) (jqModC κ) = θ := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      show _ = Polynomial.aeval (jqModC κ) (Polynomial.C c)
      rw [Polynomial.aeval_C]
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      show _ = Polynomial.aeval (jqModC κ) Polynomial.X
      rw [Polynomial.aeval_X]
  rw [hθ, Polynomial.eval₂_eq_eval_map, hPmap, Polynomial.eval_map]
  exact he

end PolyPoly

section Reduction

variable {L : Type*} [CommRing L] (A : Subring L) {κ : Type*} [Field κ] (red : A →+* κ)

private theorem modularRedLocHom_eq_coeffRed_j3 (M : ℕ) [NeZero M] {g : LaurentSeries L}
    (hg : g ∈ CharPReduction.modularLocalized M A red)
    (hgi : g ∈ CharPReduction.integralCoeffs A) :
    CharPReduction.modularRedLocHom M A red ⟨g, hg⟩ = CharPReduction.coeffRed A red ⟨g, hgi⟩ := by
  obtain ⟨r, s, hs, hgs⟩ := (CharPReduction.mem_localizedAtKer A red
    (CharPReduction.modularRing M A) (CharPReduction.modularRing_le_integralCoeffs M A)).mp hg
  have h1 := CharPReduction.redLoc_spec (A := A) (red := red) (R := CharPReduction.modularRing M A)
    (hR := CharPReduction.modularRing_le_integralCoeffs M A) ⟨g, hg⟩ hgs
  have hsne := (CharPReduction.notMem_redKer_iff A red (CharPReduction.modularRing M A)
    (CharPReduction.modularRing_le_integralCoeffs M A)).mp hs
  have h2 : CharPReduction.coeffRed A red ⟨g, hgi⟩ *
      CharPReduction.redRes A red (CharPReduction.modularRing M A)
        (CharPReduction.modularRing_le_integralCoeffs M A) s =
      CharPReduction.redRes A red (CharPReduction.modularRing M A)
        (CharPReduction.modularRing_le_integralCoeffs M A) r := by
    rw [CharPReduction.redRes_apply, CharPReduction.redRes_apply, ← map_mul]
    congr 1
    exact Subtype.ext hgs
  exact mul_right_cancel₀ hsne (h1.trans h2.symm)

end Reduction

section Bar

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ)) {κ : Type*} [Field κ]
  (red : A →+* κ)

private theorem mem_bar_of_mem_modularRing_j3 {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ CharPReduction.modularRing N A.toSubring) : x ∈ modularFunctionFieldBar N := by
  have hle : CharPReduction.modularRing N A.toSubring ≤ (modularFunctionFieldBar N).toSubring := by
    rw [CharPReduction.modularRing, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl | rfl)
    · exact (modularFunctionFieldBar N).algebraMap_mem (a : AlgebraicClosure ℚ)
    · have h : jqModC (AlgebraicClosure ℚ) = coeffEmb (AlgebraicClosure ℚ) jq := by
        show _ = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) jq
        rw [← jqModC_rat]
        exact (coeffMap_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))).symm
      rw [h]
      exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full N (jq_mem N))
    · have h : jqNModC (AlgebraicClosure ℚ) N = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) := by
        show _ = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ N jq)
        rw [← coeffMap_jqNModC (algebraMap ℚ (AlgebraicClosure ℚ)) N, jqNModC, jqModC_rat]
      rw [h]
      exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N dvd_rfl)
  exact hle hx

private theorem mem_bar_of_mem_modularLocalized_j3 {f : LaurentSeries (AlgebraicClosure ℚ)}
    (hf : f ∈ CharPReduction.modularLocalized N A.toSubring red) : f ∈ modularFunctionFieldBar N := by
  obtain ⟨r, s, hs, hfs⟩ := (CharPReduction.mem_localizedAtKer A.toSubring red
    (CharPReduction.modularRing N A.toSubring) (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp hf
  have hsne := (CharPReduction.notMem_redKer_iff A.toSubring red (CharPReduction.modularRing N A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp hs
  have hs0 : ((s : LaurentSeries (AlgebraicClosure ℚ))) ≠ 0 := by
    intro h0
    apply hsne
    have : s = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hfe : f = (r : LaurentSeries (AlgebraicClosure ℚ)) / s := by
    rw [eq_div_iff hs0]
    exact hfs
  rw [hfe]
  exact div_mem (mem_bar_of_mem_modularRing_j3 N A r.2) (mem_bar_of_mem_modularRing_j3 N A s.2)

private theorem isIntegral_bar_j3 {f : LaurentSeries (AlgebraicClosure ℚ)} (hf : f ∈ modularFunctionFieldBar N)
    (hint : ∃ P : Polynomial (Polynomial A), P.Monic ∧
      Polynomial.eval₂ (Polynomial.eval₂RingHom
        ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
        (jqModC (AlgebraicClosure ℚ))) f P = 0) :
    IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) (⟨f, hf⟩ : ↥(modularFunctionFieldBar N)) := by
  obtain ⟨P, hPm, hPe⟩ := hint

  let T : Subalgebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))
  let jT : ↥T := ⟨⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
    (modularFunctionField_le_full N (jq_mem N))⟩, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let θ : Polynomial A →+* ↥T :=
    Polynomial.eval₂RingHom ((algebraMap (AlgebraicClosure ℚ) ↥T).comp A.subtype) jT
  refine ⟨P.map θ, hPm.map θ, ?_⟩
  apply Subtype.val_injective
  show ((Polynomial.eval₂ (algebraMap ↥T ↥(modularFunctionFieldBar N)) ⟨f, hf⟩ (P.map θ) :
      ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
    ((0 : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ))
  rw [ZeroMemClass.coe_zero, ← hPe, show ((Polynomial.eval₂ (algebraMap ↥T ↥(modularFunctionFieldBar N))
      ⟨f, hf⟩ (P.map θ) : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (modularFunctionFieldBar N).val.toRingHom (Polynomial.eval₂ (algebraMap ↥T ↥(modularFunctionFieldBar N))
      ⟨f, hf⟩ (P.map θ)) from rfl, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  have hθC : ∀ a : A, θ (Polynomial.C a) = ((algebraMap (AlgebraicClosure ℚ) ↥T).comp A.subtype) a :=
    fun a => Polynomial.eval₂_C _ _
  have hθX : θ Polynomial.X = jT := Polynomial.eval₂_X _ _
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · show (modularFunctionFieldBar N).val.toRingHom (algebraMap ↥T ↥(modularFunctionFieldBar N) (θ (Polynomial.C a))) =
      (Polynomial.eval₂RingHom ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
        (jqModC (AlgebraicClosure ℚ))) (Polynomial.C a)
    rw [hθC, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    rfl
  · show (modularFunctionFieldBar N).val.toRingHom (algebraMap ↥T ↥(modularFunctionFieldBar N) (θ Polynomial.X)) =
      (Polynomial.eval₂RingHom ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
        (jqModC (AlgebraicClosure ℚ))) Polynomial.X
    rw [hθX, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) jq = jqModC (AlgebraicClosure ℚ)
    rw [← jqModC_rat]
    exact coeffMap_jqModC _

end Bar

end J3R1

open AlgebraicCurve ModularCurve J3R1 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] (red : A →+* k) (hqN : ¬ q ∣ N)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (h₀ : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (gbar : ↥(modularFunctionFieldC k N))
    (hh₀ : coeffMap (NodeLocalized.redRestrict red K) h₀ = (gbar : LaurentSeries k))
    (hint : IsIntegral ↥(Algebra.adjoin k ({jGeomGen k N, jNGeomGen k N} : Set ↥(modularFunctionFieldC k N))) gbar) :
    ∃ (y : LaurentSeries ↥(NodeLocalized.coeffSubring A K)) (g : ↥(modularFunctionFieldBar N)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap (NodeLocalized.coeffSubring A K).subtype y ∧
      coeffMap (NodeLocalized.redRestrict red K) y = (gbar : LaurentSeries k) ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver N K ∧
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ)
        ({⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩,
          ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩} :
          Set ↥(modularFunctionFieldBar N))) g := by

  have hker := ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP A q red
  haveI : IsLocalHom red := ⟨fun a ha => by
    by_contra hna
    exact ha.ne_zero ((hker a).mpr ((IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hna)))⟩
  let φ : IsLocalRing.ResidueField A →+* k := IsLocalRing.ResidueField.lift red
  have hφ : φ.comp (IsLocalRing.residue A) = red := IsLocalRing.ResidueField.lift_comp_residue red
  haveI : CharP (IsLocalRing.ResidueField A) q := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr ?_
    have hq : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
      (hker q).mp (by rw [map_natCast, CharP.cast_eq_zero])
    rw [← map_natCast (IsLocalRing.residue A) q]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hq

  let y' : LaurentSeries (IsLocalRing.ResidueField A) :=
    coeffMap ((IsLocalRing.residue A).comp (Subring.inclusion inf_le_left)) h₀
  have hcomp : φ.comp ((IsLocalRing.residue A).comp (Subring.inclusion inf_le_left)) =
      NodeLocalized.redRestrict red K :=
    RingHom.ext fun x => IsLocalRing.ResidueField.lift_residue_apply red _
  have hφy' : coeffMap φ y' = (gbar : LaurentSeries k) := by
    rw [← hh₀]
    show coeffMap φ (coeffMap _ h₀) = _
    rw [coeffMap_coeffMap]
    exact congrArg (fun ψ => coeffMap ψ h₀) hcomp
  have hy'C : y' ∈ modularFunctionFieldC (IsLocalRing.ResidueField A) N :=
    mem_modularFunctionFieldC_of_coeffMap_mem_j3 φ N y' (by rw [hφy']; exact gbar.2)
  have hy'int : IsIntegral ↥(Algebra.adjoin (IsLocalRing.ResidueField A)
      ({jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A)))) y' := by
    refine ModularCurve.isIntegral_adjoin_of_isIntegral_adjoin_coeffMap φ (jqModC _) y' ?_
    rw [coeffMap_jqModC, hφy']
    exact isIntegral_adjoin_jqModC_j3 k N gbar hint
  obtain ⟨P', hP'm, hP'e⟩ := exists_monic_polyPoly_j3 hy'int

  obtain ⟨f, ⟨P, hPm, hPe⟩, hfred⟩ :=
    (CharPModel.exists_integral_lift_jChart_and_jInvChart N A q hqN (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A) IsLocalRing.residue_surjective).1 y' hy'C ⟨P', hP'm, hP'e⟩

  obtain ⟨yA, hyA⟩ := CharPReduction.exists_coeffMap_eq_of_mem_modularLocalized_of_monic (q := q) A
    (IsLocalRing.residue A) (f : LaurentSeries (AlgebraicClosure ℚ)) f.2 ⟨P, hPm, hPe⟩
  have hyABar : coeffMap A.subtype yA ∈ modularFunctionFieldBar N := by
    rw [hyA]
    exact mem_bar_of_mem_modularLocalized_j3 N A (IsLocalRing.residue A) f.2
  have hfI : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring := by
    rw [← hyA]
    intro n
    rw [coeffMap_coeff]
    exact (yA.coeff n).2

  have hredf : coeffMap (IsLocalRing.residue A) yA = y' := by
    rw [← hfred, modularRedLocHom_eq_coeffRed_j3 A.toSubring (IsLocalRing.residue A) N f.2 hfI]
    ext n
    rw [coeffMap_coeff, CharPReduction.coeffRed_coeff]
    congr 1
    apply Subtype.ext
    show ((yA.coeff n : A) : AlgebraicClosure ℚ) = (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n
    rw [← hyA, coeffMap_coeff]
    rfl
  have hredA : coeffMap (NodeLocalized.redRestrict red K) h₀ = coeffMap red yA := by
    rw [hh₀, ← hφ, ← coeffMap_coeffMap, hredf, hφy']
  have hintA := isIntegral_bar_j3 N A hyABar ⟨P, hPm, by rw [hyA]; exact hPe⟩

  obtain ⟨y, g, hgF, hyg, hredy, hgint⟩ :=
    NodeLocalized.exists_mem_fieldOver_coeffMap_eq_of_coeffMap_redRestrict_eq_of_isIntegral (q := q)
      red K h₀ yA hyABar hredA hintA
  exact ⟨y, g, hyg.symm, hredy.symm.trans hh₀, hgF, hgint⟩

end S_ModularCurve_exists_fieldOver_lift_isIntegral_of_isIntegral
end P2MW
export P2MW.S_ModularCurve_exists_fieldOver_lift_isIntegral_of_isIntegral (solution)
