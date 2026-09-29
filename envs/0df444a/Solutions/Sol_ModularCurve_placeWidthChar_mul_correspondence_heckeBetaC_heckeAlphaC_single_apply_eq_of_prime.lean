-- Prove2me | solution 1 for ModularCurve.placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5eacb153-edf7-5ca2-81f8-d9bd6ff904d5

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_single
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_placeWidthChar_restrictAlong_mul_ramificationIndexAlong_heckeAlphaC_heckeBetaC_cross_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm"
set_option autoImplicit false
open AlgebraicCurve ModularCurve

namespace MatrixCrossAux

namespace PlaceRationality

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem isRational_restrict_of_isRational [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] (w : Place K F') (hw : w.IsRational) :
    (w.restrict F).IsRational := by
  intro y
  obtain ⟨k, hk⟩ := hw (algebraMap (w.restrict F).ResidueField w.ResidueField y)
  refine ⟨k, (algebraMap (w.restrict F).ResidueField w.ResidueField).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply K (w.restrict F).ResidueField w.ResidueField k]
  exact hk

theorem isRational_of_isRational_restrict [IsAlgClosed K] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] (w : Place K F') (hv : (w.restrict F).IsRational) :
    w.IsRational := by
  haveI : Module.Finite K (w.restrict F).ResidueField :=
    Module.Finite.of_surjective (Algebra.linearMap K (w.restrict F).ResidueField) hv
  have hpos : 0 < Module.finrank (w.restrict F).ResidueField w.ResidueField :=
    Place.inertiaDeg_pos_of_finiteDimensional (F := F) w
  haveI : Module.Finite (w.restrict F).ResidueField w.ResidueField :=
    Module.finite_of_finrank_pos hpos
  haveI : Module.Finite K w.ResidueField :=
    Module.Finite.trans (w.restrict F).ResidueField w.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem isRational_restrictAlong_of_isRational (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (hw : w.IsRational) : (w.restrictAlong φ hφ).IsRational := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact isRational_restrict_of_isRational w hw

theorem isRational_of_isRational_restrictAlong [IsAlgClosed K] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (w : Place K F')
    (hv : (w.restrictAlong φ hφ).IsRational) : w.IsRational := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI : Module.Finite F F' := hfin
  exact isRational_of_isRational_restrict w hv

theorem isRational_of_mem_fiberAlong [IsAlgClosed K] [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (v : Place K F) (hv : v.IsRational)
    (w : Place K F') (hw : w ∈ Place.fiberAlong φ hφ v) : w.IsRational := by
  refine isRational_of_isRational_restrictAlong φ hφ hfin w ?_
  have h : w.restrictAlong φ hφ = v := Place.mem_fiberAlong.mp hw
  rw [h]
  exact hv

theorem inertiaDegAlong_eq_one_of_isRational (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (hw : w.IsRational) (hv : (w.restrictAlong φ hφ).IsRational) :
    w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.inertiaDeg_eq_one_of_isRational w hw hv

theorem inertiaDegAlong_eq_one_of_mem_fiberAlong [IsAlgClosed K] [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (v : Place K F)
    (hv : v.IsRational) (w : Place K F') (hw : w ∈ Place.fiberAlong φ hφ v) :
    w.inertiaDegAlong φ hφ = 1 := by
  have h : w.restrictAlong φ hφ = v := Place.mem_fiberAlong.mp hw
  exact inertiaDegAlong_eq_one_of_isRational φ hφ w
    (isRational_of_mem_fiberAlong φ hφ hfin v hv w hw) (h ▸ hv)

end PlaceRationality

theorem isRational_level (k : Type*) [Field k] [IsAlgClosed k] (M : ℕ) [NeZero M] {p : ℕ} [Fact p.Prime] [CharP k p]
    (v : Place k (modularFunctionFieldC k M)) : v.IsRational := by
  haveI : IsCurveOver k (modularFunctionFieldC k M) :=
    isCurveOver_modularFunctionFieldC_of_perfectField k M
  haveI : Module.Finite k v.ResidueField := IsCurveOver.finite_residueField v
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := v.ResidueField)).2

theorem isRational_roof (k : Type*) [Field k] [IsAlgClosed k] (M s : ℕ) [NeZero M] [NeZero s] {p : ℕ} [Fact p.Prime]
    [CharP k p] (hα : HeckeAlphaCIntegral k M s) (W : Place k (charLDegeneracyRoof k M s)) : W.IsRational :=
  PlaceRationality.isRational_of_isRational_restrictAlong (heckeAlphaC k M s) hα
    (finiteAlong_heckeAlphaC k M s) W (isRational_level k M _)

end MatrixCrossAux

open MatrixCrossAux in
set_option maxHeartbeats 3200000 in
theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    [HasPrincipalDivisors k (charLDegeneracyRoof k M s)]
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    (w₀ w' : Place k (modularFunctionFieldC k M)) :
    (placeWidthChar q' M w' : ℤ) *
        Divisor.correspondence (heckeBetaC k M s) (heckeAlphaC k M s) hβ hα (Finsupp.single w₀ 1) w' =
      (placeWidthChar q' M w₀ : ℤ) *
        Divisor.correspondence (heckeAlphaC k M s) (heckeBetaC k M s) hα hβ (Finsupp.single w' 1) w₀ := by
  classical
  have hratW : ∀ W : Place k (charLDegeneracyRoof k M s), W.IsRational := isRational_roof k M s hα
  have hfα : ∀ W : Place k (charLDegeneracyRoof k M s), W.inertiaDegAlong (heckeAlphaC k M s) hα = 1 := fun W =>
    PlaceRationality.inertiaDegAlong_eq_one_of_isRational _ hα W (hratW W) (isRational_level k M _)
  have hfβ : ∀ W : Place k (charLDegeneracyRoof k M s), W.inertiaDegAlong (heckeBetaC k M s) hβ = 1 := fun W =>
    PlaceRationality.inertiaDegAlong_eq_one_of_isRational _ hβ W (hratW W) (isRational_level k M _)

  set S : Finset (Place k (charLDegeneracyRoof k M s)) :=
    (Place.fiberAlong (heckeBetaC k M s) hβ w₀).filter
      (fun Y => Y.restrictAlong (heckeAlphaC k M s) hα = w') with hS
  have hS' : (Place.fiberAlong (heckeAlphaC k M s) hα w').filter
      (fun Y => Y.restrictAlong (heckeBetaC k M s) hβ = w₀) = S := by
    ext Y
    simp only [hS, Finset.mem_filter, Place.mem_fiberAlong]
    tauto

  have hL : Divisor.correspondence (heckeBetaC k M s) (heckeAlphaC k M s) hβ hα (Finsupp.single w₀ 1) w' =
      ∑ Y ∈ S, (Y.ramificationIndexAlong (heckeBetaC k M s) : ℤ) := by
    rw [Divisor.correspondence_single, Finsupp.finsetSum_apply, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Finsupp.single_apply, hfα, Nat.cast_one, mul_one, one_mul]
  have hR : Divisor.correspondence (heckeAlphaC k M s) (heckeBetaC k M s) hα hβ (Finsupp.single w' 1) w₀ =
      ∑ Y ∈ S, (Y.ramificationIndexAlong (heckeAlphaC k M s) : ℤ) := by
    rw [Divisor.correspondence_single, Finsupp.finsetSum_apply, ← hS', Finset.sum_filter]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Finsupp.single_apply, hfβ, Nat.cast_one, mul_one, one_mul]
  rw [hL, hR, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y hY => ?_
  rw [hS, Finset.mem_filter, Place.mem_fiberAlong] at hY
  obtain ⟨hYβ, hYα⟩ := hY
  have hx := ModularCurve.placeWidthChar_restrictAlong_mul_ramificationIndexAlong_heckeAlphaC_heckeBetaC_cross_of_prime
    M s q' hs hsq' hq'M hsM hα hβ Y
  rw [hYβ, hYα] at hx

  exact hx.symm

end S_ModularCurve_placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime
end P2MW
export P2MW.S_ModularCurve_placeWidthChar_mul_correspondence_heckeBetaC_heckeAlphaC_single_apply_eq_of_prime (solution)
