-- Prove2me | solution 1 for ModularCurve.placeWidthChar_restrictAlong_mul_ramificationIndexAlong_heckeAlphaC_heckeBetaC_cross_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/658cf4f2-5f72-5c13-a8a0-f3482d4f2eaa

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_ModularCurve_degeneracyPair_finrankAlong_and_place_transports
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
import Theorems.Thm_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_placeWidthChar_restrictAlong_mul_ramificationIndexAlong_heckeAlphaC_heckeBetaC_cross_of_prime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm"
set_option autoImplicit false
open AlgebraicCurve ModularCurve

private theorem placeRamificationJ_pos_of_isAffineGeomPlace
    {k : Type*} [Field k] [IsAlgClosed k] (N : ℕ) [NeZero N]
    (p : Place k ↥(modularFunctionFieldC k N)) (hp : IsAffineGeomPlace k N p) :
    0 < placeRamificationJ N p := by
  have hrat : p.IsRational :=
    (Place.isRational_iff_deg_eq_one p).mpr (place_deg_eq_one_of_isAlgClosed k N p)
  have h := ord_sub_evalAt_pos_of_isRational hrat hp.1 (jGeomGen_sub_algebraMap_ne_zero k N _)
  unfold placeRamificationJ
  omega

private theorem placeRamificationJ_eq_zero_of_not_isAffineGeomPlace
    {k : Type*} [Field k] (N : ℕ) [NeZero N]
    (p : Place k ↥(modularFunctionFieldC k N)) (hp : ¬ IsAffineGeomPlace k N p) :
    placeRamificationJ N p = 0 := by
  have hpole : p.ord (jGeomGen k N) < 0 :=
    (isAffineGeomPlace_or_ord_jGeomGen_lt_zero k N p).resolve_left hp

  have hneg : p.ord (jGeomGen k N - algebraMap k (modularFunctionFieldC k N) (p.evalAt (jGeomGen k N))) < 0 := by
    by_contra hcon
    push Not at hcon
    have hmem := p.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N _) hcon
    have hj : jGeomGen k N ∈ p.toValuationSubring := by
      have := add_mem hmem (p.algebraMap_mem' (p.evalAt (jGeomGen k N)))
      simpa using this
    exact absurd (p.ord_nonneg_of_mem hj) (not_le.mpr hpole)
  unfold placeRamificationJ
  omega

private theorem branch_five_le
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    (W : Place k ↥(charLDegeneracyRoof k M s))
    (hq5 : 5 ≤ q') :
    (placeWidthChar q' M (W.restrictAlong (heckeBetaC k M s) hβ) : ℤ)
        * (W.ramificationIndexAlong (heckeAlphaC k M s) : ℤ)
      = (placeWidthChar q' M (W.restrictAlong (heckeAlphaC k M s) hα) : ℤ)
        * (W.ramificationIndexAlong (heckeBetaC k M s) : ℤ) := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  have hq'prime : q'.Prime := by
    rcases CharP.char_is_prime_or_zero k q' with h | h
    · exact h
    · omega
  haveI : Fact q'.Prime := ⟨hq'prime⟩
  have hq'Ms : ¬ q' ∣ M * s := by
    intro h
    rcases (Nat.Prime.dvd_mul hq'prime).mp h with h | h
    · exact hq'M h
    · exact hsq' ((Nat.prime_dvd_prime_iff_eq hq'prime hs).mp h).symm

  have hroof : charLDegeneracyRoof k M s = modularFunctionFieldC k (M * s) :=
    (charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' M s hq'Ms).trans
      (modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (M * s) hq'Ms).symm

  unfold HeckeAlphaCIntegral at hα
  unfold HeckeBetaCIntegral at hβ
  have hA : ∀ x : ↥(modularFunctionFieldC k M),
      ((heckeAlphaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) = x := by
    intro x
    simp
  have hB : ∀ x : ↥(modularFunctionFieldC k M),
      ((heckeBetaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) = qExpand k s x := by
    intro x
    simp
  generalize heckeAlphaC k M s = α at hα hA ⊢
  generalize heckeBetaC k M s = β at hβ hB ⊢

  generalize charLDegeneracyRoof k M s = R at hroof W α β hα hβ hA hB ⊢
  subst hroof
  obtain ⟨φ, hφ0, hφ1⟩ : ∃ φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))),
      φ 0 = α ∧ φ 1 = β := ⟨![α, β], rfl, rfl⟩
  subst hφ0
  subst hφ1
  have hφ : ∀ i, (φ i).toRingHom.IsIntegral := by
    intro i
    fin_cases i
    · exact hα
    · exact hβ
  rw [placeWidthChar_of_five_le hq5, placeWidthChar_of_five_le hq5]
  by_cases haff : IsAffineGeomPlace k (M * s) W
  ·
    have hguard : placeRamificationJ (M * s) W ∣ jWidth (W.evalAt (jGeomGen k (M * s))) :=
      placeRamificationJ_dvd_jWidth_of_ord_pos hq5 hq'Ms
        (placeRamificationJ_pos_of_isAffineGeomPlace (M * s) W haff)
    have h0 := ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong M s q' hs hsq' hq'M
      φ hφ hA hB 0 W hguard
    have h1 := ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong M s q' hs hsq' hq'M
      φ hφ hA hB 1 W hguard
    rw [← h0, ← h1]
    push_cast
    ring
  ·
    have htr := (degeneracyPair_finrankAlong_and_place_transports M s q' hs hsq' hq'M hsM
      φ hφ hA hB).2.2.1
    have hzero : ∀ i : Fin 2,
        placeWidthChar q' M (W.restrictAlong (φ i) (hφ i)) = 0 := by
      intro i
      apply placeWidthChar_of_placeRamificationJ_eq_zero
      apply placeRamificationJ_eq_zero_of_not_isAffineGeomPlace
      intro h
      exact haff ((htr i W).mp h)
    have hz0 := hzero 0
    have hz1 := hzero 1
    rw [placeWidthChar_of_five_le hq5] at hz0 hz1
    rw [hz0, hz1]
    simp

private theorem isRational_of_isAlgClosed
    {k : Type*} [Field k] [IsAlgClosed k] {N : ℕ} [NeZero N] (p : Place k ↥(modularFunctionFieldC k N)) :
    p.IsRational :=
  (Place.isRational_iff_deg_eq_one p).mpr (place_deg_eq_one_of_isAlgClosed k N p)

private theorem wild_widths_and_indices_of_not_mem_ssPlaces
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M) (hq5 : q' < 5)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (hjw : ∀ j : k, j ≠ 0 → jWidthChar q' j = 1) (h1728 : (1728 : k) = 0) :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (_ : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (_ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
      (p : Place k ↥(modularFunctionFieldC k (M * s))),
      IsAffineGeomPlace k (M * s) p → p ∉ ssPlaces q' (M * s) k →
      (∀ i : Fin 2, placeWidthChar q' M (p.restrictAlong (φ i) (hφ i)) = 1) ∧
      (∀ i : Fin 2, p.ramificationIndexAlong (φ i) = 1) := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  intro φ hφ hφα hφβ p haff hss
  have hq : q'.Prime := Fact.out
  have hq'Ms : ¬ q' ∣ M * s := fun h =>
    ((Nat.Prime.dvd_mul hq).mp h).elim hq'M fun h' => hsq' ((Nat.prime_dvd_prime_iff_eq hq hs).mp h').symm

  have hrest_aff : ∀ i : Fin 2, IsAffineGeomPlace k M (p.restrictAlong (φ i) (hφ i)) := fun i =>
    ((degeneracyPair_finrankAlong_and_place_transports M s q' hs hsq' hq'M hsM φ hφ hφα hφβ).2.2.1 i p).mpr haff
  have hrest_nss : ∀ i : Fin 2, p.restrictAlong (φ i) (hφ i) ∉ ssPlaces q' M k := fun i h =>
    hss ((degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s q' hs hsq' hq'M hsM
      φ hφ hφα hφβ).2.2.2.2 i _ h p rfl)

  have hjne : ∀ {L : ℕ} [NeZero L] (w : Place k ↥(modularFunctionFieldC k L)),
      IsAffineGeomPlace k L w → w ∉ ssPlaces q' L k → w.evalAt (jGeomGen k L) ≠ 0 := by
    intro L _ w hw hwss hj
    apply hwss
    show IsSupersingularPlace q' L k w
    refine ⟨isRational_of_isAlgClosed w, hw, ?_⟩
    rw [hj]
    exact zero_mem_ssJSet_of_lt_five hq5

  have hindex : ∀ {L : ℕ} [NeZero L] (hL : ¬ q' ∣ L) (w : Place k ↥(modularFunctionFieldC k L)),
      IsAffineGeomPlace k L w → w ∉ ssPlaces q' L k → placeRamificationJ L w = 1 := by
    intro L _ hL w hw hwss
    have hne := hjne w hw hwss
    have h := ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq q' k L hL w _ rfl hne (by rw [h1728]; exact hne)
    unfold placeRamificationJ
    rw [h]
    rfl
  have hp1 := hindex hq'Ms p haff hss
  have hr1 : ∀ i : Fin 2, placeRamificationJ M (p.restrictAlong (φ i) (hφ i)) = 1 := fun i =>
    hindex hq'M _ (hrest_aff i) (hrest_nss i)

  have hjw' : ∀ {L : ℕ} [NeZero L] (w : Place k ↥(modularFunctionFieldC k L)),
      w.evalAt (jGeomGen k L) ≠ 0 → jWidth (w.evalAt (jGeomGen k L)) = 1 := by
    intro L _ w hw
    apply jWidth_of_ne hw
    rw [h1728]
    exact hw
  refine ⟨fun i => ?_, fun i => ?_⟩
  · rw [placeWidthChar_eq_div, hjw _ (hjne _ (hrest_aff i) (hrest_nss i)), hr1 i]
  · have h := ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong M s q' hs hsq' hq'M
      φ hφ hφα hφβ i p (by rw [hp1]; exact one_dvd _)
    unfold placeWidth at h
    rw [hp1, hr1 i, hjw' p (hjne p haff hss), hjw' _ (hjne _ (hrest_aff i) (hrest_nss i))] at h
    simpa using h

private theorem wild_branch
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime)
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M) (hq5 : q' < 5)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (hp : q'.Prime)
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    (W : Place k ↥(charLDegeneracyRoof k M s)) :
    (placeWidthChar q' M (W.restrictAlong (heckeBetaC k M s) hβ) : ℤ)
        * (W.ramificationIndexAlong (heckeAlphaC k M s) : ℤ)
      = (placeWidthChar q' M (W.restrictAlong (heckeAlphaC k M s) hα) : ℤ)
        * (W.ramificationIndexAlong (heckeBetaC k M s) : ℤ) := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  haveI : Fact q'.Prime := ⟨hp⟩
  have hq'Ms : ¬ q' ∣ M * s := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact hq'M h
    · exact hsq' ((Nat.prime_dvd_prime_iff_eq hp hs).mp h).symm

  have hjw : ∀ j : k, j ≠ 0 → jWidthChar q' j = 1 := by
    have h4 : q' ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
    have h2 := hp.two_le
    obtain rfl | rfl : q' = 2 ∨ q' = 3 := by omega
    · exact fun j hj => jWidthChar_two_of_ne_zero hj
    · exact fun j hj => jWidthChar_three_of_ne_zero hj
  have h1728 : (1728 : k) = 0 := by
    have h4 : q' ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
    have h2 := hp.two_le
    obtain rfl | rfl : q' = 2 ∨ q' = 3 := by omega
    · exact_mod_cast (CharP.cast_eq_zero_iff k 2 1728).mpr (by norm_num)
    · exact_mod_cast (CharP.cast_eq_zero_iff k 3 1728).mpr (by norm_num)

  have hroof : charLDegeneracyRoof k M s = modularFunctionFieldC k (M * s) :=
    (charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' M s hq'Ms).trans
      (modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (M * s) hq'Ms).symm

  unfold HeckeAlphaCIntegral at hα
  unfold HeckeBetaCIntegral at hβ
  have hA : ∀ x : ↥(modularFunctionFieldC k M),
      ((heckeAlphaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) = x := by
    intro x
    simp
  have hB : ∀ x : ↥(modularFunctionFieldC k M),
      ((heckeBetaC k M s x : ↥(charLDegeneracyRoof k M s)) : LaurentSeries k) = qExpand k s x := by
    intro x
    simp
  generalize heckeAlphaC k M s = α at hα hA ⊢
  generalize heckeBetaC k M s = β at hβ hB ⊢

  generalize charLDegeneracyRoof k M s = R at hroof W α β hα hβ hA hB ⊢
  subst hroof
  obtain ⟨φ, hφ0, hφ1⟩ : ∃ φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))),
      φ 0 = α ∧ φ 1 = β := ⟨![α, β], rfl, rfl⟩
  subst hφ0
  subst hφ1
  have hφ : ∀ i, (φ i).toRingHom.IsIntegral := by
    intro i
    fin_cases i
    · exact hα
    · exact hβ
  by_cases hss : W ∈ ssPlaces q' (M * s) k
  ·
    have hpres := (degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s q' hs hsq' hq'M hsM
      φ hφ hA hB).2.2.2.1
    have h8 := ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
      M s q' hs hsq' hq'M
      (fun i (v : ↥(ssPlaces q' (M * s) k)) => ⟨Place.restrictAlong (φ i) (hφ i) v, hpres i v v.2⟩)
      (fun i (v : ↥(ssPlaces q' (M * s) k)) => Place.ramificationIndexAlong (φ i) v)
      φ hφ hA hB (fun _ _ => rfl) (fun _ _ => rfl)
    have h0 := h8 0 ⟨W, hss⟩
    have h1 := h8 1 ⟨W, hss⟩
    dsimp only at h0 h1
    rw [← h0, ← h1]
    push_cast
    ring
  · by_cases haff : IsAffineGeomPlace k (M * s) W
    · obtain ⟨hw1, he1⟩ := wild_widths_and_indices_of_not_mem_ssPlaces M s q' hs hsq' hq'M hsM hq5 hjw h1728
        φ hφ hA hB W haff hss
      rw [hw1 0, hw1 1, he1 0, he1 1]
    ·
      have htr := (degeneracyPair_finrankAlong_and_place_transports M s q' hs hsq' hq'M hsM
        φ hφ hA hB).2.2.1
      have hzero : ∀ i : Fin 2,
          placeWidthChar q' M (W.restrictAlong (φ i) (hφ i)) = 0 := by
        intro i
        apply placeWidthChar_of_placeRamificationJ_eq_zero
        apply placeRamificationJ_eq_zero_of_not_isAffineGeomPlace
        intro h
        exact haff ((htr i W).mp h)
      rw [hzero 0, hzero 1]
      simp

private theorem branch_lt_five
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M) (hq5 : q' < 5)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    (W : Place k ↥(charLDegeneracyRoof k M s)) :
    (placeWidthChar q' M (W.restrictAlong (heckeBetaC k M s) hβ) : ℤ)
        * (W.ramificationIndexAlong (heckeAlphaC k M s) : ℤ)
      = (placeWidthChar q' M (W.restrictAlong (heckeAlphaC k M s) hα) : ℤ)
        * (W.ramificationIndexAlong (heckeBetaC k M s) : ℤ) := by
  exact wild_branch M s q' hs hsq' hq'M hsM hq5 Fact.out hα hβ W

theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    (W : Place k ↥(charLDegeneracyRoof k M s)) :
    (placeWidthChar q' M (W.restrictAlong (heckeBetaC k M s) hβ) : ℤ)
        * (W.ramificationIndexAlong (heckeAlphaC k M s) : ℤ)
      = (placeWidthChar q' M (W.restrictAlong (heckeAlphaC k M s) hα) : ℤ)
        * (W.ramificationIndexAlong (heckeBetaC k M s) : ℤ) := by
  by_cases hq5 : 5 ≤ q'
  · exact branch_five_le M s q' hs hsq' hq'M hsM hα hβ W hq5
  · exact branch_lt_five M s q' hs hsq' hq'M hsM (Nat.lt_of_not_le hq5) hα hβ W

end S_ModularCurve_placeWidthChar_restrictAlong_mul_ramificationIndexAlong_heckeAlphaC_heckeBetaC_cross_of_prime
end P2MW
export P2MW.S_ModularCurve_placeWidthChar_restrictAlong_mul_ramificationIndexAlong_heckeAlphaC_heckeBetaC_cross_of_prime (solution)
