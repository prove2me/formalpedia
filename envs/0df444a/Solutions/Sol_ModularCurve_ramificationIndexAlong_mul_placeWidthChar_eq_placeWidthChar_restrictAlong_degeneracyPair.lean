-- Prove2me | solution 1 for ModularCurve.ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6595ee6e-83ae-5d90-8c4e-919681266eb2

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_placeRamificationJ_mul_jWidthChar_evalAt_jNGeomGen_eq_of_mem_ssPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois"
p2m_attr_erase "simp" "ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"
p2m_attr_erase "simp" "WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option Elab.async false
set_option autoImplicit false

namespace DegeneracyWidthTransport

open AlgebraicCurve ModularCurve

private theorem mul_div_mul_left_cancel {m e W : ℕ} (h : m * e ∣ W) (he : 0 < e) :
    m * (W / (m * e)) = W / e := by
  obtain ⟨t, rfl⟩ := h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Nat.mul_div_cancel_left t (Nat.mul_pos hm he),
      (by ring : m * e * t = e * (m * t)), Nat.mul_div_cancel_left (m * t) he]

private theorem quot_eq_of_readings {e eJp eJv eJNp eJNv Wa Wa' Wb : ℕ}
    (hdp : eJp ∣ Wa) (hdv : eJv ∣ Wa') (h1p : eJp * Wb = eJNp * Wa) (h1v : eJv * Wb = eJNv * Wa')
    (hN : eJNp = e * eJNv) (hp : 0 < eJp) (hv : 0 < eJv) (hNv : 0 < eJNv) :
    e * (Wa / eJp) = Wa' / eJv := by
  obtain ⟨t, rfl⟩ := hdp
  obtain ⟨t', rfl⟩ := hdv
  rw [Nat.mul_div_cancel_left t hp, Nat.mul_div_cancel_left t' hv]
  have hbp : Wb = eJNp * t :=
    Nat.eq_of_mul_eq_mul_left hp (by rw [h1p]; ring)
  have hbv : Wb = eJNv * t' :=
    Nat.eq_of_mul_eq_mul_left hv (by rw [h1v]; ring)
  refine Nat.eq_of_mul_eq_mul_left hNv ?_
  calc eJNv * (e * t) = eJNp * t := by rw [hN]; ring
    _ = eJNv * t' := by rw [← hbp, hbv]

private theorem pos_of_natCast_mul_pos {e : ℕ} {x : ℤ} (h : 0 < (e : ℤ) * x) : 0 < x := by
  by_contra hx
  exact absurd h (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg e) (not_lt.mp hx)))

private theorem toNat_eq_mul_toNat {e : ℕ} {x y : ℤ} (h : y = (e : ℤ) * x) (hx : 0 ≤ x) :
    y.toNat = e * x.toNat := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  subst h
  rw [← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]

private theorem toNat_pos {x : ℤ} (hx : 0 < x) : 0 < x.toNat := by
  omega

variable {k : Type*} [Field k] {N N' : ℕ} [NeZero N] [NeZero N']

private theorem ord_sub_algebraMap_eq_mul
    (φ : ↥(modularFunctionFieldC k N) →ₐ[k] ↥(modularFunctionFieldC k N')) (hφ : φ.toRingHom.IsIntegral)
    {g : ↥(modularFunctionFieldC k N)} {g' : ↥(modularFunctionFieldC k N')} (hg : φ g = g')
    (w' : Place k ↥(modularFunctionFieldC k N')) (c : k) :
    w'.ord (g' - algebraMap k ↥(modularFunctionFieldC k N') c)
      = Place.ramificationIndexAlong φ w'
          * (w'.restrictAlong φ hφ).ord (g - algebraMap k ↥(modularFunctionFieldC k N) c) := by
  rw [← Place.ord_restrictAlong φ hφ w', map_sub, hg, AlgHom.commutes]

private theorem transport_of_jGeomGen (q' : ℕ) [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    (φ : ↥(modularFunctionFieldC k N) →ₐ[k] ↥(modularFunctionFieldC k N')) (hφ : φ.toRingHom.IsIntegral)
    (hgen : φ (jGeomGen k N) = jGeomGen k N')
    (p : Place k ↥(modularFunctionFieldC k N')) (hp : p ∈ ssPlaces q' N' k) (hv : p.restrictAlong φ hφ ∈ ssPlaces q' N k)
    (hdvd : placeRamificationJ N' p ∣ jWidthChar q' (p.evalAt (jGeomGen k N'))) :
    Place.ramificationIndexAlong φ p * placeWidthChar q' N' p
      = placeWidthChar q' N (p.restrictAlong φ hφ) := by
  have hcp := (show IsSupersingularPlace q' N' k p from hp).isCentreOf_evalAt
  have hcv := (show IsSupersingularPlace q' N k (p.restrictAlong φ hφ) from hv).isCentreOf_evalAt
  have hcp1 : 0 < p.ord (jGeomGen k N' - algebraMap k _ (p.evalAt (jGeomGen k N'))) := hcp.1
  have hord := ord_sub_algebraMap_eq_mul φ hφ hgen p (p.evalAt (jGeomGen k N'))
  have hposv : 0 < (p.restrictAlong φ hφ).ord
      (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (p.evalAt (jGeomGen k N'))) :=
    pos_of_natCast_mul_pos (hord ▸ hcp1)
  have hcv' : IsCentreOf k N
      (p.evalAt (jGeomGen k N'), (p.restrictAlong φ hφ).evalAt (jNGeomGen k N))
      (p.restrictAlong φ hφ) := ⟨hposv, hcv.2⟩
  have ha : (p.restrictAlong φ hφ).evalAt (jGeomGen k N) = p.evalAt (jGeomGen k N') :=
    hcv'.evalAt_jGeomGen
  have heJ : placeRamificationJ N' p
      = Place.ramificationIndexAlong φ p * placeRamificationJ N (p.restrictAlong φ hφ) := by
    unfold placeRamificationJ
    rw [ha]
    exact toNat_eq_mul_toNat hord hposv.le
  have hepos : 0 < placeRamificationJ N (p.restrictAlong φ hφ) := by
    unfold placeRamificationJ
    rw [ha]
    exact toNat_pos hposv
  rw [heJ] at hdvd
  unfold placeWidthChar
  rw [ha, heJ]
  exact mul_div_mul_left_cancel hdvd hepos

private theorem transport_of_jNGeomGen (q' : ℕ) [Fact q'.Prime] [CharP k q'] [IsAlgClosed k]
    [DecidableEq k] (hN : ¬ q' ∣ N) (hN' : ¬ q' ∣ N')
    (φ : ↥(modularFunctionFieldC k N) →ₐ[k] ↥(modularFunctionFieldC k N')) (hφ : φ.toRingHom.IsIntegral)
    (hgen : φ (jNGeomGen k N) = jNGeomGen k N')
    (p : Place k ↥(modularFunctionFieldC k N')) (hp : p ∈ ssPlaces q' N' k) (hv : p.restrictAlong φ hφ ∈ ssPlaces q' N k)
    (hdvdp : placeRamificationJ N' p ∣ jWidthChar q' (p.evalAt (jGeomGen k N')))
    (hdvdv : placeRamificationJ N (p.restrictAlong φ hφ)
      ∣ jWidthChar q' ((p.restrictAlong φ hφ).evalAt (jGeomGen k N))) :
    Place.ramificationIndexAlong φ p * placeWidthChar q' N' p
      = placeWidthChar q' N (p.restrictAlong φ hφ) := by
  have hcp := (show IsSupersingularPlace q' N' k p from hp).isCentreOf_evalAt
  have hcv := (show IsSupersingularPlace q' N k (p.restrictAlong φ hφ) from hv).isCentreOf_evalAt
  have hcp2 : 0 < p.ord (jNGeomGen k N' - algebraMap k _ (p.evalAt (jNGeomGen k N'))) := hcp.2
  have hcp1 : 0 < p.ord (jGeomGen k N' - algebraMap k _ (p.evalAt (jGeomGen k N'))) := hcp.1
  have hcv1 : 0 < (p.restrictAlong φ hφ).ord (jGeomGen k N - algebraMap k _
      ((p.restrictAlong φ hφ).evalAt (jGeomGen k N))) := hcv.1
  have hord := ord_sub_algebraMap_eq_mul φ hφ hgen p (p.evalAt (jNGeomGen k N'))
  have hposv : 0 < (p.restrictAlong φ hφ).ord
      (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (p.evalAt (jNGeomGen k N'))) :=
    pos_of_natCast_mul_pos (hord ▸ hcp2)
  have hcv' : IsCentreOf k N
      ((p.restrictAlong φ hφ).evalAt (jGeomGen k N), p.evalAt (jNGeomGen k N'))
      (p.restrictAlong φ hφ) := ⟨hcv.1, hposv⟩
  have hb : (p.restrictAlong φ hφ).evalAt (jNGeomGen k N) = p.evalAt (jNGeomGen k N') :=
    hcv'.evalAt_jNGeomGen

  have h1p := placeRamificationJ_mul_jWidthChar_evalAt_jNGeomGen_eq_of_mem_ssPlaces hN' hp
  have h1v := placeRamificationJ_mul_jWidthChar_evalAt_jNGeomGen_eq_of_mem_ssPlaces hN hv
  rw [hb] at h1v

  have heJN : (p.ord (jNGeomGen k N' - algebraMap k ↥(modularFunctionFieldC k N') (p.evalAt (jNGeomGen k N')))).toNat
      = Place.ramificationIndexAlong φ p * ((p.restrictAlong φ hφ).ord
          (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (p.evalAt (jNGeomGen k N')))).toNat :=
    toNat_eq_mul_toNat hord hposv.le

  have hpJ : 0 < placeRamificationJ N' p := toNat_pos hcp1
  have hvJ : 0 < placeRamificationJ N (p.restrictAlong φ hφ) := toNat_pos hcv1
  have hvJN : 0 < ((p.restrictAlong φ hφ).ord
      (jNGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (p.evalAt (jNGeomGen k N')))).toNat := toNat_pos hposv
  unfold placeWidthChar
  exact quot_eq_of_readings hdvdp hdvdv h1p h1v heJN hpJ hvJ hvJN

end DegeneracyWidthTransport

open AlgebraicCurve ModularCurve DegeneracyWidthTransport in
theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (ab : Fin 2 → ↥(ssPlaces q' (M * s) k) → ↥(ssPlaces q' M k))
      (m : Fin 2 → ↥(ssPlaces q' (M * s) k) → ℕ)
      (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x)
      (hab : ∀ i p, (ab i p : Place k (modularFunctionFieldC k M))
        = Place.restrictAlong (φ i) (hφ i) ↑p)
      (hm : ∀ i p, m i p = Place.ramificationIndexAlong (φ i)
        (p : Place k (modularFunctionFieldC k (M * s)))),
    ∀ (i : Fin 2) (p : ↥(ssPlaces q' (M * s) k)),
      m i p * placeWidthChar q' (M * s)
          (p : Place k (modularFunctionFieldC k (M * s)))
        = placeWidthChar q' M (ab i p : Place k (modularFunctionFieldC k M)) := by
  intro ab m φ hφ hφα hφβ hab hm i p
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  have hq : q'.Prime := Fact.out
  have hq'Ms : ¬ q' ∣ M * s := fun h =>
    ((Nat.Prime.dvd_mul hq).mp h).elim hq'M fun h' => hsq' ((Nat.prime_dvd_prime_iff_eq hq hs).mp h').symm

  have hdvd : ∀ {L : ℕ} [NeZero L] (_ : ¬ q' ∣ L) {w : Place k (modularFunctionFieldC k L)}
      (_ : w ∈ ssPlaces q' L k), placeRamificationJ L w ∣ jWidthChar q' (w.evalAt (jGeomGen k L)) := by
    intro L _ hL w hw
    by_cases h5 : 5 ≤ q'
    · rw [jWidthChar_of_five_le h5]
      exact placeRamificationJ_dvd_jWidth_of_mem_ssPlaces h5 hL hw
    · have h2 := hq.two_le
      have h4 : q' ≠ 4 := fun h => by subst h; exact absurd hq (by decide)
      obtain rfl | rfl : q' = 2 ∨ q' = 3 := by omega
      · exact placeRamificationJ_dvd_jWidthChar_two_of_mem_ssPlaces hL hw
      · exact placeRamificationJ_dvd_jWidthChar_three_of_mem_ssPlaces hL hw
  have hvss : Place.restrictAlong (φ i) (hφ i) (p : Place k (modularFunctionFieldC k (M * s)))
      ∈ ssPlaces q' M k := by
    rw [← hab]; exact (ab i p).2
  rw [hm, hab]

  have hgen0 : φ 0 (jGeomGen k M) = jGeomGen k (M * s) := by
    apply Subtype.ext
    simp only [hφα, coe_jGeomGen]
  have hgen1 : φ 1 (jNGeomGen k M) = jNGeomGen k (M * s) := by
    apply Subtype.ext
    simp only [hφβ, coe_jNGeomGen]
    show qExpand k s (qExpand k M (jqModC k)) = qExpand k (M * s) (jqModC k)
    rw [qExpand_qExpand, qExpand_congr (Nat.mul_comm s M)]
  fin_cases i
  · exact transport_of_jGeomGen q' (φ 0) (hφ 0) hgen0 ↑p p.2 hvss (hdvd hq'Ms p.2)
  · exact transport_of_jNGeomGen q' hq'M hq'Ms (φ 1) (hφ 1) hgen1 ↑p p.2 hvss (hdvd hq'Ms p.2)
      (hdvd hq'M hvss)

#print axioms solution

end S_ModularCurve_ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair
end P2MW
export P2MW.S_ModularCurve_ramificationIndexAlong_mul_placeWidthChar_eq_placeWidthChar_restrictAlong_degeneracyPair (solution)
