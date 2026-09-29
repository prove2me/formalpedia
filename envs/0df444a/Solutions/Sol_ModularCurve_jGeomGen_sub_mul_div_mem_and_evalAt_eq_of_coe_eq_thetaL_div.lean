-- Prove2me | solution 1 for ModularCurve.jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/af0dee3c-39ec-5fc4-8834-f4c21920b753

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_Place_mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord
import Theorems.Thm_AlgebraicCurve_Place_derivation_apply_eq_diffCoeff_D_mul
import Theorems.Thm_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC
import Theorems.Thm_ModularCurve_theta_mul
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_ord_pos
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div.ModularCurve KaehlerDifferential"

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Place.ord_zero Place.ord_inv Place.mem_iff_ord_nonneg Place.residueInv_algebraMap Place.evalAt_of_mem Place.diffCoeff Place.mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord Place.derivation_apply_eq_diffCoeff_D_mul Place.exists_ord_eq_one Place.evalAt_mul Place.evalAt_inv" namespace Place p2m_export "AlgebraicCurve.Place" "ext ResidueField ord ord_zero ord_inv ord_coe_unit toValuationSubring mem_iff_ord_nonneg IsRational residueInv_algebraMap evalAt evalAt_of_mem diffCoeff uniformizer_alt mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord derivation_apply_eq_diffCoeff_D_mul exists_ord_eq_one evalAt_mul evalAt_inv" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in
theorem AlgebraicCurve.Place.isUnit_of_evalAt_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  by_contra hu
  apply h
  rw [Place.evalAt_of_mem v hf, (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu),
    ← map_zero (algebraMap K v.ResidueField), Place.residueInv_algebraMap]

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in
theorem AlgebraicCurve.Place.ne_zero_and_ord_eq_zero_of_evalAt_ne_zero {K F : Type*} [Field K] [Field F]
    [Algebra K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    f ≠ 0 ∧ v.ord f = 0 := by
  obtain ⟨u, hu⟩ := Place.isUnit_of_evalAt_ne_zero v hf h
  have hcoe : ((u : v.toValuationSubring) : F) = f := by rw [hu]
  refine ⟨?_, ?_⟩
  · rw [← hcoe]; simp [ne_eq, ZeroMemClass.coe_eq_zero]
  · rw [← hcoe]; exact v.ord_coe_unit u

p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

theorem AlgebraicCurve.Place.mul_derivation_div_mem_and_evalAt_eq_div
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x₀ : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    (v : Place K F) (hv : v.IsRational) (δ : Derivation K F F) {u f : F}
    (hu : δ u = 1) (hu0 : u ≠ 0) (hf : f ≠ 0) (hordK : ((v.ord u : ℤ) : K) ≠ 0) :
    u * δ f / f ∈ v.toValuationSubring ∧
      v.evalAt (u * δ f / f) = ((v.ord f : ℤ) : K) / ((v.ord u : ℤ) : K) := by
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨t, ht⟩ := Place.exists_ord_eq_one v

  have hR2 : ∀ h : F, δ h = Place.diffCoeff t (KaehlerDifferential.D K F h) * δ t :=
    fun h => Place.derivation_apply_eq_diffCoeff_D_mul x₀ v ht δ h
  have hDu : Place.diffCoeff t (KaehlerDifferential.D K F u) * δ t = 1 := by rw [← hR2, hu]
  have hDu0 : Place.diffCoeff t (KaehlerDifferential.D K F u) ≠ 0 := left_ne_zero_of_mul_eq_one hDu
  have hδt : δ t = (Place.diffCoeff t (KaehlerDifferential.D K F u))⁻¹ :=
    eq_inv_of_mul_eq_one_right hDu

  obtain ⟨hAmem, hAval⟩ := Place.mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord x₀ v ht hf
  obtain ⟨hBmem, hBval⟩ := Place.mul_diffCoeff_D_div_mem_and_evalAt_eq_intCast_ord x₀ v ht hu0
  set A := t * Place.diffCoeff t (KaehlerDifferential.D K F f) / f with hA
  set B := t * Place.diffCoeff t (KaehlerDifferential.D K F u) / u with hB
  have hBne : v.evalAt B ≠ 0 := by rw [hBval]; exact hordK
  obtain ⟨hB0, hordB⟩ := Place.ne_zero_and_ord_eq_zero_of_evalAt_ne_zero v hBmem hBne
  have hBinv : B⁻¹ ∈ v.toValuationSubring :=
    (Place.mem_iff_ord_nonneg v (inv_ne_zero hB0)).mpr (by rw [Place.ord_inv, hordB, neg_zero])
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht
  have hexpr : u * δ f / f = A * B⁻¹ := by
    rw [hR2 f, hδt, hA, hB]
    field_simp
  rw [hexpr]
  refine ⟨mul_mem hAmem hBinv, ?_⟩
  rw [Place.evalAt_mul v hv hAmem hBinv, Place.evalAt_inv v hv hB0 hordB, hAval, hBval, div_eq_mul_inv]

namespace ModularCurve
p2m_export "ModularCurve" "placeRamificationJ jGeomGen IsAffineGeomPlace exists_isCentreOf_of_isRational jqModC jqNModC modularFunctionFieldC jqNModC_mem coeff_jqModC_neg_one jWidth_dvd_six thetaL thetaL_apply thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC theta_mul finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero nonempty_modularPolynomialData placeRamificationJ_dvd_jWidth_of_ord_pos"
p2m_open "ModularCurve"

section Theta

variable {L : Type*} [Field L]

theorem coeff_thetaL_eq_mul (f : LaurentSeries L) (n : ℤ) :
    (thetaL L f).coeff n = (n : L) * f.coeff n := by
  rw [thetaL_apply, LaurentSeries.derivative_apply, HahnSeries.coeff_single_mul, one_mul,
    LaurentSeries.hasseDeriv_coeff, Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem thetaL_mul_eq (f g : LaurentSeries L) : thetaL L (f * g) = f * thetaL L g + g * thetaL L f := by
  simp only [thetaL_apply]
  exact theta_mul f g

theorem thetaL_C_eq_zero (c : L) : thetaL L (HahnSeries.C c : LaurentSeries L) = 0 := by
  ext n
  rw [coeff_thetaL_eq_mul, HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs with h
  · subst h; simp
  · simp

theorem C_eq_algebraMap (c : L) :
    (HahnSeries.C c : LaurentSeries L) = algebraMap L (LaurentSeries L) c := by
  rw [HahnSeries.algebraMap_apply']
  simp

theorem thetaL_jqModC_ne_zero : thetaL L (jqModC L) ≠ 0 := by
  intro h
  have hc := congrArg (fun s : LaurentSeries L => s.coeff (-1)) h
  simp only [coeff_thetaL_eq_mul, coeff_jqModC_neg_one] at hc
  simp at hc

end Theta

section DerivTheta

variable (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (N : ℕ) [NeZero N]

noncomputable def thetaDivFun (hpN : ¬ p ∣ N) (h : modularFunctionFieldC K N) : modularFunctionFieldC K N :=
  ⟨thetaL K (h : LaurentSeries K) / thetaL K (jqModC K),
    thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC K p N hpN h h.2⟩

variable {K p N}

theorem coe_thetaDivFun (hpN : ¬ p ∣ N) (h : modularFunctionFieldC K N) :
    ((thetaDivFun K p N hpN h : modularFunctionFieldC K N) : LaurentSeries K) =
      thetaL K (h : LaurentSeries K) / thetaL K (jqModC K) := rfl

theorem thetaDivFun_add (hpN : ¬ p ∣ N) (a b : modularFunctionFieldC K N) :
    thetaDivFun K p N hpN (a + b) = thetaDivFun K p N hpN a + thetaDivFun K p N hpN b := by
  apply Subtype.ext
  rw [IntermediateField.coe_add, coe_thetaDivFun, coe_thetaDivFun, coe_thetaDivFun,
    IntermediateField.coe_add, map_add, add_div]

theorem thetaDivFun_mul (hpN : ¬ p ∣ N) (a b : modularFunctionFieldC K N) :
    thetaDivFun K p N hpN (a * b) = a * thetaDivFun K p N hpN b + b * thetaDivFun K p N hpN a := by
  apply Subtype.ext
  rw [IntermediateField.coe_add, IntermediateField.coe_mul, IntermediateField.coe_mul, coe_thetaDivFun,
    coe_thetaDivFun, coe_thetaDivFun, IntermediateField.coe_mul, thetaL_mul_eq]
  ring

theorem thetaDivFun_algebraMap (hpN : ¬ p ∣ N) (c : K) :
    thetaDivFun K p N hpN (algebraMap K (modularFunctionFieldC K N) c) = 0 := by
  apply Subtype.ext
  rw [coe_thetaDivFun, IntermediateField.coe_zero]
  have hc : ((algebraMap K (modularFunctionFieldC K N) c : modularFunctionFieldC K N) : LaurentSeries K)
      = HahnSeries.C c := by
    rw [C_eq_algebraMap]; rfl
  rw [hc, thetaL_C_eq_zero, zero_div]

variable (K p N) in

set_option synthInstance.maxHeartbeats 1600000 in

noncomputable def derivationThetaDiv (hpN : ¬ p ∣ N) :
    Derivation K (modularFunctionFieldC K N) (modularFunctionFieldC K N) where
  toFun := thetaDivFun K p N hpN
  map_add' := thetaDivFun_add hpN
  map_smul' c a := by
    show thetaDivFun K p N hpN (c • a) = c • thetaDivFun K p N hpN a
    rw [Algebra.smul_def, Algebra.smul_def, thetaDivFun_mul, thetaDivFun_algebraMap, mul_zero, add_zero]
  map_one_eq_zero' := by
    show thetaDivFun K p N hpN 1 = 0
    rw [← map_one (algebraMap K (modularFunctionFieldC K N)), thetaDivFun_algebraMap]
  leibniz' a b := by
    show thetaDivFun K p N hpN (a * b) = a • thetaDivFun K p N hpN b + b • thetaDivFun K p N hpN a
    rw [smul_eq_mul, smul_eq_mul, thetaDivFun_mul]

theorem coe_derivationThetaDiv_apply (hpN : ¬ p ∣ N) (h : modularFunctionFieldC K N) :
    ((derivationThetaDiv K p N hpN h : modularFunctionFieldC K N) : LaurentSeries K) =
      thetaL K (h : LaurentSeries K) / thetaL K (jqModC K) := rfl

theorem derivationThetaDiv_jGeomGen (hpN : ¬ p ∣ N) :
    derivationThetaDiv K p N hpN (jGeomGen K N) = 1 := by
  apply Subtype.ext
  rw [coe_derivationThetaDiv_apply, IntermediateField.coe_one]
  exact div_self thetaL_jqModC_ne_zero

theorem derivationThetaDiv_algebraMap (hpN : ¬ p ∣ N) (c : K) :
    derivationThetaDiv K p N hpN (algebraMap K (modularFunctionFieldC K N) c) = 0 :=
  thetaDivFun_algebraMap hpN c

end DerivTheta

theorem natCast_ne_zero_of_dvd_six (K : Type*) [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (hp5 : 5 ≤ p) {e : ℕ} (he : e ∣ 6) : (e : K) ≠ 0 := by
  intro h0
  rw [CharP.cast_eq_zero_iff K p] at h0
  have h6 : p ∣ 6 := h0.trans he
  have hple : p ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  have hprime : p.Prime := hp.out
  clear h0
  interval_cases p
  · exact absurd h6 (by decide)
  · exact absurd hprime (by decide)

end ModularCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (x : Place K (modularFunctionFieldC K N)) (hxr : x.IsRational) (hx : IsAffineGeomPlace K N x)
    (f g : ↥(modularFunctionFieldC K N)) (hf : f ≠ 0)
    (hg : (g : LaurentSeries K) = thetaL K (f : LaurentSeries K) / thetaL K (jqModC K)) :
    (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) (x.evalAt (jGeomGen K N))) * g / f
        ∈ x.toValuationSubring ∧
      x.evalAt ((jGeomGen K N - algebraMap K (modularFunctionFieldC K N) (x.evalAt (jGeomGen K N))) * g / f)
        = ((x.ord f : ℤ) : K) / ((placeRamificationJ N x : ℕ) : K) := by

  haveI : PerfectField K := IsAlgClosed.perfectField K
  have hNK : (N : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p]; exact hpN
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  haveI := (finiteDimensional_and_isSeparable_adjoin_jqNModC_of_natCast_ne_zero K N hNK data).1

  set J : modularFunctionFieldC K N := jGeomGen K N with hJ
  set c : modularFunctionFieldC K N :=
    algebraMap K (modularFunctionFieldC K N) (x.evalAt (jGeomGen K N)) with hc
  set δ := derivationThetaDiv K p N hpN with hδ

  have hpos : 0 < x.ord (J - c) := by
    have hcen := (exists_isCentreOf_of_isRational hxr hx).1
    dsimp only at hcen
    exact hcen
  have hJc0 : J - c ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hpos; exact lt_irrefl _ hpos
  have he : ((placeRamificationJ N x : ℕ) : ℤ) = x.ord (J - c) := by
    show (((x.ord (jGeomGen K N - algebraMap K (modularFunctionFieldC K N)
      (x.evalAt (jGeomGen K N)))).toNat : ℕ) : ℤ) = _
    exact Int.toNat_of_nonneg hpos.le
  have hepos : 0 < placeRamificationJ N x := by
    have : (0 : ℤ) < ((placeRamificationJ N x : ℕ) : ℤ) := by rw [he]; exact hpos
    exact_mod_cast this
  have heK : ((placeRamificationJ N x : ℕ) : K) ≠ 0 :=
    natCast_ne_zero_of_dvd_six K p hp5
      ((placeRamificationJ_dvd_jWidth_of_ord_pos hp5 hpN hepos).trans (jWidth_dvd_six _))
  have hordK : ((x.ord (J - c) : ℤ) : K) ≠ 0 := by rw [← he, Int.cast_natCast]; exact heK

  have hδu : δ (J - c) = 1 := by
    have h1 : δ (J - c) = δ J - δ c := (δ : modularFunctionFieldC K N →ₗ[K] modularFunctionFieldC K N).map_sub J c
    rw [h1, hJ, derivationThetaDiv_jGeomGen hpN, hc, derivationThetaDiv_algebraMap hpN, sub_zero]
  have hδf : δ f = g := Subtype.ext (by rw [coe_derivationThetaDiv_apply]; exact hg.symm)

  have key := Place.mul_derivation_div_mem_and_evalAt_eq_div (⟨jqNModC K N, jqNModC_mem K N⟩ :
    modularFunctionFieldC K N) x hxr δ hδu hJc0 hf hordK
  rw [hδf, ← he, Int.cast_natCast] at key
  exact key

end S_ModularCurve_jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div
end P2MW
export P2MW.S_ModularCurve_jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div (solution)
