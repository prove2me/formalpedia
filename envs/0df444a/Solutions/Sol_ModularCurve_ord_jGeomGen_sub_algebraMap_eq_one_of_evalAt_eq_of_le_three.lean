-- Prove2me | solution 1 for ModularCurve.ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/84d99031-74ac-58c4-9149-054a4d0b9a4b

import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_ModularCurve_exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_variableChange_mk_neg_one_smul_eq_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

namespace P2MS13SmallPrime

variable {K : Type*} [Field K] [DecidableEq K]

def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

def autPt {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

theorem autPt_apply {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

theorem autPt_eq_iff_heq {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

theorem heq_some {V V' : WeierstrassCurve.Affine K} (hV : V' = V) {x y : K}
    {h : V.Nonsingular x y} {h' : V'.Nonsingular x y} :
    HEq (Point.some x y h' : V'.Point) (Point.some x y h : V.Point) := by
  subst hV; rfl

theorem some_eq_some {V : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    (hx : x₁ = x₂) (hy : y₁ = y₂) {h₁ : V.Nonsingular x₁ y₁} {h₂ : V.Nonsingular x₂ y₂} :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx hy; rfl

theorem nonsingular_vcInv {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W)
    {x y : K} (h : W.toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular (vcXInv γ x) (vcYInv γ x y) := by
  have h' : (γ • W).toAffine.Nonsingular (vcXInv γ x) (vcYInv γ x y) :=
    (nonsingular_variableChange_iff (vcXInv γ x) (vcYInv γ x y)).mpr
      (by rwa [vcX_vcXInv, vcY_vcYInv])
  rwa [hγ] at h'

theorem autPt_some {W : WeierstrassCurve K} (γ : VariableChange K) (hγ : γ • W = W) {x y : K}
    (h : W.toAffine.Nonsingular x y) :
    autPt γ hγ (.some x y h) = .some (vcXInv γ x) (vcYInv γ x y) (nonsingular_vcInv γ hγ h) := by
  rw [autPt_eq_iff_heq]
  show HEq (Point.some (vcXInv γ x) (vcYInv γ x y) _ : (γ • W).toAffine.Point) _
  exact heq_some (congrArg WeierstrassCurve.toAffine hγ)

abbrev Aut (W : WeierstrassCurve K) : Subgroup (VariableChange K) :=
  MulAction.stabilizer (VariableChange K) W

theorem smul_eq_of_mem_Aut {W : WeierstrassCurve K} (γ : Aut W) : (γ : VariableChange K) • W = W :=
  MulAction.mem_stabilizer_iff.mp γ.2

theorem one_u : (1 : VariableChange K).u = 1 := rfl
theorem one_r : (1 : VariableChange K).r = 0 := rfl
theorem one_s : (1 : VariableChange K).s = 0 := rfl
theorem one_t : (1 : VariableChange K).t = 0 := rfl
theorem mul_u (C C' : VariableChange K) : (C * C').u = C.u * C'.u := rfl
theorem mul_r (C C' : VariableChange K) : (C * C').r = C.r * C'.u ^ 2 + C'.r := rfl
theorem mul_s (C C' : VariableChange K) : (C * C').s = C'.u * C.s + C'.s := rfl
theorem mul_t (C C' : VariableChange K) :
    (C * C').t = C.t * C'.u ^ 3 + C.r * C'.s * C'.u ^ 2 + C'.t := rfl

theorem vcXInv_one (x : K) : vcXInv (1 : VariableChange K) x = x := by
  rw [vcXInv, one_u, one_r]; simp

theorem vcYInv_one (x y : K) : vcYInv (1 : VariableChange K) x y = y := by
  rw [vcYInv, one_u, one_r, one_s, one_t]; simp

theorem vcXInv_mul (C C' : VariableChange K) (x : K) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, mul_u, mul_r, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

theorem vcYInv_mul (C C' : VariableChange K) (x y : K) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : K) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : K) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, mul_u, mul_r, mul_s, mul_t, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

scoped instance instMulActionAutPoint (W : WeierstrassCurve K) : MulAction (Aut W) W.toAffine.Point where
  smul γ P := autPt γ.1 (smul_eq_of_mem_Aut γ) P
  one_smul P := by
    change autPt (1 : VariableChange K) _ P = P
    rcases P with _ | ⟨x, y, h⟩
    · exact map_zero (autPt (1 : VariableChange K) _)
    · rw [autPt_some]
      exact some_eq_some (vcXInv_one x) (vcYInv_one x y)
  mul_smul γ δ P := by
    change autPt (γ.1 * δ.1) _ P = autPt γ.1 _ (autPt δ.1 _ P)
    rcases P with _ | ⟨x, y, h⟩
    · show autPt (γ.1 * δ.1) _ 0 = autPt γ.1 _ (autPt δ.1 _ 0)
      simp only [map_zero]
    · rw [autPt_some, autPt_some, autPt_some]
      exact some_eq_some (vcXInv_mul _ _ x) (vcYInv_mul _ _ x y)

theorem aut_smul_def {W : WeierstrassCurve K} (γ : Aut W) (P : W.toAffine.Point) :
    γ • P = autPt γ.1 (smul_eq_of_mem_Aut γ) P := rfl

scoped instance instDistribMulActionAutPoint (W : WeierstrassCurve K) :
    DistribMulAction (Aut W) W.toAffine.Point where
  smul_zero γ := map_zero (autPt γ.1 (smul_eq_of_mem_Aut γ))
  smul_add γ P Q := map_add (autPt γ.1 (smul_eq_of_mem_Aut γ)) P Q

open scoped Pointwise

abbrev CycSub (W : WeierstrassCurve K) (N : ℕ) : Type _ :=
  {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}

theorem natCard_smul_addSubgroup {W : WeierstrassCurve K} (γ : Aut W) (H : AddSubgroup W.toAffine.Point) :
    Nat.card (γ • H : AddSubgroup W.toAffine.Point) = Nat.card H := by
  rw [AddSubgroup.pointwise_smul_def]
  exact (Nat.card_congr (H.equivMapOfInjective _ (MulAction.injective γ)).toEquiv).symm

theorem isAddCyclic_smul_addSubgroup {W : WeierstrassCurve K} (γ : Aut W)
    (H : AddSubgroup W.toAffine.Point) [hH : IsAddCyclic H] :
    IsAddCyclic (γ • H : AddSubgroup W.toAffine.Point) := by
  rw [AddSubgroup.pointwise_smul_def]
  exact isAddCyclic_of_surjective (H.equivMapOfInjective _ (MulAction.injective γ))
    (H.equivMapOfInjective _ (MulAction.injective γ)).surjective

scoped instance instMulActionAutCycSub (W : WeierstrassCurve K) (N : ℕ) : MulAction (Aut W) (CycSub W N) where
  smul γ H := ⟨γ • H.1, ⟨by haveI := H.2.1; exact isAddCyclic_smul_addSubgroup γ H.1,
    (natCard_smul_addSubgroup γ H.1).trans H.2.2⟩⟩
  one_smul H := Subtype.ext (one_smul (Aut W) H.1)
  mul_smul γ δ H := Subtype.ext (mul_smul γ δ H.1)

theorem coe_smul_cycSub {W : WeierstrassCurve K} {N : ℕ} (γ : Aut W) (H : CycSub W N) :
    ((γ • H : CycSub W N) : AddSubgroup W.toAffine.Point) = γ • (H : AddSubgroup W.toAffine.Point) := rfl

theorem rel_iff_mem_orbit {W : WeierstrassCurve K} {N : ℕ} [NeZero N] (H H' : CycSub W N) :
    (∃ γ : VariableChange K, γ • W = W ∧
        ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ W.toAffine T) T') ↔
      H' ∈ MulAction.orbit (Aut W) H := by
  constructor
  · rintro ⟨γ, hγ, h⟩
    let g : Aut W := ⟨γ, MulAction.mem_stabilizer_iff.mpr hγ⟩
    have hle : (g • H.1 : AddSubgroup W.toAffine.Point) ≤ H'.1 := by
      intro P hP
      obtain ⟨T, hT, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists P g H.1).mp hP
      obtain ⟨T', hT', hh⟩ := h T hT
      have : g • T = T' := (autPt_eq_iff_heq γ hγ T T').mpr hh
      rwa [this]
    haveI : Finite H'.1 := Nat.finite_of_card_ne_zero (by rw [H'.2.2]; exact NeZero.ne N)
    have heq : (g • H.1 : AddSubgroup W.toAffine.Point) = H'.1 :=
      AddSubgroup.eq_of_le_of_card_ge hle (by rw [natCard_smul_addSubgroup, H.2.2, H'.2.2])
    exact MulAction.mem_orbit_iff.mpr ⟨g, Subtype.ext heq⟩
  · intro hmem
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hmem
    refine ⟨g.1, smul_eq_of_mem_Aut g, fun T hT => ⟨g • T, ?_, ?_⟩⟩
    · exact AddSubgroup.smul_mem_pointwise_smul T g H.1 hT
    · exact (autPt_eq_iff_heq g.1 (smul_eq_of_mem_Aut g) T _).mp rfl

def negVC (W : WeierstrassCurve K) : VariableChange K := ⟨-1, 0, -W.a₁, -W.a₃⟩

theorem negVC_smul (W : WeierstrassCurve K) : negVC W • W = W :=
  WeierstrassCurve.variableChange_mk_neg_one_smul_eq_self W

def negAut (W : WeierstrassCurve K) : Aut W := ⟨negVC W, MulAction.mem_stabilizer_iff.mpr (negVC_smul W)⟩

theorem negAut_smul_point {W : WeierstrassCurve K} (P : W.toAffine.Point) : negAut W • P = -P := by
  change autPt (negVC W) _ P = -P
  rcases P with _ | ⟨x, y, h⟩
  · show autPt (negVC W) _ 0 = -0
    rw [map_zero, neg_zero]
  · rw [autPt_some, Point.neg_some]
    refine some_eq_some ?_ ?_
    · show ((((negVC W).u⁻¹ : Kˣ) : K)) ^ 2 * (x - (negVC W).r) = x
      simp [negVC]
    · show ((((negVC W).u⁻¹ : Kˣ) : K)) ^ 3 * (y - (negVC W).t - (negVC W).s * (x - (negVC W).r))
          = W.toAffine.negY x y
      rw [Affine.negY]
      simp [negVC]
      ring

theorem negAut_mul_self (W : WeierstrassCurve K) : negAut W * negAut W = 1 := by
  refine Subtype.ext (VariableChange.ext ?_ ?_ ?_ ?_)
  · show (negVC W).u * (negVC W).u = 1
    simp [negVC]
  · show (negVC W).r * (negVC W).u ^ 2 + (negVC W).r = 0
    simp [negVC]
  · show (negVC W).u * (negVC W).s + (negVC W).s = 0
    simp [negVC]
  · show (negVC W).t * (negVC W).u ^ 3 + (negVC W).r * (negVC W).s * (negVC W).u ^ 2 + (negVC W).t = 0
    simp only [negVC]
    push_cast
    ring

theorem negAut_smul_addSubgroup {W : WeierstrassCurve K} (H : AddSubgroup W.toAffine.Point) :
    negAut W • H = H := by
  ext P
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hinv : (negAut W)⁻¹ = negAut W :=
    inv_eq_of_mul_eq_one_right (negAut_mul_self W)
  rw [hinv, negAut_smul_point]
  exact neg_mem_iff

theorem negAut_mem_stabilizer {W : WeierstrassCurve K} {N : ℕ} (H : CycSub W N) :
    negAut W ∈ MulAction.stabilizer (Aut W) H :=
  MulAction.mem_stabilizer_iff.mpr (Subtype.ext (negAut_smul_addSubgroup H.1))

theorem eq_one_or_eq_negVC {W : WeierstrassCurve K} (h23 : (2 : K) = 0 ∨ (3 : K) = 0)
    (ha₁ : W.a₁ ≠ 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0)
    (γ : VariableChange K) (h : γ • W = W) : γ = 1 ∨ γ = negVC W := by
  have hU : (γ.u : K) ≠ 0 := γ.u.ne_zero
  have hVU : ((γ.u : K))⁻¹ * (γ.u : K) = 1 := inv_mul_cancel₀ hU
  have e1 : ((γ.u : K))⁻¹ * (W.a₁ + 2 * γ.s) = W.a₁ := by
    have e := congrArg WeierstrassCurve.a₁ h
    rwa [variableChange_a₁, Units.val_inv_eq_inv_val] at e
  have e2 : ((γ.u : K))⁻¹ ^ 2 * (W.a₂ - γ.s * W.a₁ + 3 * γ.r - γ.s ^ 2) = W.a₂ := by
    have e := congrArg WeierstrassCurve.a₂ h
    rwa [variableChange_a₂, Units.val_inv_eq_inv_val] at e
  have e3 : ((γ.u : K))⁻¹ ^ 3 * (W.a₃ + γ.r * W.a₁ + 2 * γ.t) = W.a₃ := by
    have e := congrArg WeierstrassCurve.a₃ h
    rwa [variableChange_a₃, Units.val_inv_eq_inv_val] at e
  have e4 : ((γ.u : K))⁻¹ ^ 4 * (W.a₄ - γ.s * W.a₃ + 2 * γ.r * W.a₂ - (γ.t + γ.r * γ.s) * W.a₁
      + 3 * γ.r ^ 2 - 2 * γ.s * γ.t) = W.a₄ := by
    have e := congrArg WeierstrassCurve.a₄ h
    rwa [variableChange_a₄, Units.val_inv_eq_inv_val] at e
  rcases h23 with h2 | h3
  ·
    have hV : ((γ.u : K))⁻¹ = 1 := by
      have e := mul_eq_zero.mp (show (((γ.u : K))⁻¹ - 1) * W.a₁ = 0 by
        linear_combination e1 - ((γ.u : K))⁻¹ * γ.s * h2)
      exact sub_eq_zero.mp (e.resolve_right ha₁)
    have hUeq : (γ.u : K) = 1 := by linear_combination -(γ.u : K) * hV + hVU
    have hr : γ.r = 0 := by
      have e := mul_eq_zero.mp (show γ.r * W.a₁ = 0 by
        rw [hV] at e3
        linear_combination e3 - γ.t * h2)
      exact e.resolve_right ha₁
    have ht : γ.t = 0 := by
      have e := mul_eq_zero.mp (show γ.t * W.a₁ = 0 by
        rw [hV] at e4
        linear_combination -e4 - γ.s * ha₃ - (-2 * W.a₂ + γ.s * W.a₁ - 3 * γ.r) * hr - γ.s * γ.t * h2)
      exact e.resolve_right ha₁
    have hs : γ.s = 0 ∨ γ.s = -W.a₁ := by
      have e := mul_eq_zero.mp (show γ.s * (γ.s + W.a₁) = 0 by
        rw [hV] at e2
        linear_combination -e2 + 3 * hr)
      rcases e with e | e
      · exact Or.inl e
      · exact Or.inr (by linear_combination e)
    have hu1 : γ.u = 1 := Units.ext (show (γ.u : K) = ((1 : Kˣ) : K) by rw [Units.val_one]; exact hUeq)
    rcases hs with hs | hs
    · exact Or.inl (VariableChange.ext hu1 hr hs ht)
    · refine Or.inr (VariableChange.ext ?_ hr hs ?_)
      · refine Units.ext ?_
        show (γ.u : K) = ((-1 : Kˣ) : K)
        rw [Units.val_neg, Units.val_one, hUeq]
        linear_combination h2
      · show γ.t = -W.a₃
        rw [ht, ha₃, neg_zero]
  ·
    have hV0 : ((γ.u : K))⁻¹ ≠ 0 := inv_ne_zero hU
    have hX2 : W.a₂ - γ.s * W.a₁ + 3 * γ.r - γ.s ^ 2 = 0 := by
      have e := mul_eq_zero.mp
        (show ((γ.u : K))⁻¹ ^ 2 * (W.a₂ - γ.s * W.a₁ + 3 * γ.r - γ.s ^ 2) = 0 by rw [e2]; exact ha₂)
      exact e.resolve_left (pow_ne_zero 2 hV0)
    have hX3 : W.a₃ + γ.r * W.a₁ + 2 * γ.t = 0 := by
      have e := mul_eq_zero.mp
        (show ((γ.u : K))⁻¹ ^ 3 * (W.a₃ + γ.r * W.a₁ + 2 * γ.t) = 0 by rw [e3]; exact ha₃)
      exact e.resolve_left (pow_ne_zero 3 hV0)
    have hs : γ.s = 0 ∨ γ.s = -W.a₁ := by
      have e := mul_eq_zero.mp (show γ.s * (γ.s + W.a₁) = 0 by
        linear_combination -hX2 + γ.r * h3 + ha₂)
      rcases e with e | e
      · exact Or.inl e
      · exact Or.inr (by linear_combination e)
    rcases hs with hs | hs
    ·
      have hV : ((γ.u : K))⁻¹ = 1 := by
        have e := mul_eq_zero.mp (show (((γ.u : K))⁻¹ - 1) * W.a₁ = 0 by
          linear_combination e1 - 2 * ((γ.u : K))⁻¹ * hs)
        exact sub_eq_zero.mp (e.resolve_right ha₁)
      have hUeq : (γ.u : K) = 1 := by linear_combination -(γ.u : K) * hV + hVU
      have ht : γ.t = 0 := by
        have e := mul_eq_zero.mp (show γ.t * W.a₁ = 0 by
          rw [hV] at e4
          linear_combination -e4 - (W.a₃ + γ.r * W.a₁ + 2 * γ.t) * hs + 2 * γ.r * ha₂ + γ.r ^ 2 * h3)
        exact e.resolve_right ha₁
      have hr : γ.r = 0 := by
        have e := mul_eq_zero.mp (show γ.r * W.a₁ = 0 by
          linear_combination hX3 - ha₃ - 2 * ht)
        exact e.resolve_right ha₁
      have hu1 : γ.u = 1 := Units.ext (show (γ.u : K) = ((1 : Kˣ) : K) by rw [Units.val_one]; exact hUeq)
      exact Or.inl (VariableChange.ext hu1 hr hs ht)
    ·
      have hV : ((γ.u : K))⁻¹ = -1 := by
        have e := mul_eq_zero.mp (show (((γ.u : K))⁻¹ + 1) * W.a₁ = 0 by
          linear_combination -e1 + 2 * ((γ.u : K))⁻¹ * hs)
        exact eq_neg_of_add_eq_zero_left (e.resolve_right ha₁)
      have hUeq : (γ.u : K) = -1 := by linear_combination (γ.u : K) * hV - hVU
      have htr : γ.t + γ.r * W.a₁ = 0 := by
        have e := mul_eq_zero.mp (show W.a₁ * (γ.t + γ.r * W.a₁) = 0 by
          rw [hV] at e4
          linear_combination e4 + (W.a₃ + γ.r * W.a₁ + 2 * γ.t) * hs - W.a₁ * ha₃ - 2 * γ.r * ha₂
            - γ.r ^ 2 * h3)
        exact e.resolve_left ha₁
      have hr : γ.r = 0 := by
        have e := mul_eq_zero.mp (show γ.r * W.a₁ = 0 by
          linear_combination 2 * htr - hX3 + ha₃)
        exact e.resolve_right ha₁
      have ht : γ.t = 0 := by linear_combination htr - W.a₁ * hr
      refine Or.inr (VariableChange.ext ?_ hr hs ?_)
      · refine Units.ext ?_
        show (γ.u : K) = ((-1 : Kˣ) : K)
        rw [Units.val_neg, Units.val_one, hUeq]
      · show γ.t = -W.a₃
        rw [ht, ha₃, neg_zero]

theorem smul_cycSub_eq_self {W : WeierstrassCurve K} (h23 : (2 : K) = 0 ∨ (3 : K) = 0)
    (ha₁ : W.a₁ ≠ 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0) {N : ℕ} (g : Aut W) (H : CycSub W N) :
    g • H = H := by
  rcases eq_one_or_eq_negVC h23 ha₁ ha₂ ha₃ g.1 (smul_eq_of_mem_Aut g) with h | h
  · have hg : g = 1 := Subtype.ext h
    rw [hg, one_smul]
  · have hg : g = negAut W := Subtype.ext h
    rw [hg]
    exact Subtype.ext (negAut_smul_addSubgroup H.1)

theorem natCard_fibre_eq_one {W : WeierstrassCurve K} (h23 : (2 : K) = 0 ∨ (3 : K) = 0)
    (ha₁ : W.a₁ ≠ 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0) {N : ℕ} [NeZero N] {α : Type*}
    (f : CycSub W N → α)
    (hf : ∀ H H', f H = f H' ↔ ∃ γ : VariableChange K, γ • W = W ∧
      ∀ T ∈ H.1, ∃ T' ∈ H'.1, HEq (Point.vcInvFun γ W.toAffine T) T')
    (H : CycSub W N) :
    Nat.card {H' : CycSub W N // f H' = f H} = 1 := by
  have e : {H' : CycSub W N // f H' = f H} ≃ MulAction.orbit (Aut W) H :=
    Equiv.subtypeEquivRight (fun H' => by
      rw [eq_comm, hf H H', rel_iff_mem_orbit H H']
      try rfl)
  have horb : MulAction.orbit (Aut W) H = {H} := by
    ext H'
    rw [Set.mem_singleton_iff]
    constructor
    · intro hmem
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hmem
      exact smul_cycSub_eq_self h23 ha₁ ha₂ ha₃ g H
    · intro hH'
      rw [hH']
      exact MulAction.mem_orbit_self H
  rw [Nat.card_congr e, horb]
  exact Nat.card_unique

end P2MS13SmallPrime
p2m_reactivate "P2MW.S_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three.P2MS13SmallPrime"

namespace P2MS13SmallPrime

theorem ord_eq_one_of_eq_full
    (K : Type*) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (h23 : (2 : K) = 0 ∨ (3 : K) = 0)
    (F : IntermediateField K (LaurentSeries K)) (hF : F = modularFunctionFieldFullC K N)
    [hPD : HasPrincipalDivisors K F] (hmem : jqModC K ∈ F) (w : Place K F) (a : K)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (hne : (⟨jqModC K, hmem⟩ : F) - algebraMap K F a ≠ 0)
    (hpos : 0 < w.ord ((⟨jqModC K, hmem⟩ : F) - algebraMap K F a)) :
    w.ord ((⟨jqModC K, hmem⟩ : F) - algebraMap K F a) = 1 := by
  subst hF
  classical

  obtain ⟨D, hD, -⟩ := hPD.exists_divisor _ hne
  let S : Finset (Place K (modularFunctionFieldFullC K N)) := D.support.filter (fun P => 0 < D P)
  have hS : ∀ P, P ∈ S ↔ 0 < P.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)
      - algebraMap K (modularFunctionFieldFullC K N) a) := by
    intro P
    rw [Finset.mem_filter, Finsupp.mem_support_iff, hD P]
    exact ⟨fun h => h.2, fun h => ⟨h.ne', h⟩⟩

  haveI : (WeierstrassCurve.ofJ a).IsElliptic := inferInstance
  have hj : (WeierstrassCurve.ofJ a).j = a := WeierstrassCurve.ofJ_j a

  obtain ⟨f, -, hsurj, hfib, hord⟩ :=
    ModularCurve.exists_orbitMap_cyclicAddSubgroup_places_modularFunctionFieldFullC
      K N hN a (WeierstrassCurve.ofJ a) hj S hS
  obtain ⟨H, rfl⟩ := hsurj w ((hS w).mpr hpos)

  have hW : WeierstrassCurve.ofJ a = WeierstrassCurve.ofJNe0Or1728 a :=
    WeierstrassCurve.ofJ_ne_0_ne_1728 a h0 h1728
  have ha₁ : (WeierstrassCurve.ofJ a).a₁ ≠ 0 := by
    rw [hW]
    exact sub_ne_zero.mpr h1728
  have ha₂ : (WeierstrassCurve.ofJ a).a₂ = 0 := by rw [hW]; rfl
  have ha₃ : (WeierstrassCurve.ofJ a).a₃ = 0 := by rw [hW]; rfl
  rw [hord H, natCard_fibre_eq_one h23 ha₁ ha₂ ha₃ f hfib H, Nat.cast_one]

end P2MS13SmallPrime
p2m_reactivate "P2MW.S_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three.P2MS13SmallPrime"

end
p2m_reactivate "P2MW.S_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three.P2MS13SmallPrime"

open P2MS13SmallPrime in
theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq : q ≤ 3)
    (v : Place k ↥(modularFunctionFieldC k N))
    (a : k) (ha : v.evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) = 1 := by
  classical

  have hjmem : jGeomGen k N ∈ v.toValuationSubring := by
    by_contra hnot
    apply h0
    rw [← ha, Place.evalAt, dif_neg hnot]
  subst ha
  have hrat : v.IsRational :=
    (Place.isRational_iff_deg_eq_one v).mpr (place_deg_eq_one_of_isAlgClosed k N v)
  have hne := jGeomGen_sub_algebraMap_ne_zero k N (v.evalAt (jGeomGen k N))
  have hpos : 0 < v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (v.evalAt (jGeomGen k N))) :=
    ord_sub_evalAt_pos_of_isRational hrat hjmem hne
  have hCF : modularFunctionFieldC k N = modularFunctionFieldFullC k N :=
    ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC k q N hqN
  haveI : HasPrincipalDivisors k (modularFunctionFieldC k N) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k N
  have hNK : (N : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k q]
    exact hqN

  have h23 : (2 : k) = 0 ∨ (3 : k) = 0 := by
    have h2q : 2 ≤ q := (Fact.out : q.Prime).two_le
    have hq23 : q = 2 ∨ q = 3 := by omega
    rcases hq23 with rfl | rfl
    · exact Or.inl (by exact_mod_cast CharP.cast_eq_zero k 2)
    · exact Or.inr (by exact_mod_cast CharP.cast_eq_zero k 3)
  exact ord_eq_one_of_eq_full k N hNK h23 (modularFunctionFieldC k N) hCF
    (jqModC_mem k N) v (v.evalAt (jGeomGen k N)) h0 h1728 hne hpos

end S_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three
end P2MW
export P2MW.S_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three (solution)
