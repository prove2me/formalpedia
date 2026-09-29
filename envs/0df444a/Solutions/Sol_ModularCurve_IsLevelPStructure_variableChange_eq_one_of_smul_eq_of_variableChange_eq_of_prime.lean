-- Prove2me | solution 1 for ModularCurve.IsLevelPStructure.variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/f89f5730-890f-51ae-8349-7d0ea63a371f

import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsLevelPStructure_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_IsLevelPStructure_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "indepElt LevelPData LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ IsLevelPStructure LevelPData.yQ LevelPData.xP LevelPData.yP LevelPData.xQ"
namespace RigidLevel
p2m_open "ModularCurve"

open WeierstrassCurve

variable {T : Type*} [CommRing T]

theorem isUnit_sub_of_isUnit_indepElt (W : WeierstrassCurve T) {ℓ : ℕ} (hℓ3 : 3 ≤ ℓ) {x₀ x : T}
    (h : IsUnit (indepElt W ℓ x₀ x)) : IsUnit (x - x₀) := by
  unfold indepElt at h
  have h1 : 1 ∈ Finset.Icc 1 ((ℓ - 1) / 2) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  rw [← Finset.mul_prod_erase _ _ h1] at h
  have h' := isUnit_of_mul_isUnit_left h
  simpa [WeierstrassCurve.ΨSq_one, WeierstrassCurve.Φ_one] using h'

theorem variableChange_eq_one_of_isUnit_psi2 (ℓ : ℕ) (hℓ3 : 3 ≤ ℓ)
    (W : WeierstrassCurve T) (D : LevelPData T) (hD : IsLevelPStructure W ℓ D)
    (C : WeierstrassCurve.VariableChange T) (hCW : C • W = W) (hCD : D.variableChange C = D)
    (hψ : IsUnit (2 * D.yP + W.a₁ * D.xP + W.a₃)) :
    C = 1 := by
  obtain ⟨u, r, s, t⟩ := C

  set v : T := ((u⁻¹ : Tˣ) : T) with hv
  have hxP : v ^ 2 * (D.xP - r) = D.xP := by
    have := congrArg LevelPData.xP hCD
    simpa [LevelPData.variableChange_xP] using this
  have hxQ : v ^ 2 * (D.xQ - r) = D.xQ := by
    have := congrArg LevelPData.xQ hCD
    simpa [LevelPData.variableChange_xQ] using this
  have hyP : v ^ 3 * (D.yP - s * (D.xP - r) - t) = D.yP := by
    have := congrArg LevelPData.yP hCD
    simpa [LevelPData.variableChange_yP] using this
  have hyQ : v ^ 3 * (D.yQ - s * (D.xQ - r) - t) = D.yQ := by
    have := congrArg LevelPData.yQ hCD
    simpa [LevelPData.variableChange_yQ] using this
  have ha1 : v * (W.a₁ + 2 * s) = W.a₁ := by
    have := congrArg WeierstrassCurve.a₁ hCW
    simpa [WeierstrassCurve.variableChange_a₁] using this
  have ha3 : v ^ 3 * (W.a₃ + r * W.a₁ + 2 * t) = W.a₃ := by
    have := congrArg WeierstrassCurve.a₃ hCW
    simpa [WeierstrassCurve.variableChange_a₃] using this

  have hxu : IsUnit (D.xP - D.xQ) := by
    have := isUnit_sub_of_isUnit_indepElt W hℓ3 hD.isUnit_indepElt_QP
    exact this

  have hv2 : v ^ 2 = 1 := by
    have h0 : (v ^ 2 - 1) * (D.xP - D.xQ) = 0 := by linear_combination hxP - hxQ
    have := (hxu.mul_left_eq_zero).mp h0
    linear_combination this
  have hr : r = 0 := by linear_combination (-1 : T) * hxP + (D.xP - r) * hv2
  have hv3 : v ^ 3 = v := by linear_combination v * hv2

  have hkey : (v - 1) * (2 * D.yP + W.a₁ * D.xP + W.a₃) = 0 := by
    linear_combination (2 : T) * hyP + D.xP * ha1 + ha3
      - (2 * v * (D.yP - s * (D.xP - r) - t) + v * (W.a₃ + r * W.a₁ + 2 * t)) * hv2
      - (2 * v * s + v * W.a₁) * hr
  have hv1 : v = 1 := by
    have := (hψ.mul_left_eq_zero).mp hkey
    linear_combination this

  have hsP : s * D.xP + t = 0 := by
    linear_combination (-1 : T) * hyP + (D.yP - s * (D.xP - r) - t) * (v ^ 2 + v + 1) * hv1 + s * hr
  have hsQ : s * D.xQ + t = 0 := by
    linear_combination (-1 : T) * hyQ + (D.yQ - s * (D.xQ - r) - t) * (v ^ 2 + v + 1) * hv1 + s * hr
  have hs : s = 0 := by
    have h0 : s * (D.xP - D.xQ) = 0 := by linear_combination hsP - hsQ
    exact (hxu.mul_left_eq_zero).mp h0
  have ht : t = 0 := by linear_combination hsP - D.xP * hs
  have hu : u = 1 := by
    have : (u⁻¹ : Tˣ) = 1 := Units.ext (by rw [Units.val_one]; exact hv ▸ hv1)
    simpa using this
  rw [WeierstrassCurve.VariableChange.one_def, hu, hr, hs, ht]

end ModularCurve.RigidLevel

namespace ModularCurve
p2m_export "ModularCurve" "indepElt LevelPData LevelPData.variableChange_xP LevelPData.variableChange_yP LevelPData.variableChange_xQ LevelPData.variableChange_yQ IsLevelPStructure LevelPData.yQ LevelPData.xP LevelPData.yP LevelPData.xQ"
namespace RigidLevel
p2m_open "ModularCurve"

open WeierstrassCurve

variable {T : Type*} [CommRing T]

theorem psi2_ne_zero_field {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    {ℓ : ℕ} (hℓ : Odd ℓ) {x y : k} (heq : W.toAffine.Equation x y) (hψ : (W.preΨ' ℓ).eval x = 0) :
    2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
  intro h0
  have hns : W.toAffine.Nonsingular x y := W.toAffine.equation_iff_nonsingular.mp heq
  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y hns with hP
  have hℓP : ℓ • P = 0 :=
    (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hℓ hns).mpr hψ
  have hneg : -P = P := by
    rw [hP, WeierstrassCurve.Affine.Point.neg_some]
    congr 1
    show -y - W.a₁ * x - W.a₃ = y
    linear_combination (-1 : k) * h0
  have h2P : 2 • P = 0 := by
    rw [two_nsmul]
    nth_rewrite 2 [← hneg]
    exact add_neg_cancel P
  have hd : addOrderOf P ∣ Nat.gcd ℓ 2 :=
    Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hℓP) (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2P)
  have hg : Nat.gcd ℓ 2 = 1 := Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hℓ)
  rw [hg, Nat.dvd_one] at hd
  exact WeierstrassCurve.Affine.Point.some_ne_zero hns (AddMonoid.addOrderOf_eq_one_iff.mp hd)

theorem isUnit_psi2 {ℓ : ℕ} (hℓ : Odd ℓ) (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    {x y : T} (heq : W.toAffine.Equation x y) (hψ : (W.preΨ ℓ).eval x = 0) :
    IsUnit (2 * y + W.a₁ * x + W.a₃) := by
  classical
  by_contra hnu
  have hne : Ideal.span ({2 * y + W.a₁ * x + W.a₃} : Set T) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hnu
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : 2 * y + W.a₁ * x + W.a₃ ∈ m := hle (Ideal.mem_span_singleton_self _)
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  set π : T →+* T ⧸ m := Ideal.Quotient.mk m with hπ
  haveI : (W.map π).IsElliptic := by
    refine ⟨?_⟩
    rw [WeierstrassCurve.map_Δ]
    exact hΔ.map π
  have heq' : (W.map π).toAffine.Equation (π x) (π y) := heq.map π
  have hψ' : ((W.map π).preΨ' ℓ).eval (π x) = 0 := by
    rw [← WeierstrassCurve.preΨ_ofNat, WeierstrassCurve.map_preΨ, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, hψ, map_zero]
  have h := psi2_ne_zero_field (W.map π) hℓ heq' hψ'
  apply h
  have : π (2 * y + W.a₁ * x + W.a₃) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simp [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at this
  exact this

end ModularCurve.RigidLevel

theorem solution
    {T : Type*} [CommRing T] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓu : IsUnit ((ℓ : ℕ) : T))
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ)
    (D : LevelPData T) (hD : IsLevelPStructure W ℓ D)
    (C : WeierstrassCurve.VariableChange T) (hCW : C • W = W) (hCD : D.variableChange C = D) :
    C = 1 :=
  ModularCurve.RigidLevel.variableChange_eq_one_of_isUnit_psi2 ℓ hℓ3 W D hD C hCW hCD
    (ModularCurve.RigidLevel.isUnit_psi2
      ((Fact.out : ℓ.Prime).odd_of_ne_two (by omega)) W hΔ hD.equation_P hD.preΨ_P)

end S_ModularCurve_IsLevelPStructure_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
end P2MW
export P2MW.S_ModularCurve_IsLevelPStructure_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime (solution)
