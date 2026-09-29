-- Prove2me | solution 1 for ModularCurve.IsLevelPStructure.exists_injective_addMonoidHom_zmod_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/ecb1c89b-186c-5131-b628-9c37ad1c98e0

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IsLevelPStructure_exists_injective_addMonoidHom_zmod_prod
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "WeierstrassCurve~evalEval_ψ_sq~evalEval_φ Polynomial"
open scoped Polynomial.Bivariate

namespace LevelPDict

universe u

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

theorem evalEval_eq_of_mk_eq {x y : F} (hxy : W.toAffine.Equation x y) {A B : F[X][Y]}
    (h : Affine.CoordinateRing.mk W.toAffine A = Affine.CoordinateRing.mk W.toAffine B) :
    A.evalEval x y = B.evalEval x y := by
  rw [Affine.CoordinateRing.mk, AdjoinRoot.mk_eq_mk] at h
  obtain ⟨q, hq⟩ := h
  have h0 : (A - B).evalEval x y = 0 := by
    rw [hq, ← coe_evalEvalRingHom, map_mul, coe_evalEvalRingHom]
    rw [WeierstrassCurve.Affine.Equation] at hxy
    rw [hxy, zero_mul]
  rw [← coe_evalEvalRingHom, map_sub, sub_eq_zero] at h0
  exact h0

theorem evalEval_ψ_sq {x y : F} (hxy : W.toAffine.Equation x y) (n : ℤ) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h1 : Affine.CoordinateRing.mk W.toAffine (W.ψ n ^ 2) =
      Affine.CoordinateRing.mk W.toAffine (C (W.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  have := evalEval_eq_of_mk_eq W hxy h1
  rw [← coe_evalEvalRingHom, map_pow, coe_evalEvalRingHom] at this
  rw [this, evalEval_C]

theorem evalEval_φ {x y : F} (hxy : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  rw [evalEval_eq_of_mk_eq W hxy (WeierstrassCurve.Affine.CoordinateRing.mk_φ W n), evalEval_C]

end LevelPDict

open LevelPDict in
universe u in
theorem solution
    {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0)
    {D : ModularCurve.LevelPData F} (hD : ModularCurve.IsLevelPStructure W p D) :
    ∃ f : ZMod p × ZMod p →+ W.toAffine.Point, Function.Injective f := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hpodd : Odd p := hp.odd_of_ne_two hp2

  have hPns : W.toAffine.Nonsingular D.xP D.yP :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).1 hD.equation_P
  have hQns : W.toAffine.Nonsingular D.xQ D.yQ :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).1 hD.equation_Q
  set P : W.toAffine.Point := .some D.xP D.yP hPns with hPdef
  set Q : W.toAffine.Point := .some D.xQ D.yQ hQns with hQdef
  clear_value P Q
  have hpP : (p : ℤ) • P = 0 := by
    rw [natCast_zsmul, hPdef,
      WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hpodd hPns,
      ← WeierstrassCurve.preΨ_ofNat]
    exact hD.preΨ_P
  have hpQ : (p : ℤ) • Q = 0 := by
    rw [natCast_zsmul, hQdef,
      WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hpodd hQns,
      ← WeierstrassCurve.preΨ_ofNat]
    exact hD.preΨ_Q

  have hmodP : ∀ a : ℤ, a • P = (a % p) • P := fun a => by
    conv_lhs => rw [← Int.mul_ediv_add_emod a p]
    rw [add_zsmul, mul_comm, mul_zsmul, hpP, zsmul_zero, zero_add]

  have hindep : ∀ a : ℤ, a • P ≠ Q := by
    intro a ha
    rw [hmodP] at ha
    set a₀ : ℤ := a % p with ha₀
    have ha₀0 : 0 ≤ a₀ := Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero)
    have ha₀p : a₀ < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp.pos)
    have ha₀ne : a₀ ≠ 0 := by
      rintro h; rw [h, zero_zsmul, hQdef] at ha; cases ha

    obtain ⟨c, hc1, hc2, y', hy'ns, hcP⟩ : ∃ c : ℕ, 1 ≤ c ∧ c ≤ (p - 1) / 2 ∧
        ∃ (y' : F) (h' : W.toAffine.Nonsingular D.xQ y'), (c : ℤ) • P = .some D.xQ y' h' := by
      by_cases hle : a₀ ≤ ((p - 1) / 2 : ℕ)
      · refine ⟨a₀.toNat, by omega, by omega, D.yQ, hQns, ?_⟩
        rw [Int.toNat_of_nonneg ha₀0, ha, hQdef]
      · refine ⟨(p - a₀).toNat, by omega, ?_, W.toAffine.negY D.xQ D.yQ,
          (WeierstrassCurve.Affine.nonsingular_neg ..).mpr hQns, ?_⟩
        · have : (p : ℤ) % 2 = 1 := by exact_mod_cast Nat.odd_iff.1 hpodd
          omega
        · have hneg : ((p : ℤ) - a₀) • P = -Q := by rw [sub_zsmul, hpP, ha]; abel
          rw [Int.toNat_of_nonneg (by omega), hneg, hQdef, WeierstrassCurve.Affine.Point.neg_some]

    rw [hPdef] at hcP
    have hx := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq W (c : ℤ) hPns hy'ns hcP
    rw [evalEval_ψ_sq W hD.equation_P, evalEval_φ W hD.equation_P] at hx
    have hzero : ModularCurve.indepElt W p D.xP D.xQ = 0 := by
      unfold ModularCurve.indepElt
      apply Finset.prod_eq_zero (i := c) (Finset.mem_Icc.2 ⟨hc1, hc2⟩)
      rw [hx, sub_self]
    exact not_isUnit_zero (hzero ▸ hD.isUnit_indepElt_PQ)

  let fP : ZMod p →+ W.toAffine.Point :=
    ZMod.lift p ⟨zmultiplesHom W.toAffine.Point P, by simpa using hpP⟩
  let fQ : ZMod p →+ W.toAffine.Point :=
    ZMod.lift p ⟨zmultiplesHom W.toAffine.Point Q, by simpa using hpQ⟩
  have hfP : ∀ z : ℤ, fP (z : ZMod p) = z • P := fun z => by
    simp [fP, ZMod.lift_coe]
  have hfQ : ∀ z : ℤ, fQ (z : ZMod p) = z • Q := fun z => by
    simp [fQ, ZMod.lift_coe]
  refine ⟨fP.coprod fQ, ?_⟩
  rw [injective_iff_map_eq_zero]
  rintro ⟨i, j⟩ hij
  rw [AddMonoidHom.coprod_apply] at hij

  have hj : j = 0 := by
    by_contra hj

    set t : ℤ := ((j⁻¹ : ZMod p).val : ℤ) with ht
    have htZ : (t : ZMod p) = j⁻¹ := by rw [ht, Int.cast_natCast, ZMod.natCast_zmod_val]
    set k : ZMod p := j⁻¹ * i with hk
    have h0 : fP k + fQ 1 = 0 := by
      have := congrArg (fun R => t • R) hij
      simp only [smul_add, smul_zero, ← map_zsmul, zsmul_eq_mul, htZ, inv_mul_cancel₀ hj] at this
      exact this
    have hkZ : ((k.val : ℤ) : ZMod p) = k := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have h1Z : ((1 : ℤ) : ZMod p) = 1 := by simp
    rw [← hkZ, ← h1Z, hfP, hfQ, one_zsmul] at h0
    have hQ : Q = (-(k.val : ℤ)) • P := by
      rw [neg_zsmul]; exact eq_neg_of_add_eq_zero_right h0
    exact hindep _ hQ.symm
  subst hj
  rw [map_zero, add_zero] at hij

  have hi : ((i.val : ℤ) : ZMod p) = i := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hi, hfP] at hij
  have horder : addOrderOf P = p := by
    refine (addOrderOf_eq_prime_iff.2 ⟨?_, ?_⟩)
    · rw [← natCast_zsmul]; exact hpP
    · intro h; rw [hPdef] at h; cases h
  have hdvd : (p : ℤ) ∣ (i.val : ℤ) := by
    have := (addOrderOf_dvd_iff_zsmul_eq_zero).2 hij
    rwa [horder] at this
  have : i = 0 := by
    rw [← hi]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
  subst this
  rfl

end S_ModularCurve_IsLevelPStructure_exists_injective_addMonoidHom_zmod_prod
end P2MW
export P2MW.S_ModularCurve_IsLevelPStructure_exists_injective_addMonoidHom_zmod_prod (solution)
