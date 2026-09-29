-- Prove2me | solution 1 for ModularCurve.exists_inLineMulPoly_eq_C_mul_of_toPoint_eq_zsmul_of_eval_prePsi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1ef88d67-e86a-57aa-a3ba-36badd0a1e09

import Mathlib
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_evalEval_phi
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_inLineMulPoly_eq_C_mul_of_toPoint_eq_zsmul_of_eval_prePsi_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve Polynomial

namespace LinkDiamond

variable {T : Type} [Field T] [DecidableEq T] (W : WeierstrassCurve T)

theorem xmul [W.IsElliptic] {m : ℤ} {x₀ y₀ : T} (h₀ : W.toAffine.Nonsingular x₀ y₀) {x₁ y₁ : T}
    (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (hm : m • WeierstrassCurve.Affine.Point.some x₀ y₀ h₀ = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) :
    (W.ΨSq m).eval x₀ ≠ 0 ∧ x₁ * (W.ΨSq m).eval x₀ = (W.Φ m).eval x₀ := by
  have key := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq W m h₀ h₁ hm
  rw [WeierstrassCurve.Affine.evalEval_psi_sq W h₀.left m, WeierstrassCurve.Affine.evalEval_phi W h₀.left m] at key
  refine ⟨fun h0 => ?_, key⟩
  have hΦ : (W.Φ m).eval x₀ = 0 := by rw [← key, h0, mul_zero]
  obtain ⟨u, v, huv⟩ := WeierstrassCurve.isCoprime_Phi_PsiSq W m
  have := congrArg (Polynomial.eval x₀) huv
  rw [eval_add, eval_mul, eval_mul, hΦ, h0, mul_zero, mul_zero, add_zero, eval_one] at this
  exact zero_ne_one this

def fold (ℓ r : ℕ) : ℕ := if r ≤ (ℓ - 1) / 2 then r else ℓ - r

theorem fold_mem {ℓ r : ℕ} (hℓ : Odd ℓ) (hr : r < ℓ) (hr0 : r ≠ 0) : fold ℓ r ∈ Finset.Icc 1 ((ℓ - 1) / 2) := by
  unfold fold
  obtain ⟨k, rfl⟩ := hℓ
  have hk : (2 * k + 1 - 1) / 2 = k := by omega
  rw [hk, Finset.mem_Icc]
  split_ifs with h
  · omega
  · omega

theorem fold_cast {ℓ r : ℕ} (hr : r < ℓ) :
    ((fold ℓ r : ℕ) : ZMod ℓ) = (r : ZMod ℓ) ∨ ((fold ℓ r : ℕ) : ZMod ℓ) = -(r : ZMod ℓ) := by
  unfold fold
  split_ifs with h
  · exact Or.inl rfl
  · right
    rw [Nat.cast_sub hr.le, ZMod.natCast_self, zero_sub]

section PM
variable {R : Type} [Ring R]

theorem pm_symm {u v : R} (h : u = v ∨ u = -v) : v = u ∨ v = -u := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (neg_neg v).symm

theorem pm_trans {u v w : R} (h1 : u = v ∨ u = -v) (h2 : v = w ∨ v = -w) : u = w ∨ u = -w := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (neg_neg w)

end PM

theorem pm_cancel {F : Type} [Field F] {a u v : F} (ha : a ≠ 0) (h : a * u = a * v ∨ a * u = -(a * v)) :
    u = v ∨ u = -v := by
  rcases h with h | h
  · exact Or.inl (mul_left_cancel₀ ha h)
  · rw [← mul_neg] at h
    exact Or.inr (mul_left_cancel₀ ha h)

end LinkDiamond

open LinkDiamond in
theorem solution
    (T : Type) [Field T] [DecidableEq T] (W : WeierstrassCurve T)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓT : ((ℓ : ℕ) : T) ≠ 0) (hΔ : W.Δ ≠ 0)
    (x y : T) (hxy : W.toAffine.Equation x y) (hx : (W.preΨ ℓ).eval x = 0)
    (a : ℤ) (ha : ¬ ((ℓ : ℤ) ∣ a))
    (x' y' : T) (hxy' : W.toAffine.Equation x' y')
    (hP : ModularCurve.LevelRelabelling.toPoint (W.baseChange T) x' y' =
      a • ModularCurve.LevelRelabelling.toPoint (W.baseChange T) x y)
    (n : ℕ) :
    ∃ u : T, u ≠ 0 ∧ ModularCurve.inLineMulPoly W ℓ n x' = Polynomial.C u * ModularCurve.inLineMulPoly W ℓ n x := by
  classical
  haveI hE : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hℓp : ℓ.Prime := Fact.out
  have hodd : Odd ℓ := hℓp.odd_of_ne_two hℓ2
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩

  have hns : W.toAffine.Nonsingular x y := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hxy
  have hns' : W.toAffine.Nonsingular x' y' := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hxy'
  have hbc : W.baseChange T = W := by
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hbc] at hP
  have hPt : ModularCurve.LevelRelabelling.toPoint W x y = WeierstrassCurve.Affine.Point.some x y hns := by
    unfold ModularCurve.LevelRelabelling.toPoint; rw [dif_pos hns]
  have hPt' : ModularCurve.LevelRelabelling.toPoint W x' y' = WeierstrassCurve.Affine.Point.some x' y' hns' := by
    unfold ModularCurve.LevelRelabelling.toPoint; rw [dif_pos hns']
  rw [hPt, hPt'] at hP

  set P : W.toAffine.Point := WeierstrassCurve.Affine.Point.some x y hns with hPdef

  have hℓP : (ℓ : ℤ) • P = 0 := by
    rw [natCast_zsmul, hPdef]
    refine (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W hodd hns).mpr ?_
    have : W.preΨ (ℓ : ℕ) = W.preΨ' ℓ := WeierstrassCurve.preΨ_ofNat W ℓ
    rw [← this]; exact hx
  have hP0 : P ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hns
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓp
  have hiff : ∀ m : ℤ, m • P = 0 ↔ (ℓ : ℤ) ∣ m := by
    intro m
    constructor
    · intro hm
      by_contra hdvd
      have hcopN : Nat.Coprime ℓ m.natAbs :=
        (Nat.Prime.coprime_iff_not_dvd hℓp).mpr (fun h => hdvd (Int.natCast_dvd.mpr h))
      have hcop : IsCoprime (ℓ : ℤ) m := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]; exact hcopN
      obtain ⟨u, v, huv⟩ := hcop
      apply hP0
      calc P = (1 : ℤ) • P := (one_zsmul P).symm
        _ = (u * ℓ + v * m) • P := by rw [huv]
        _ = u • ((ℓ : ℤ) • P) + v • (m • P) := by rw [add_zsmul, mul_zsmul, mul_zsmul]
        _ = 0 := by rw [hℓP, hm, zsmul_zero, zsmul_zero, add_zero]
    · rintro ⟨k, rfl⟩
      rw [mul_comm, mul_zsmul, hℓP, zsmul_zero]

  set I : Finset ℕ := Finset.Icc 1 ((ℓ - 1) / 2) with hI
  set A : ZMod ℓ := ((a : ℤ) : ZMod ℓ) with hA
  have hA0 : A ≠ 0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a ℓ).mp h)
  let r : ℕ → ℕ := fun b => (A * (b : ZMod ℓ)).val
  let σ : ℕ → ℕ := fun b => fold ℓ (r b)
  have hr_lt : ∀ b, r b < ℓ := fun b => ZMod.val_lt _
  have hr_cast : ∀ b, ((r b : ℕ) : ZMod ℓ) = A * (b : ZMod ℓ) := fun b => ZMod.natCast_zmod_val _
  have hmemI : ∀ b ∈ I, 1 ≤ b ∧ b ≤ (ℓ - 1) / 2 := fun b hb => Finset.mem_Icc.mp hb
  have hl2 : 2 * ((ℓ - 1) / 2) < ℓ := by obtain ⟨k, hk⟩ := hodd; omega
  have hb0 : ∀ b ∈ I, (b : ZMod ℓ) ≠ 0 := by
    intro b hb h
    obtain ⟨h1, h2⟩ := hmemI b hb
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hr0 : ∀ b ∈ I, r b ≠ 0 := by
    intro b hb h0
    have : A * (b : ZMod ℓ) = 0 := by rw [← hr_cast b, h0, Nat.cast_zero]
    rcases mul_eq_zero.mp this with h | h
    · exact hA0 h
    · exact hb0 b hb h
  have hσmem : ∀ b ∈ I, σ b ∈ I := fun b hb => fold_mem hodd (hr_lt b) (hr0 b hb)
  have hσcast : ∀ b, ((σ b : ℕ) : ZMod ℓ) = A * (b : ZMod ℓ) ∨ ((σ b : ℕ) : ZMod ℓ) = -(A * (b : ZMod ℓ)) := by
    intro b
    rcases fold_cast (ℓ := ℓ) (hr_lt b) with h | h
    · left; rw [show σ b = fold ℓ (r b) from rfl, h, hr_cast]
    · right; rw [show σ b = fold ℓ (r b) from rfl, h, hr_cast]

  have hsmall : ∀ b₁ ∈ I, ∀ b₂ ∈ I, ((b₁ : ZMod ℓ) = (b₂ : ZMod ℓ) ∨ (b₁ : ZMod ℓ) = -(b₂ : ZMod ℓ)) → b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ h
    obtain ⟨h11, h12⟩ := hmemI b₁ hb₁
    obtain ⟨h21, h22⟩ := hmemI b₂ hb₂
    rcases h with h | h
    · have : (((b₁ : ℤ) - (b₂ : ℤ) : ℤ) : ZMod ℓ) = 0 := by push_cast; rw [h, sub_self]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      have habs := Int.eq_zero_of_abs_lt_dvd this (by rw [abs_lt]; constructor <;> push_cast <;> omega)
      omega
    · have : (((b₁ : ℤ) + (b₂ : ℤ) : ℤ) : ZMod ℓ) = 0 := by push_cast; rw [h, neg_add_cancel]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      have habs := Int.eq_zero_of_abs_lt_dvd this (by rw [abs_lt]; constructor <;> push_cast <;> omega)
      omega
  have hinj : Set.InjOn σ (I : Set ℕ) := by
    intro b₁ hb₁ b₂ hb₂ hσ
    have hb₁' : b₁ ∈ I := hb₁
    have hb₂' : b₂ ∈ I := hb₂
    apply hsmall b₁ hb₁' b₂ hb₂'
    apply pm_cancel hA0
    have e : ((σ b₁ : ℕ) : ZMod ℓ) = ((σ b₂ : ℕ) : ZMod ℓ) := by rw [hσ]
    have h1 := pm_symm (hσcast b₁)
    rw [e] at h1
    exact pm_trans h1 (hσcast b₂)
  have hsurj : Set.SurjOn σ (I : Set ℕ) (I : Set ℕ) :=
    Finset.surjOn_of_injOn_of_card_le σ (fun b hb => hσmem b hb) hinj le_rfl

  let F : T → ℕ → T[X] := fun x₀ m => W.Φ n * C ((W.ΨSq m).eval x₀) - C ((W.Φ m).eval x₀) * W.ΨSq n
  have hprod : ∀ x₀ : T, ModularCurve.inLineMulPoly W ℓ n x₀ = ∏ b ∈ I, F x₀ b := fun x₀ => rfl

  have hfac : ∀ b ∈ I, (W.ΨSq (σ b : ℕ)).eval x ≠ 0 ∧ (W.ΨSq (b : ℕ)).eval x' ≠ 0 ∧
      F x' b = C ((W.ΨSq (b : ℕ)).eval x' / (W.ΨSq (σ b : ℕ)).eval x) * F x (σ b) := by
    intro b hb
    have hb' := hσmem b hb
    obtain ⟨hb1, hb2⟩ := hmemI b hb

    have hσP : ((σ b : ℕ) : ℤ) • P ≠ 0 := by
      intro h0
      have := (hiff _).mp h0
      obtain ⟨h1, h2⟩ := hmemI _ hb'
      have := Int.le_of_dvd (by exact_mod_cast h1) this
      omega

    have hab : (((b : ℕ) : ℤ) * a) • P = ((σ b : ℕ) : ℤ) • P ∨ (((b : ℕ) : ℤ) * a) • P = -(((σ b : ℕ) : ℤ) • P) := by
      rcases hσcast b with h | h
      · left
        have hz : ((((b : ℕ) : ℤ) * a - ((σ b : ℕ) : ℤ) : ℤ) : ZMod ℓ) = 0 := by
          push_cast; rw [h, hA]; push_cast; ring
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
        have h0 := (hiff _).mpr hz
        have e : (((b : ℕ) : ℤ) * a) • P = ((((b : ℕ) : ℤ) * a - ((σ b : ℕ) : ℤ)) + ((σ b : ℕ) : ℤ)) • P := by
          rw [sub_add_cancel]
        rw [add_zsmul, h0, zero_add] at e
        exact e
      · right
        have hz : ((((b : ℕ) : ℤ) * a + ((σ b : ℕ) : ℤ) : ℤ) : ZMod ℓ) = 0 := by
          push_cast; rw [h, hA]; push_cast; ring
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
        have h0 := (hiff _).mpr hz
        have e : (((b : ℕ) : ℤ) * a) • P = ((((b : ℕ) : ℤ) * a + ((σ b : ℕ) : ℤ)) - ((σ b : ℕ) : ℤ)) • P := by
          rw [add_sub_cancel_right]
        rw [sub_zsmul, h0, zero_add] at e
        exact e

    obtain ⟨xb, yb, hbns, hQ⟩ : ∃ (xb yb : T) (hbns : W.toAffine.Nonsingular xb yb),
        ((σ b : ℕ) : ℤ) • P = WeierstrassCurve.Affine.Point.some xb yb hbns := by
      cases hQ : ((σ b : ℕ) : ℤ) • P with
      | zero => exact absurd hQ hσP
      | some xb yb hbns => exact ⟨xb, yb, hbns, rfl⟩

    obtain ⟨hΨx, hxb⟩ := xmul W hns hbns (by rw [← hPdef]; exact hQ)

    obtain ⟨yb', hbns', hQ'⟩ : ∃ (yb' : T) (hbns' : W.toAffine.Nonsingular xb yb'),
        ((b : ℕ) : ℤ) • WeierstrassCurve.Affine.Point.some x' y' hns' = WeierstrassCurve.Affine.Point.some xb yb' hbns' := by
      rw [hP, ← mul_zsmul]
      rcases hab with h | h
      · exact ⟨yb, hbns, h.trans hQ⟩
      · refine ⟨W.toAffine.negY xb yb, (by rw [WeierstrassCurve.Affine.nonsingular_neg]; exact hbns), ?_⟩
        rw [h, hQ, WeierstrassCurve.Affine.Point.neg_some]
    obtain ⟨hΨx', hxb'⟩ := xmul W hns' hbns' hQ'
    refine ⟨hΨx, hΨx', ?_⟩

    have hcross : (W.Φ (b : ℕ)).eval x' * (W.ΨSq (σ b : ℕ)).eval x = (W.Φ (σ b : ℕ)).eval x * (W.ΨSq (b : ℕ)).eval x' := by
      rw [← hxb, ← hxb']; ring
    set c : T := (W.ΨSq (b : ℕ)).eval x' / (W.ΨSq (σ b : ℕ)).eval x with hc
    have hc1 : c * (W.ΨSq (σ b : ℕ)).eval x = (W.ΨSq (b : ℕ)).eval x' := by
      rw [hc]; field_simp
    have hc2 : c * (W.Φ (σ b : ℕ)).eval x = (W.Φ (b : ℕ)).eval x' := by
      rw [hc, div_mul_eq_mul_div, div_eq_iff hΨx]
      linear_combination hcross.symm
    show W.Φ n * C ((W.ΨSq (b : ℕ)).eval x') - C ((W.Φ (b : ℕ)).eval x') * W.ΨSq n =
      C c * (W.Φ n * C ((W.ΨSq (σ b : ℕ)).eval x) - C ((W.Φ (σ b : ℕ)).eval x) * W.ΨSq n)
    rw [← hc1, ← hc2, C_mul, C_mul]
    ring

  refine ⟨∏ b ∈ I, (W.ΨSq (b : ℕ)).eval x' / (W.ΨSq (σ b : ℕ)).eval x, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro b hb
    obtain ⟨h1, h2, -⟩ := hfac b hb
    exact div_ne_zero h2 h1
  · rw [hprod, hprod, Finset.prod_congr rfl (fun b hb => (hfac b hb).2.2), Finset.prod_mul_distrib, ← map_prod C]
    have hperm : ∏ b ∈ I, F x (σ b) = ∏ b ∈ I, F x b :=
      Finset.prod_nbij σ hσmem hinj hsurj (fun b hb => rfl)
    rw [hperm]

end S_ModularCurve_exists_inLineMulPoly_eq_C_mul_of_toPoint_eq_zsmul_of_eval_prePsi_eq_zero
end P2MW
export P2MW.S_ModularCurve_exists_inLineMulPoly_eq_C_mul_of_toPoint_eq_zsmul_of_eval_prePsi_eq_zero (solution)
