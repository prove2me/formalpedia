-- Prove2me | solution 1 for GlobalTheory.quadratic_refinement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:21.360548+00:00
-- url     : https://prove2.me/submissions/26900cb4-f8ea-406a-bb7d-96a680283d2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsHomDivMulRefine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
namespace QuadRefinement
section Additive
variable {O Y M : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y]
  [AddCommGroup M]
variable {τ : Y →+ Y →+ M} {w : O}
end Additive
section Multiplicative
variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A]
variable {τ : Y →+ Y →+ Additive A} {w : O}
end Multiplicative
section HalfElement
variable {K : Type*} [Field K] [CharZero K] [StarRing K] {d : ℤ} {s : K}
end HalfElement
section Example
open QuadraticAlgebra
end Example
end QuadRefinement
variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_smul_add_apply_smul_eq_of_add_star_eq_one (hsymm : ∀ y y', τ y y' = τ y' y)
    (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) (hw : w + star w = 1) (y y' : Y) :
    τ y (w • y') + τ y' (w • y) = τ y y' := by
  rw [hsymm y' (w • y), hadj, ← (τ y).map_add, ← add_smul, hw, one_smul]
variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_add_smul_add_eq_add_add (hsymm : ∀ y y', τ y y' = τ y' y)
    (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) (hw : w + star w = 1) (y y' : Y) :
    τ (y + y') (w • (y + y')) = τ y (w • y) + τ y' (w • y') + τ y y' := by
  rw [← apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw y y']
  simp only [smul_add, map_add, AddMonoidHom.add_apply]
  abel
variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_neg_smul_neg_eq (y : Y) : τ (-y) (w • -y) = τ y (w • y) := by
  simp
variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_smul_smul_smul_eq_zsmul_of_mul_star_eq (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y'))
    (a : O) (n : ℤ) (h : a * star a = n) (y : Y) :
    τ (a • y) (w • a • y) = n • τ y (w • y) := by
  have e : star a * w * a = (n : O) * w := by rw [← h]; ring
  rw [hadj, smul_smul, smul_smul, e, mul_smul, Int.cast_smul_eq_zsmul, map_zsmul]
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ {O Y A : Type} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A]
      (τ : Y →+ Y →+ Additive A) (w : O), (∀ y y', τ y y' = τ y' y) →
      (∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) → w + star w = 1 →
      (∀ y y', _root_.GlobalTheory.QuadRefinement.mulRefine τ w (y + y') =
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w y *
          _root_.GlobalTheory.QuadRefinement.mulRefine τ w y' * (τ y y').toMul) ∧
      (∀ y, _root_.GlobalTheory.QuadRefinement.mulRefine τ w (-y) =
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w y) ∧
      (∀ y, _root_.GlobalTheory.QuadRefinement.mulRefine τ w y ^ 2 = (τ y y).toMul) ∧
      (∀ (a : O) (n : ℤ), a * star a = n → ∀ y,
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w (a • y) =
          _root_.GlobalTheory.QuadRefinement.mulRefine τ w y ^ n) ∧
      (∀ ψ : Y → A, (∀ y y', ψ (y + y') = ψ y * ψ y' * (τ y y').toMul) → (∀ y, ψ (-y) = ψ y) →
        (∃ α : Multiplicative Y →* A,
          (∀ y, α (Multiplicative.ofAdd y) = ψ y / _root_.GlobalTheory.QuadRefinement.mulRefine τ w y)
            ∧ α ^ 2 = 1) ∧
        ∀ n : ℤ, w * star w = n → (∀ y, ψ (w • y) = ψ y ^ n) →
          (∀ y, ψ (star w • y) = ψ y ^ n) → ψ = _root_.GlobalTheory.QuadRefinement.mulRefine τ w) ∧
      (∀ (v : Additive A →+ ℚ) y,
        2 * v (Additive.ofMul (_root_.GlobalTheory.QuadRefinement.mulRefine τ w y)) =
          τ.compr₂ v y y)) ∧
    (∀ {K : Type} [Field K] [CharZero K] [StarRing K] (d : ℤ) (s : K), d % 8 = 7 →
      s ^ 2 = -(d : K) → star s = -s →
      IsIntegral ℤ ((1 + s) / 2) ∧ (1 + s) / 2 + star ((1 + s) / 2) = 1 ∧
      (1 + s) / 2 * star ((1 + s) / 2) = (((1 + d) / 4 : ℤ) : K) ∧
      4 * ((1 + d) / 4) = 1 + d ∧ Even ((1 + d) / 4)) := by
  refine ⟨?_, ?_⟩
  · intro O Y A _ _ _ _ _ τ w hsymm hadj hw
    set m := _root_.GlobalTheory.QuadRefinement.mulRefine τ w with hmdef
    have hm : ∀ y, m y = (τ y (w • y)).toMul := fun _ => rfl
    have hadd : ∀ y y', m (y + y') = m y * m y' * (τ y y').toMul := by
      intro y y'
      simp only [hm, apply_add_smul_add_eq_add_add hsymm hadj hw, toMul_add]
    have hneg : ∀ y, m (-y) = m y := by
      intro y
      simp only [hm, apply_neg_smul_neg_eq]
    have hsq : ∀ y, m y ^ 2 = (τ y y).toMul := by
      intro y
      rw [hm, ← toMul_nsmul, two_nsmul, apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw]
    have hpow : ∀ (a : O) (n : ℤ), a * star a = n → ∀ y, m (a • y) = m y ^ n := by
      intro a n h y
      rw [hm, hm, apply_smul_smul_smul_eq_zsmul_of_mul_star_eq hadj a n h, toMul_zsmul]
    refine ⟨hadd, hneg, hsq, hpow, ?_, ?_⟩
    · intro ψ hψ heven
      have h0 : ψ 0 = 1 := by
        have := hψ 0 0
        simpa using this
      have hψsq : ∀ y, ψ y ^ 2 = (τ y y).toMul := by
        intro y
        have h := hψ y (-y)
        rw [add_neg_cancel, h0, heven, map_neg, toMul_neg, eq_comm, mul_inv_eq_one] at h
        rw [sq, h]
      have hb : ∀ y y', ψ (y + y') / m (y + y') = ψ y / m y * (ψ y' / m y') := by
        intro y y'
        rw [hψ, hadd, mul_div_mul_right_eq_div, div_mul_div_comm]
      have hbsq : ∀ y, (ψ y / m y) ^ 2 = 1 := by
        intro y
        rw [div_pow, hψsq, hsq, div_self']
      let β : Multiplicative Y →* A :=
        MonoidHom.mk' (fun y => ψ y.toAdd / m y.toAdd) (fun y y' => by
          simp only [toAdd_mul]
          exact hb _ _)
      refine ⟨⟨β, fun y => rfl, ?_⟩, ?_⟩
      · ext y
        show β y ^ 2 = 1
        exact hbsq (Multiplicative.toAdd y)
      · intro n hn h1 h2
        funext y
        have hw1 : ψ (w • y) / m (w • y) = (ψ y / m y) ^ n := by
          rw [h1, hpow w n hn, div_zpow]
        have hw2 : ψ (star w • y) / m (star w • y) = (ψ y / m y) ^ n := by
          rw [h2, hpow (star w) n (by rw [star_star, mul_comm, hn]), div_zpow]
        have e : w • y + star w • y = y := by rw [← add_smul, hw, one_smul]
        have key : ψ y / m y = 1 := by
          calc ψ y / m y = ψ (w • y + star w • y) / m (w • y + star w • y) := by rw [e]
            _ = ((ψ y / m y) ^ 2) ^ n := by rw [hb, hw1, hw2, ← mul_zpow, ← sq]
            _ = 1 := by rw [hbsq, one_zpow]
        exact div_eq_one.mp key
    · intro v y
      rw [hm, ofMul_toMul, AddMonoidHom.compr₂_apply, ← apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw y y,
        map_add, two_mul]
  · intro K _ _ _ d s hd hs hstar
    obtain ⟨k, rfl⟩ : ∃ k, d = 8 * k + 7 := ⟨d / 8, by omega⟩
    have hq : (1 + (8 * k + 7)) / 4 = 2 * k + 2 := by omega
    rw [hq]
    push_cast at hs
    have hst : star ((1 + s) / 2) = (1 - s) / 2 := by
      rw [div_eq_mul_inv, star_mul', star_inv₀, star_add, star_one, hstar, star_ofNat]
      ring
    refine ⟨?_, ?_, ?_, by omega, ⟨k + 1, by ring⟩⟩
    · refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k + 2 : ℤ)), ?_, ?_⟩
      · monicity!
      · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
        rw [algebraMap_int_eq, eq_intCast]
        push_cast
        linear_combination (1 / 4 : K) * hs
    · rw [hst]; ring
    · rw [hst]; push_cast; linear_combination (-1 / 4 : K) * hs
end _root_.GlobalTheory
end GlobalTheory
