-- Prove2me | solution 1 for MvPolynomial.exists_pair_clearDenominator_deformation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/045bd684-d807-5717-9bec-ff8124daceaa

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RingTheory.Polynomial.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_pair_clearDenominator_deformation

set_option autoImplicit false

open MvPolynomial in

theorem A3H.eval_reverse (D : Polynomial ℂ) (a x y : ℂ) (hy : y ≠ 0) :
    MvPolynomial.eval ![x, y]
        (∑ i ∈ Finset.range (D.natDegree + 1), C (D.coeff i * a ^ i) * X 0 ^ i * X 1 ^ (D.natDegree - i)) =
      y ^ D.natDegree * D.eval (a * x * y⁻¹) := by
  rw [Polynomial.eval_eq_sum_range, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ D.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  rw [show y ^ D.natDegree = y ^ (D.natDegree - i) * y ^ i from by rw [← pow_add, Nat.sub_add_cancel hi'],
    mul_pow, mul_pow, inv_pow]
  field_simp

open MvPolynomial in

theorem A3H.eval_twist (P : MvPolynomial (Fin 3) ℂ) (r b₁ b₂ x y : ℂ) (hy : y ≠ 0) (m : ℕ) (hm : ∀ n ∈ P.support, n 1 ≤ m) :
    MvPolynomial.eval ![x, y]
        (∑ n ∈ P.support, C (P.coeff n * r ^ (n 0) * b₁ ^ (n 1) * b₂ ^ (n 2)) * X 0 ^ (n 0) * X 1 ^ (m - n 1 + n 2)) =
      y ^ m * MvPolynomial.eval ![r * x, b₁ * y⁻¹, b₂ * y] P := by
  conv_rhs => rw [MvPolynomial.eval_eq']
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : n 1 ≤ m := hm n hn
  simp only [map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Fin.prod_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
  rw [show y ^ m = y ^ (m - n 1) * y ^ (n 1) from by rw [← pow_add, Nat.sub_add_cancel hn1], pow_add,
    mul_pow, mul_pow, mul_pow]
  have hyinv : y ^ n 1 * y⁻¹ ^ n 1 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hy, one_pow]
  linear_combination (-(P.coeff n * r ^ n 0 * b₁ ^ n 1 * b₂ ^ n 2 * x ^ n 0 * y ^ (m - n 1) * y ^ n 2)) * hyinv

open MvPolynomial in
theorem solution
    (r b₁ b₂ ω c : ℂ) (hr : r ≠ 0) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hω : ω ≠ 0)
    (P : MvPolynomial (Fin 3) ℂ) (D₁ D₂ : Polynomial ℂ) (e : ℕ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0) :
    ∃ p q : MvPolynomial (Fin 2) ℂ,
      (∀ y : ℂ, y ≠ 0 → ∃ x : ℂ, MvPolynomial.eval ![x, y] q ≠ 0) ∧
      ∀ (x y Z : ℂ), y ≠ 0 →
        Z * (D₁.eval (b₁ * y⁻¹ * (r * x)) * D₁.eval (b₂ * y * (r * x)) * D₂.eval (ω * (r * x) ^ 2) *
            (ω * (r * x) ^ 2) ^ e) =
          c * MvPolynomial.eval ![r * x, b₁ * y⁻¹, b₂ * y] P →
        Z * MvPolynomial.eval ![x, y] q = MvPolynomial.eval ![x, y] p := by
  classical

  set d := D₁.natDegree with hd
  set m := P.support.sup (fun n => n 1) with hm
  have hm' : ∀ n ∈ P.support, n 1 ≤ m := fun n hn => Finset.le_sup (f := fun n => n 1) hn

  let Q₁ : MvPolynomial (Fin 2) ℂ := ∑ i ∈ Finset.range (D₁.natDegree + 1), C (D₁.coeff i * (b₁ * r) ^ i) * X 0 ^ i * X 1 ^ (D₁.natDegree - i)
  let Q₂ : MvPolynomial (Fin 2) ℂ := Polynomial.eval₂ (MvPolynomial.C) (C (b₂ * r) * X 0 * X 1) D₁
  let Q₃ : MvPolynomial (Fin 2) ℂ := Polynomial.eval₂ (MvPolynomial.C) (C (ω * r ^ 2) * X 0 ^ 2) D₂
  let M  : MvPolynomial (Fin 2) ℂ := (C (ω * r ^ 2) * X 0 ^ 2) ^ e
  let Pm : MvPolynomial (Fin 2) ℂ := ∑ n ∈ P.support, C (P.coeff n * r ^ (n 0) * b₁ ^ (n 1) * b₂ ^ (n 2)) * X 0 ^ (n 0) * X 1 ^ (m - n 1 + n 2)

  have hev2 : ∀ (D : Polynomial ℂ) (T : MvPolynomial (Fin 2) ℂ) (x y : ℂ),
      MvPolynomial.eval ![x, y] (Polynomial.eval₂ MvPolynomial.C T D) = D.eval (MvPolynomial.eval ![x, y] T) := by
    intro D T x y
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_eq_eval_map]
    congr 1
    ext i
    simp [Polynomial.coeff_map]
  have hQ₁ : ∀ x y : ℂ, y ≠ 0 → MvPolynomial.eval ![x, y] Q₁ = y ^ d * D₁.eval (b₁ * y⁻¹ * (r * x)) := by
    intro x y hy
    rw [show b₁ * y⁻¹ * (r * x) = b₁ * r * x * y⁻¹ by ring]
    exact A3H.eval_reverse D₁ (b₁ * r) x y hy
  have hQ₂ : ∀ x y : ℂ, MvPolynomial.eval ![x, y] Q₂ = D₁.eval (b₂ * y * (r * x)) := by
    intro x y
    rw [hev2]; congr 1; simp; ring
  have hQ₃ : ∀ x y : ℂ, MvPolynomial.eval ![x, y] Q₃ = D₂.eval (ω * (r * x) ^ 2) := by
    intro x y
    rw [hev2]; congr 1; simp; ring
  have hM : ∀ x y : ℂ, MvPolynomial.eval ![x, y] M = (ω * (r * x) ^ 2) ^ e := by
    intro x y; simp [M]; ring
  have hPm : ∀ x y : ℂ, y ≠ 0 → MvPolynomial.eval ![x, y] Pm = y ^ m * MvPolynomial.eval ![r * x, b₁ * y⁻¹, b₂ * y] P :=
    fun x y hy => A3H.eval_twist P r b₁ b₂ x y hy m hm'
  have hq : ∀ x y : ℂ, y ≠ 0 → MvPolynomial.eval ![x, y] (X 1 ^ m * Q₁ * Q₂ * Q₃ * M) =
      y ^ (m + d) * (D₁.eval (b₁ * y⁻¹ * (r * x)) * D₁.eval (b₂ * y * (r * x)) * D₂.eval (ω * (r * x) ^ 2) *
        (ω * (r * x) ^ 2) ^ e) := by
    intro x y hy
    rw [map_mul, map_mul, map_mul, map_mul, hQ₁ x y hy, hQ₂, hQ₃, hM, map_pow, MvPolynomial.eval_X, pow_add]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
    ring
  have hp : ∀ x y : ℂ, y ≠ 0 → MvPolynomial.eval ![x, y] (C c * X 1 ^ d * Pm) =
      y ^ (m + d) * (c * MvPolynomial.eval ![r * x, b₁ * y⁻¹, b₂ * y] P) := by
    intro x y hy
    rw [map_mul, map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X, hPm x y hy, pow_add]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
    ring
  refine ⟨C c * X 1 ^ d * Pm, X 1 ^ m * Q₁ * Q₂ * Q₃ * M, ?_, ?_⟩
  ·
    intro y hy

    let R : Polynomial ℂ :=
      (D₁.comp (Polynomial.C (b₁ * y⁻¹ * r) * Polynomial.X)) * (D₁.comp (Polynomial.C (b₂ * y * r) * Polynomial.X)) *
        (D₂.comp (Polynomial.C (ω * r ^ 2) * Polynomial.X ^ 2)) * (Polynomial.C (ω * r ^ 2) * Polynomial.X ^ 2) ^ e
    have hD₁0 : D₁ ≠ 0 := fun h => hD₁ (by rw [h, Polynomial.eval_zero])
    have hD₂0 : D₂ ≠ 0 := fun h => hD₂ (by rw [h, Polynomial.eval_zero])
    have hcomp : ∀ (D : Polynomial ℂ) (a : ℂ) (k : ℕ), D ≠ 0 → a ≠ 0 → 0 < k →
        D.comp (Polynomial.C a * Polynomial.X ^ k) ≠ 0 := by
      intro D a k hD ha hk h
      rw [Polynomial.comp_eq_zero_iff] at h
      rcases h with h | ⟨_, h2⟩
      · exact hD h
      · have := congrArg Polynomial.natDegree h2
        rw [Polynomial.natDegree_C_mul_X_pow k a ha, Polynomial.natDegree_C] at this
        omega
    have hR : R ≠ 0 := by
      have h1 : D₁.comp (Polynomial.C (b₁ * y⁻¹ * r) * Polynomial.X) ≠ 0 := by
        simpa using hcomp D₁ (b₁ * y⁻¹ * r) 1 hD₁0 (mul_ne_zero (mul_ne_zero hb₁ (inv_ne_zero hy)) hr) one_pos
      have h2 : D₁.comp (Polynomial.C (b₂ * y * r) * Polynomial.X) ≠ 0 := by
        simpa using hcomp D₁ (b₂ * y * r) 1 hD₁0 (mul_ne_zero (mul_ne_zero hb₂ hy) hr) one_pos
      have h3 : D₂.comp (Polynomial.C (ω * r ^ 2) * Polynomial.X ^ 2) ≠ 0 :=
        hcomp D₂ (ω * r ^ 2) 2 hD₂0 (mul_ne_zero hω (pow_ne_zero _ hr)) two_pos
      have h4 : (Polynomial.C (ω * r ^ 2) * Polynomial.X ^ 2 : Polynomial ℂ) ≠ 0 :=
        mul_ne_zero (Polynomial.C_ne_zero.mpr (mul_ne_zero hω (pow_ne_zero _ hr))) (pow_ne_zero _ Polynomial.X_ne_zero)
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) (pow_ne_zero _ h4)
    obtain ⟨x, hx⟩ : ∃ x : ℂ, R.eval x ≠ 0 := by
      by_contra h
      push Not at h
      exact hR (Polynomial.funext (by simpa using h))
    refine ⟨x, ?_⟩
    rw [hq x y hy]
    have hRe : R.eval x = D₁.eval (b₁ * y⁻¹ * (r * x)) * D₁.eval (b₂ * y * (r * x)) * D₂.eval (ω * (r * x) ^ 2) *
        (ω * (r * x) ^ 2) ^ e := by
      simp [R, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_pow]
      ring
    rw [← hRe]
    exact mul_ne_zero (pow_ne_zero _ hy) hx
  · intro x y Z hy hid
    rw [hq x y hy, hp x y hy, ← hid]
    ring

end S_MvPolynomial_exists_pair_clearDenominator_deformation
end P2MW
export P2MW.S_MvPolynomial_exists_pair_clearDenominator_deformation (solution)
