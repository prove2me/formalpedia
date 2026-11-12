-- Prove2me | solution 1 for IsingVectorBalancing.Subgaussian.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:40:21.678067+00:00
-- url     : https://prove2.me/submissions/f8a1391a-6423-4ff1-a715-46f1f43d8a2c

import Mathlib
import Definitions.Def_IsingVectorBalancing_Subgaussian_Lorentz
import Theorems.Thm_IsingVectorBalancing_Subgaussian_selectionMatrix_isLorentzian

section
set_option autoImplicit false
namespace IsingVectorBalancing.Subgaussian.Dev.T5
open IsingVectorBalancing.Subgaussian Matrix

theorem eig_dot {C : Type*} [Fintype C] [DecidableEq C] {A : Matrix C C ℝ} (hA : A.IsHermitian)
    (i j : C) : (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (⇑(hA.eigenvectorBasis j)) = if i = j then 1 else 0 := by
  have := (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at this
  simpa [dotProduct_comm] using this

theorem quad_eig {C : Type*} [Fintype C] [DecidableEq C] {A : Matrix C C ℝ} (hA : A.IsHermitian)
    (w : C → ℝ) :
    w ⬝ᵥ A.mulVec w = ∑ c, hA.eigenvalues c * (⇑(hA.eigenvectorBasis c) ⬝ᵥ w) ^ 2 := by
  set U : Matrix C C ℝ := (hA.eigenvectorUnitary : Matrix C C ℝ) with hUdef
  have hU : ∀ i c, U i c = hA.eigenvectorBasis c i := by
    intro i c; simp [hUdef, Matrix.IsHermitian.eigenvectorUnitary_apply]
  have hUU : U * Uᵀ = 1 := by
    have := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose, hUdef] using this
  set y : C → ℝ := fun c => ⇑(hA.eigenvectorBasis c) ⬝ᵥ w with hy
  have hw : w = ∑ c, y c • ⇑(hA.eigenvectorBasis c) := by
    have : w = (U * Uᵀ) *ᵥ w := by rw [hUU]; simp
    rw [this, ← Matrix.mulVec_mulVec]
    ext i
    simp [Matrix.mulVec, dotProduct, hU, hy, Finset.sum_apply, mul_comm]
  have hA' : A.mulVec w = ∑ c, (y c * hA.eigenvalues c) • ⇑(hA.eigenvectorBasis c) := by
    conv_lhs => rw [hw]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis, smul_smul]
  conv_lhs => rw [hA', hw]
  simp only [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, eig_dot, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hy]; ring


theorem sym_form {C : Type*} [Fintype C] [DecidableEq C] {A : Matrix C C ℝ} (hA : A.IsHermitian)
    (x z : C → ℝ) : z ⬝ᵥ A.mulVec x = x ⬝ᵥ A.mulVec z := by
  rw [dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose]
  have : Aᵀ = A := by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  rw [this]

theorem key {C : Type*} [Fintype C] [DecidableEq C] {A : Matrix C C ℝ} (hA : A.IsHermitian)
    (hle : (Finset.univ.filter (fun c => 0 < hA.eigenvalues c)).card ≤ 1)
    (x z : C → ℝ) (hx : 0 < x ⬝ᵥ A.mulVec x) (hxz : x ⬝ᵥ A.mulVec z = 0) :
    z ⬝ᵥ A.mulVec z ≤ 0 := by
  by_contra hz
  rw [not_le] at hz
  by_cases hex : ∃ c0, 0 < hA.eigenvalues c0
  · obtain ⟨c0, hc0⟩ := hex
    have huniq : ∀ c, 0 < hA.eigenvalues c → c = c0 := by
      intro c hc
      have := Finset.card_le_one.mp hle c (by simpa using hc) c0 (by simpa using hc0)
      exact this
    set e : C → ℝ := ⇑(hA.eigenvectorBasis c0)
    obtain ⟨a, b, hab, hs⟩ : ∃ a b : ℝ, (0 < a ^ 2 + b ^ 2) ∧
        a * (e ⬝ᵥ x) + b * (e ⬝ᵥ z) = 0 := by
      by_cases hs1 : e ⬝ᵥ x = 0
      · exact ⟨1, 0, by norm_num, by simp [hs1]⟩
      · refine ⟨e ⬝ᵥ z, -(e ⬝ᵥ x), ?_, by ring⟩
        have : 0 < (e ⬝ᵥ x) ^ 2 := by positivity
        nlinarith [sq_nonneg (e ⬝ᵥ z)]
    have hle0 : (a • x + b • z) ⬝ᵥ A.mulVec (a • x + b • z) ≤ 0 := by
      rw [quad_eig hA]
      refine Finset.sum_nonpos fun c _ => ?_
      by_cases hc : 0 < hA.eigenvalues c
      · have : c = c0 := huniq c hc
        subst this
        have h0 : ⇑(hA.eigenvectorBasis c) ⬝ᵥ (a • x + b • z) = 0 := by
          simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]; exact hs
        rw [h0]; simp
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) (sq_nonneg _)
    have hexp : (a • x + b • z) ⬝ᵥ A.mulVec (a • x + b • z) =
        a ^ 2 * (x ⬝ᵥ A.mulVec x) + b ^ 2 * (z ⬝ᵥ A.mulVec z) := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [sym_form hA x z, hxz]
      ring
    rw [hexp] at hle0
    rcases lt_or_ge 0 (a ^ 2) with ha | ha
    · nlinarith [mul_pos ha hx, mul_nonneg (sq_nonneg b) hz.le]
    · have : 0 < b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]
      nlinarith [mul_pos this hz, mul_nonneg (sq_nonneg a) hx.le]
  · have hex' : ∀ c, hA.eigenvalues c ≤ 0 := fun c => not_lt.mp (fun h => hex ⟨c, h⟩)
    have h2 : x ⬝ᵥ A.mulVec x ≤ 0 := by
      rw [quad_eig hA]
      exact Finset.sum_nonpos fun c _ => mul_nonpos_of_nonpos_of_nonneg (hex' c) (sq_nonneg _)
    linarith


noncomputable def Tm {C : Type*} [Fintype C] (m : ℕ) (A : Matrix C C ℝ) (tail : Fin m → C → ℝ)
    (a b : C) (t : Fin m → C) : ℝ :=
  (∏ i, tail i (t i)) * (A a b * (∏ j, A a (t j)) * (∏ j, A b (t j)) *
    ∏ i : Fin m, ∏ j ∈ Finset.univ.filter (fun j : Fin m => i < j), A (t i) (t j))

theorem sum_split {C : Type*} [Fintype C] (m : ℕ) (f : (Fin (m+2) → C) → ℝ) :
    ∑ c, f c = ∑ a, ∑ b, ∑ t : Fin m → C, f (Fin.cons a (Fin.cons b t)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (m+2) => C)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => C)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem expand {C : Type*} [Fintype C] [DecidableEq C] (m : ℕ) (A : Matrix C C ℝ)
    (x y : C → ℝ) (tail : Fin m → C → ℝ) :
    selectionPolynomial A (selections x y tail) =
      ∑ a, ∑ b, x a * y b * ∑ t : Fin m → C, Tm m A tail a b t := by
  unfold selectionPolynomial
  rw [sum_split]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Tm, selections, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.prod_filter]
  have h1 : ∀ x : Fin m, (1 : Fin (m+2)) < x.succ.succ := fun x => by
    simp [Fin.lt_def]
  simp [Fin.succ_pos, Fin.succ_lt_succ_iff, h1]
  ring

end IsingVectorBalancing.Subgaussian.Dev.T5

namespace IsingVectorBalancing.Subgaussian
open IsingVectorBalancing.Subgaussian.Dev.T5 in
theorem chk_theorem_5 {C : Type*} [Fintype C] [DecidableEq C] (m : ℕ)
    (A : Matrix C C ℝ) (hA : IsLorentzian A)
    (x₁ x₂ : C → ℝ) (tail : Fin m → C → ℝ)
    (hx₂ : ∀ c, 0 ≤ x₂ c) (htail : ∀ i c, 0 ≤ tail i c) :
    selectionPolynomial A (selections x₁ x₂ tail) ^ 2 ≥
      selectionPolynomial A (selections x₁ x₁ tail) *
      selectionPolynomial A (selections x₂ x₂ tail) := by
  have hL := selectionMatrix_isLorentzian m A hA tail htail
  set M : Matrix C C ℝ := Matrix.of fun c c' =>
      selectionPolynomial A (selections (Pi.single c 1) (Pi.single c' 1) tail) with hM
  have hMt : ∀ a b, M a b = ∑ t : Fin m → C, Tm m A tail a b t := by
    intro a b
    simp only [hM, Matrix.of_apply]
    rw [expand]
    simp [Pi.single_apply]
  have hP : ∀ x y : C → ℝ, selectionPolynomial A (selections x y tail) = x ⬝ᵥ M.mulVec y := by
    intro x y
    rw [expand]
    simp only [dotProduct, Matrix.mulVec, hMt]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  obtain ⟨hnn, hH, hle⟩ := hL
  rw [hP, hP, hP]
  have hsy := sym_form hH
  have h22 : 0 ≤ x₂ ⬝ᵥ M.mulVec x₂ := by
    refine Finset.sum_nonneg fun a _ => mul_nonneg (hx₂ a) (Finset.sum_nonneg fun b _ => ?_)
    exact mul_nonneg (hnn a b) (hx₂ b)
  rcases h22.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact sq_nonneg _
  · set q := x₂ ⬝ᵥ M.mulVec x₂ with hq
    set p := x₁ ⬝ᵥ M.mulVec x₂ with hp
    set r := p / q with hr
    have hrq : r * q = p := by rw [hr]; field_simp
    have hz := key hH hle x₂ (x₁ - r • x₂) hpos (by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
        smul_eq_mul]
      rw [← hsy x₂ x₁, ← hp, ← hq, hrq]; ring)
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
      sub_dotProduct, smul_dotProduct, smul_eq_mul] at hz
    rw [hsy x₁ x₂, ← hp, ← hq] at hz
    have hz2 : (x₁ ⬝ᵥ M.mulVec x₁ - 2 * r * p + r ^ 2 * q) * q ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hz]) hpos.le
    have : (x₁ ⬝ᵥ M.mulVec x₁ - 2 * r * p + r ^ 2 * q) * q =
        x₁ ⬝ᵥ M.mulVec x₁ * q - p ^ 2 := by
      have : r ^ 2 * q * q = p ^ 2 := by rw [← hrq]; ring
      nlinarith [this, hrq]
    nlinarith [this, hz2]

end IsingVectorBalancing.Subgaussian
end

theorem solution : type_of% @IsingVectorBalancing.Subgaussian.chk_theorem_5 := @IsingVectorBalancing.Subgaussian.chk_theorem_5
