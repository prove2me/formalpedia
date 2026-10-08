-- Prove2me | solution 1 for HryniewiczCriterion.graphUnitary2_polar_roots
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T16:22:51.128791+00:00
-- url     : https://prove2.me/submissions/3f386b3f-92e3-433d-85bf-f2f10f3e9c71

import Definitions.Def_HryniewiczCriterion_GraphAngle
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

open HryniewiczCriterion
open scoped ContDiff

/-!
# Eigenvalues of the graph unitary of a `2 × 2` symplectic matrix

For `g ∈ SL(2, ℝ)` the unitary `W(Γ_g) W(Δ)⁻¹` equals `D̄⁻¹ • adj(Aᴴ) Aᵀ σ`, where
`A = graphBasis2 g`, `D = det A = (g₀₁ - g₁₀) + i (g₀₀ + g₁₁)` and `σ` swaps the coordinates.
In the polar form `g = R(x) P` its eigenvalues are `e^{i(x ± γ)}` with `cos γ = 2 / tr P`.
-/

namespace HryniewiczCriterion

open Matrix Complex Polynomial

noncomputable section

/-- For a `2 × 2` complex matrix with trace `μ₁ + μ₂` and determinant `μ₁ μ₂`, the roots of the
characteristic polynomial are `μ₁, μ₂`. -/
lemma charpoly_roots_fin_two {V : Matrix (Fin 2) (Fin 2) ℂ} {μ₁ μ₂ : ℂ}
    (htr : V.trace = μ₁ + μ₂) (hdet : V.det = μ₁ * μ₂) :
    V.charpoly.roots = {μ₁, μ₂} := by
  have h : V.charpoly = (X - C μ₁) * (X - C μ₂) := by
    rw [charpoly_fin_two, htr, hdet]; simp only [C_add, C_mul]; ring
  rw [h, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

/-- `W(L) = (Aᴴ)⁻¹ Aᵀ` for an invertible basis matrix `A`. -/
lemma lagUnitary_eq {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.det ≠ 0) : lagUnitary A = (Aᴴ)⁻¹ * Aᵀ := by
  unfold lagUnitary
  rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mul]

/-- `D(g) = (g₀₁ - g₁₀) + i (g₀₀ + g₁₁)`, the determinant of `graphBasis2 g`. -/
def graphDet2 (g : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  ((g 0 1 - g 1 0 : ℝ) : ℂ) + ((g 0 0 + g 1 1 : ℝ) : ℂ) * I

/-- The coordinate swap `σ = W(Δ)`. -/
def swap2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

lemma graphBasis2_eq (g : Matrix (Fin 2) (Fin 2) ℝ) :
    graphBasis2 g = !![1, -I; (g 0 0 : ℂ) + I * g 1 0, (g 0 1 : ℂ) + I * g 1 1] := by
  ext r k; fin_cases r <;> fin_cases k <;> simp [graphBasis2]

lemma det_graphBasis2 (g : Matrix (Fin 2) (Fin 2) ℝ) :
    (graphBasis2 g).det = graphDet2 g := by
  rw [graphBasis2_eq, det_fin_two_of, graphDet2]
  push_cast
  linear_combination (g 1 0 : ℂ) * I_sq

lemma graphDet2_ne_zero {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det = 1) : graphDet2 g ≠ 0 := by
  intro h
  have hre : g 0 1 - g 1 0 = 0 := by simpa [graphDet2] using congrArg Complex.re h
  have him : g 0 0 + g 1 1 = 0 := by simpa [graphDet2] using congrArg Complex.im h
  have e1 : g 1 0 = g 0 1 := by linarith
  have e2 : g 1 1 = -g 0 0 := by linarith
  rw [det_fin_two, e1, e2] at hg
  nlinarith [sq_nonneg (g 0 0), sq_nonneg (g 0 1)]

lemma swap2_inv : swap2⁻¹ = swap2 :=
  inv_eq_left_inv (by ext i j; fin_cases i <;> fin_cases j <;> simp [swap2, Matrix.mul_apply])

lemma lagUnitary_graphBasis2_one : lagUnitary (graphBasis2 1) = swap2 := by
  have hd : (graphBasis2 1).det ≠ 0 := by
    rw [det_graphBasis2]; exact graphDet2_ne_zero (by simp)
  rw [lagUnitary_eq hd]
  have hT : (graphBasis2 1)ᵀ = (graphBasis2 1)ᴴ * swap2 := by
    rw [graphBasis2_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [swap2, Matrix.mul_apply]
  have hu : IsUnit ((graphBasis2 1)ᴴ).det := by
    rw [det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (by simpa using hd)
  rw [hT, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]

/-- `W(Γ_g) W(Δ)⁻¹ = D̄⁻¹ • adj(Aᴴ) Aᵀ σ`. -/
lemma graphUnitary2_eq {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det = 1) :
    graphUnitary2 g = (star (graphDet2 g))⁻¹ •
      (adjugate (graphBasis2 g)ᴴ * (graphBasis2 g)ᵀ * swap2) := by
  have hd : (graphBasis2 g).det ≠ 0 := by rw [det_graphBasis2]; exact graphDet2_ne_zero hg
  unfold graphUnitary2
  rw [lagUnitary_graphBasis2_one, swap2_inv, lagUnitary_eq hd, Matrix.inv_def,
    det_conjTranspose, det_graphBasis2]
  simp [Matrix.smul_mul]

lemma trace_graphUnitary2 {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det = 1) :
    (graphUnitary2 g).trace = (star (graphDet2 g))⁻¹ * (-4 * I) := by
  rw [graphUnitary2_eq hg, trace_smul, smul_eq_mul]
  congr 1
  rw [det_fin_two] at hg
  rw [graphBasis2_eq]
  simp [trace_fin_two, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, swap2,
    Matrix.vecMul, dotProduct]
  apply Complex.ext
  · simp; ring
  · simp; linarith

lemma det_graphUnitary2 {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det = 1) :
    (graphUnitary2 g).det = (star (graphDet2 g))⁻¹ * (-graphDet2 g) := by
  have hD := graphDet2_ne_zero hg
  have hsD : star (graphDet2 g) ≠ 0 := by simpa using hD
  rw [graphUnitary2_eq hg, det_smul, det_mul, det_mul, det_adjugate, det_transpose,
    det_conjTranspose, det_graphBasis2]
  have hs : swap2.det = -1 := by simp [swap2]
  rw [hs]
  simp only [Fintype.card_fin]
  field_simp
  ring

/-- The polar form of `D`: for `g = R(x) P` with `P` symmetric, `D = (tr P) i e^{ix}`. -/
lemma graphDet2_polar (x : ℝ) {P : Matrix (Fin 2) (Fin 2) ℝ} (hPs : P 1 0 = P 0 1) :
    graphDet2 (rotationMatrix x * P) =
      ((P 0 0 + P 1 1 : ℝ) : ℂ) * I * exp (x * I) := by
  rw [exp_mul_I, graphDet2]
  simp only [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, of_apply, cons_val',
    cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, hPs]
  apply Complex.ext <;> simp <;> ring

/-- Eigenvalues of the graph unitary in polar coordinates: for `g = R(x) P` with `P` symmetric
positive definite of determinant one, they are `e^{i(x ± γ)}`, `γ = arccos (2 / tr P)`. -/
theorem graphUnitary2_polar_roots (x : ℝ) {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.PosDef)
    (hdet : P.det = 1) :
    (graphUnitary2 (rotationMatrix x * P)).charpoly.roots =
      {exp ((x + Real.arccos (2 / (P 0 0 + P 1 1))) * I),
        exp ((x - Real.arccos (2 / (P 0 0 + P 1 1))) * I)} := by
  have hPs : P 1 0 = P 0 1 := by simpa using hP.1.apply 0 1
  have h00 : 0 < P 0 0 := by simpa using hP.diag_pos (i := 0)
  have h11 : 0 < P 1 1 := by simpa using hP.diag_pos (i := 1)
  rw [det_fin_two, hPs] at hdet
  set s := P 0 0 + P 1 1 with hs
  have hs0 : 0 < s := by linarith
  have hs2 : 2 ≤ s := by nlinarith [sq_nonneg (P 0 0 - P 1 1), sq_nonneg (P 0 1)]
  have hrot : (rotationMatrix x).det = 1 := by
    simp [rotationMatrix, det_fin_two]; nlinarith [Real.sin_sq_add_cos_sq x]
  have hg : (rotationMatrix x * P).det = 1 := by
    rw [det_mul, hrot, one_mul, det_fin_two, hPs, hdet]
  set γ := Real.arccos (2 / s)
  have hcos : Real.cos γ = 2 / s :=
    Real.cos_arccos (by have : 0 < 2 / s := by positivity
                        linarith) ((div_le_one hs0).mpr hs2)
  have hD := graphDet2_polar x hPs
  rw [← hs] at hD
  have hstar : star (graphDet2 (rotationMatrix x * P)) =
      (s : ℂ) * (-I) * exp (-(x * I)) := by
    rw [hD]
    simp [star_mul', ← exp_conj, map_neg]
  have hinv : (star (graphDet2 (rotationMatrix x * P)))⁻¹ = I * exp (x * I) / s := by
    rw [hstar]
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    field_simp
    rw [mul_assoc, ← exp_add]
    simp
  apply charpoly_roots_fin_two
  · rw [trace_graphUnitary2 hg, hinv]
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hc : exp (γ * I) + exp (-(γ * I)) = 2 * (2 / s : ℝ) := by
      rw [← hcos, Complex.ofReal_cos, Complex.cos]
      ring_nf
    rw [show exp ((x + γ) * I) + exp ((x - γ) * I) =
        exp (x * I) * (exp (γ * I) + exp (-(γ * I))) by
      rw [mul_add, ← exp_add, ← exp_add]; ring_nf, hc]
    push_cast
    linear_combination (-4 * exp (x * I) / s) * I_mul_I
  · rw [det_graphUnitary2 hg, hinv, hD, ← exp_add]
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    rw [show ((x : ℂ) + γ) * I + (x - γ) * I = x * I + x * I by ring, exp_add]
    field_simp
    simp [I_sq]

end

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (x : ℝ) {P : Matrix (Fin 2) (Fin 2) ℝ} (hP : P.PosDef)
    (hdet : P.det = 1) :
    (graphUnitary2 (rotationMatrix x * P)).charpoly.roots =
      {Complex.exp ((x + Real.arccos (2 / (P 0 0 + P 1 1))) * Complex.I),
        Complex.exp ((x - Real.arccos (2 / (P 0 0 + P 1 1))) * Complex.I)} :=
  graphUnitary2_polar_roots x hP hdet
