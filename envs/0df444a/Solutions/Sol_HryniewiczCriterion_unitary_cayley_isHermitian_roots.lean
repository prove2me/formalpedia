-- Prove2me | solution 1 for HryniewiczCriterion.unitary_cayley_isHermitian_roots
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:56:35.477852+00:00
-- url     : https://prove2.me/submissions/c5ac5531-6b7f-4438-9f61-44d7037b88d2

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Matrix

/-!
# Leaf C2, part 2: the Cayley transform of a unitary matrix

For `a` on the unit circle that is not an eigenvalue of the unitary `V`,
`C = 2 i a (a - V)⁻¹ - i = i (a + V)(a - V)⁻¹` is Hermitian, `(C + i) V = a (C - i)`, and the
eigenvalues of `V` are `a (cₖ - i)/(cₖ + i)` for the eigenvalues `cₖ` of `C`.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The Cayley transform `2 i a (a - V)⁻¹ - i` of `V` with pole `a`. -/
def cayleyT (a : ℂ) (V : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 * I * a) • (a • (1 : Matrix n n ℂ) - V)⁻¹ - I • (1 : Matrix n n ℂ)

lemma inv_comm_of_sub {a : ℂ} {V : Matrix n n ℂ} :
    (a • (1 : Matrix n n ℂ) - V)⁻¹ * V = V * (a • (1 : Matrix n n ℂ) - V)⁻¹ := by
  set M := a • (1 : Matrix n n ℂ) - V
  by_cases hM : IsUnit M.det
  · have hc : M * V = V * M := by simp [M, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    calc M⁻¹ * V = M⁻¹ * V * (M * M⁻¹) := by rw [mul_nonsing_inv _ hM, Matrix.mul_one]
      _ = M⁻¹ * (M * V) * M⁻¹ := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = V * M⁻¹ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.one_mul]
  · simp [nonsing_inv_apply_not_isUnit _ hM]

lemma cayleyT_mul {a : ℂ} {V : Matrix n n ℂ} (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) :
    (cayleyT a V + I • (1 : Matrix n n ℂ)) * V = a • (cayleyT a V - I • (1 : Matrix n n ℂ)) := by
  set M := a • (1 : Matrix n n ℂ) - V
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have h1 : a • M⁻¹ - (1 : Matrix n n ℂ) = V * M⁻¹ := by
    have : a • M⁻¹ - (1 : Matrix n n ℂ) = (a • (1 : Matrix n n ℂ) - M) * M⁻¹ := by
      rw [sub_mul, mul_nonsing_inv _ hM, smul_mul_assoc, Matrix.one_mul]
    rw [this]; simp [M]
  have hL : (cayleyT a V + I • (1 : Matrix n n ℂ)) * V = (2 * I * a) • (V * M⁻¹) := by
    simp only [cayleyT, sub_add_cancel, smul_mul_assoc]
    rw [inv_comm_of_sub]
  have hR : a • (cayleyT a V - I • (1 : Matrix n n ℂ)) = (2 * I * a) • (a • M⁻¹ - 1) := by
    simp only [cayleyT, smul_sub, smul_smul]
    rw [sub_sub, ← add_smul]
    congr 1
    · congr 1; ring
    · rw [show a * I + a * I = 2 * I * a by ring]
  rw [hL, hR, h1]

lemma smul_inv_sub_one {a : ℂ} {V : Matrix n n ℂ} (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) :
    a • (a • (1 : Matrix n n ℂ) - V)⁻¹ - 1 = V * (a • (1 : Matrix n n ℂ) - V)⁻¹ := by
  set M := a • (1 : Matrix n n ℂ) - V
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have : a • M⁻¹ - (1 : Matrix n n ℂ) = (a • (1 : Matrix n n ℂ) - M) * M⁻¹ := by
    rw [sub_mul, mul_nonsing_inv _ hM, smul_mul_assoc, Matrix.one_mul]
  rw [this]; simp [M]

lemma inv_conjTranspose_sub {a : ℂ} {V : Matrix n n ℂ} (hV : star V * V = 1) (ha : star a * a = 1)
    (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) :
    (a • (1 : Matrix n n ℂ) - V)⁻¹ᴴ = (-a) • (V * (a • (1 : Matrix n n ℂ) - V)⁻¹) := by
  set M := a • (1 : Matrix n n ℂ) - V
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  rw [conjTranspose_nonsing_inv]
  apply inv_eq_right_inv
  have hVh : Vᴴ * V = 1 := hV
  have hMh : Mᴴ = star a • (1 : Matrix n n ℂ) - Vᴴ := by
    simp [M, conjTranspose_sub, conjTranspose_smul]
  rw [hMh, sub_mul, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, ← Matrix.mul_assoc, hVh,
    Matrix.one_mul, smul_smul, mul_neg, ha]
  have : M * M⁻¹ = 1 := mul_nonsing_inv _ hM
  rw [← this]
  simp only [M, sub_mul, smul_mul_assoc, Matrix.one_mul, neg_smul, one_smul]
  abel

lemma cayleyT_isHermitian {a : ℂ} {V : Matrix n n ℂ} (hV : star V * V = 1) (ha : star a * a = 1)
    (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) : (cayleyT a V).IsHermitian := by
  set M := a • (1 : Matrix n n ℂ) - V
  have hC : cayleyT a V = (2 * I) • (V * M⁻¹) + I • (1 : Matrix n n ℂ) := by
    rw [← smul_inv_sub_one hdet]
    simp only [cayleyT, smul_sub, smul_smul]
    rw [mul_assoc, sub_add, ← sub_smul]
    congr 2; ring
  unfold Matrix.IsHermitian
  conv_rhs => rw [hC]
  rw [cayleyT, conjTranspose_sub, conjTranspose_smul, conjTranspose_smul,
    inv_conjTranspose_sub hV ha hdet, conjTranspose_one, smul_smul]
  have hs : star (2 * I * a) * -a = (2 * I) * (star a * a) := by
    have : star a * a = a * star a := mul_comm _ _
    simp only [star_mul', star_ofNat, Complex.star_def, Complex.conj_I]; ring
  rw [hs, ha, mul_one, show star I = -I from Complex.conj_I, neg_smul, sub_neg_eq_add]

/-- The eigenvalues of `V`, through the eigenvalues `cₖ` of its Cayley transform. -/
lemma roots_charpoly_eq_cayley {a : ℂ} {V : Matrix n n ℂ}
    (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) (hC : (cayleyT a V).IsHermitian) :
    V.charpoly.roots = Multiset.map
      (fun k => a * (((hC.eigenvalues k : ℝ) : ℂ) - I) / (((hC.eigenvalues k : ℝ) : ℂ) + I))
      Finset.univ.val := by
  set C := cayleyT a V
  set U : Matrix n n ℂ := (hC.eigenvectorUnitary : Matrix n n ℂ)
  set c : n → ℂ := fun k => ((hC.eigenvalues k : ℝ) : ℂ)
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hD : star U * C * U = diagonal c := by
    have := hC.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    have h2 : diagonal c = diagonal (RCLike.ofReal ∘ hC.eigenvalues) := rfl
    rw [h2]
    simpa [U] using this
  set W := star U * V * U
  have key : diagonal (fun k => c k + I) * W = a • diagonal (fun k => c k - I) := by
    have e1 : diagonal (fun k => c k + I) = star U * (C + I • (1 : Matrix n n ℂ)) * U := by
      rw [Matrix.mul_add, Matrix.add_mul, hD, mul_smul_comm, Matrix.mul_one, smul_mul_assoc, hUU]
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
    have e2 : diagonal (fun k => c k - I) = star U * (C - I • (1 : Matrix n n ℂ)) * U := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hD, mul_smul_comm, Matrix.mul_one, smul_mul_assoc, hUU]
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h]
    rw [e1, e2]
    calc star U * (C + I • 1) * U * W
        = star U * ((C + I • 1) * V) * U := by
          simp only [W, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc U (star U), hUU', Matrix.one_mul]
      _ = a • (star U * (C - I • 1) * U) := by
          rw [cayleyT_mul hdet, mul_smul_comm, smul_mul_assoc]
  have hW : W = diagonal (fun k => a * (c k - I) / (c k + I)) := by
    ext i j
    have hk := congr_fun (congr_fun key i) j
    have hne : c i + I ≠ 0 := by
      intro h; have := congr_arg Complex.im h; simp [c] at this
    simp only [diagonal_mul, Matrix.smul_apply, diagonal_apply, smul_eq_mul] at hk
    rw [diagonal_apply]
    by_cases h : i = j
    · subst h; simp only [if_true] at hk ⊢; rw [eq_div_iff hne, mul_comm]; exact hk
    · simp only [h, if_false, mul_zero] at hk ⊢
      exact (mul_eq_zero.mp hk).resolve_left hne
  have hchar : V.charpoly = W.charpoly := by
    simp only [W, Matrix.mul_assoc]
    rw [charpoly_mul_comm, Matrix.mul_assoc, hUU', Matrix.mul_one]
  rw [hchar, hW, charpoly_diagonal, Polynomial.roots_prod]
  · simp [c]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

end

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n ℂ) (a : ℂ)
    (hV : star V * V = 1) (ha : star a * a = 1)
    (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) :
    ∃ hC : ((2 * Complex.I * a) • (a • (1 : Matrix n n ℂ) - V)⁻¹ -
        Complex.I • (1 : Matrix n n ℂ)).IsHermitian,
      V.charpoly.roots = Multiset.map
        (fun k => a * (((hC.eigenvalues k : ℝ) : ℂ) - Complex.I) /
          (((hC.eigenvalues k : ℝ) : ℂ) + Complex.I)) Finset.univ.val :=
  ⟨cayleyT_isHermitian hV ha hdet, roots_charpoly_eq_cayley hdet (cayleyT_isHermitian hV ha hdet)⟩
