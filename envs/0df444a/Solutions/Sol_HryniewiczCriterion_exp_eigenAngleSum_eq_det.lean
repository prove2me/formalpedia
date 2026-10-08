-- Prove2me | solution 1 for HryniewiczCriterion.exp_eigenAngleSum_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:56:36.48826+00:00
-- url     : https://prove2.me/submissions/b14301e3-14ac-45e7-b027-40b1b1b19fd6

import Definitions.Def_HryniewiczCriterion_GraphAngle
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic

open HryniewiczCriterion

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

/-!
# Leaf C2, part 3: angle bookkeeping

* `exp_eigenAngleSum_mul_I`: `exp (i · eigenAngleSum V) = det V` when `|det V| = 1`.
* `angPos_exp_mul_I_of_mem`: `angPos (e^{iφ}) = φ` for `φ ∈ (0, 2π]`.
* `angPos_cayley`: the normalized angle of `e^{iα}(c - i)/(c + i)` is
  `α + π + 2 arctan c - 2π [c > tan((π - α)/2)]`.
* `eigenAngleSum_eq_sum_cayley`: the eigen-angle sum of `V` through the eigenvalues of its
  Cayley transform with pole `e^{iα}`.
-/

namespace HryniewiczCriterion

open Matrix Complex

noncomputable section

lemma exp_angPos_mul_I {z : ℂ} : exp ((angPos z : ℂ) * I) = exp ((arg z : ℂ) * I) := by
  unfold angPos
  split_ifs
  · rfl
  · push_cast
    rw [add_mul, exp_add, show (2 * (Real.pi : ℂ)) * I = 2 * Real.pi * I by ring, exp_two_pi_mul_I,
      mul_one]

lemma exp_sum_angPos_mul_norm (s : Multiset ℂ) :
    exp (((s.map angPos).sum : ℂ) * I) * (s.map fun z => ((‖z‖ : ℝ) : ℂ)).prod = s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
    push_cast
    rw [add_mul, exp_add, exp_angPos_mul_I]
    calc exp (↑(arg z) * I) * exp (↑(s.map angPos).sum * I) *
          ((‖z‖ : ℂ) * (s.map fun z => ((‖z‖ : ℝ) : ℂ)).prod)
        = ((‖z‖ : ℂ) * exp (↑(arg z) * I)) *
          (exp (↑(s.map angPos).sum * I) * (s.map fun z => ((‖z‖ : ℝ) : ℂ)).prod) := by ring
      _ = z * s.prod := by rw [norm_mul_exp_arg_mul_I, ih]

lemma multiset_prod_norm (s : Multiset ℂ) :
    (s.map fun z => ((‖z‖ : ℝ) : ℂ)).prod = ((‖s.prod‖ : ℝ) : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih => simp [ih]

/-- `exp (i · eigenAngleSum V) = det V` for `|det V| = 1`. -/
theorem exp_eigenAngleSum_mul_I {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n ℂ)
    (hV : ‖V.det‖ = 1) : exp ((eigenAngleSum V : ℂ) * I) = V.det := by
  have h := exp_sum_angPos_mul_norm V.charpoly.roots
  rw [multiset_prod_norm, ← det_eq_prod_roots_charpoly, hV] at h
  simpa [eigenAngleSum] using h

lemma angPos_exp_mul_I_of_mem {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ 2 * Real.pi) :
    angPos (exp ((φ : ℂ) * I)) = φ := by
  unfold angPos
  rcases le_or_gt φ Real.pi with hφ | hφ
  · have : arg (exp ((φ : ℂ) * I)) = φ := by
      rw [← cos_add_sin_I]
      exact_mod_cast arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], hφ⟩
    rw [this, if_pos h0]
  · have he : exp ((φ : ℂ) * I) = exp (((φ - 2 * Real.pi : ℝ) : ℂ) * I) := by
      push_cast
      rw [sub_mul, exp_sub, show (2 * (Real.pi : ℂ)) * I = 2 * Real.pi * I by ring,
        exp_two_pi_mul_I, div_one]
    have : arg (exp ((φ : ℂ) * I)) = φ - 2 * Real.pi := by
      rw [he, ← cos_add_sin_I]
      exact_mod_cast arg_cos_add_sin_mul_I ⟨by linarith, by linarith [Real.pi_pos]⟩
    rw [this, if_neg (by linarith)]
    ring

lemma angPos_exp_mul_I_of_mem' {φ : ℝ} (h0 : 2 * Real.pi < φ) (h1 : φ ≤ 4 * Real.pi) :
    angPos (exp ((φ : ℂ) * I)) = φ - 2 * Real.pi := by
  have he : exp ((φ : ℂ) * I) = exp (((φ - 2 * Real.pi : ℝ) : ℂ) * I) := by
    push_cast
    rw [sub_mul, exp_sub, show (2 * (Real.pi : ℂ)) * I = 2 * Real.pi * I by ring,
      exp_two_pi_mul_I, div_one]
  rw [he, angPos_exp_mul_I_of_mem (by linarith) (by linarith)]

/-- `(c - i)/(c + i) = e^{i(π + 2 arctan c)}`. -/
lemma cayley_scalar_eq_exp (c : ℝ) :
    ((c : ℂ) - I) / ((c : ℂ) + I) = exp (((Real.pi + 2 * Real.arctan c : ℝ) : ℂ) * I) := by
  have hs : (0 : ℝ) < √(1 + c ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (√(1 + c ^ 2)) ^ 2 = 1 + c ^ 2 := Real.sq_sqrt (by positivity)
  have hexp : exp (((Real.arctan c : ℝ) : ℂ) * I) = (1 + c * I) / (√(1 + c ^ 2) : ℝ) := by
    rw [← cos_add_sin_I, ← ofReal_cos, ← ofReal_sin, Real.cos_arctan, Real.sin_arctan]
    push_cast
    ring
  have hne : (c : ℂ) + I ≠ 0 := by
    intro h; have := congr_arg Complex.im h; simp at this
  have hne2 : ((√(1 + c ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hs2c : ((√(1 + c ^ 2) : ℝ) : ℂ) ^ 2 = 1 + (c : ℂ) ^ 2 := by exact_mod_cast hs2
  push_cast
  rw [add_mul, exp_add, exp_pi_mul_I, show 2 * (Real.arctan c : ℂ) * I =
    (Real.arctan c : ℂ) * I + (Real.arctan c : ℂ) * I by ring, exp_add, hexp]
  have h1c : (1 + (c : ℂ) ^ 2) ≠ 0 := by
    rw [← hs2c]; exact pow_ne_zero 2 hne2
  rw [div_mul_div_comm, ← pow_two ((√(1 + c ^ 2) : ℝ) : ℂ), hs2c, neg_one_mul, ← neg_div,
    div_eq_div_iff hne h1c]
  linear_combination (2 * (c : ℂ) + c ^ 3 + c ^ 2 * I) * I_sq

/-- The normalized angle of `e^{iα}(c - i)/(c + i)`, `α ∈ (0, 2π)`. -/
def gAngle (α c : ℝ) : ℝ :=
  α + Real.pi + 2 * Real.arctan c - if Real.tan ((Real.pi - α) / 2) < c then 2 * Real.pi else 0

lemma angPos_cayley {α : ℝ} (hα0 : 0 < α) (hα1 : α < 2 * Real.pi) (c : ℝ) :
    angPos (exp ((α : ℂ) * I) * ((c : ℂ) - I) / ((c : ℂ) + I)) = gAngle α c := by
  have ha1 := Real.neg_pi_div_two_lt_arctan c
  have ha2 := Real.arctan_lt_pi_div_two c
  rw [mul_div_assoc, cayley_scalar_eq_exp, ← exp_add, ← add_mul, ← ofReal_add]
  have hy1 : -(Real.pi / 2) < (Real.pi - α) / 2 := by linarith
  have hy2 : (Real.pi - α) / 2 < Real.pi / 2 := by linarith
  have key : Real.tan ((Real.pi - α) / 2) < c ↔ (Real.pi - α) / 2 < Real.arctan c := by
    rw [← Real.arctan_lt_arctan_iff, Real.arctan_tan hy1 hy2]
  unfold gAngle
  split_ifs with h
  · rw [angPos_exp_mul_I_of_mem' (by linarith [key.mp h]) (by linarith)]
    ring
  · rw [angPos_exp_mul_I_of_mem (by linarith) (by linarith [not_lt.mp (mt key.mpr h)])]
    ring

/-- The eigen-angle sum of `V` through the eigenvalues of its Cayley transform. -/
theorem eigenAngleSum_eq_sum_cayley {n : Type} [Fintype n] [DecidableEq n] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 2 * Real.pi) {V : Matrix n n ℂ}
    (hdet : (exp ((α : ℂ) * I) • (1 : Matrix n n ℂ) - V).det ≠ 0)
    (hC : (cayleyT (exp ((α : ℂ) * I)) V).IsHermitian) :
    eigenAngleSum V = ∑ k, gAngle α (hC.eigenvalues k) := by
  unfold eigenAngleSum
  rw [roots_charpoly_eq_cayley hdet hC, Multiset.map_map]
  simp only [Function.comp_def, angPos_cayley hα0 hα1]
  rfl

end

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n ℂ)
    (hV : ‖V.det‖ = 1) :
    Complex.exp ((eigenAngleSum V : ℂ) * Complex.I) = V.det :=
  exp_eigenAngleSum_mul_I V hV
