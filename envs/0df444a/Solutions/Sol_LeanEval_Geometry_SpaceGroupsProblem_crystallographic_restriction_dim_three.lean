-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.crystallographic_restriction_dim_three
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T07:43:55.12275+00:00
-- url     : https://prove2.me/submissions/3b760652-9332-462e-a65d-d6a58393b540

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_pointGroup_integral_matrix

open Matrix RealInnerProductSpace Module LeanEval.Geometry.SpaceGroupsProblem

namespace SpaceGroupsCrystRestriction

/-! ### Two identities for `3 × 3` matrices -/

theorem det_smul_one_sub_fin_three {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R)
    (r : R) :
    (r • (1 : Matrix (Fin 3) (Fin 3) R) - M).det
      = r ^ 3 - M.trace * r ^ 2 + M.adjugate.trace * r - M.det := by
  simp [Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.adjugate_fin_three,
    Fin.sum_univ_three]
  ring

theorem cayleyHamilton_fin_three {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M ^ 3 = M.trace • M ^ 2 - M.adjugate.trace • M + M.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three,
      Matrix.adjugate_fin_three, Matrix.det_fin_three] <;> ring

/-! ### The matrix of an isometry in the standard orthonormal basis -/

/-- The standard orthonormal basis of `ℝ³`. -/
noncomputable abbrev stdBasis : OrthonormalBasis (Fin 3) ℝ (E 3) := EuclideanSpace.basisFun (Fin 3) ℝ

/-- The matrix of a linear isometry of `ℝ³` in the standard orthonormal basis. -/
noncomputable def isomMatrix (A : E 3 ≃ₗᵢ[ℝ] E 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix stdBasis.toBasis stdBasis.toBasis (A.toLinearEquiv : E 3 →ₗ[ℝ] E 3)

theorem isomMatrix_apply (A : E 3 ≃ₗᵢ[ℝ] E 3) (i j : Fin 3) :
    isomMatrix A i j = A (stdBasis j) i := by
  simp [isomMatrix, LinearMap.toMatrix_apply]

theorem isomMatrix_one : isomMatrix 1 = 1 := by
  ext i j
  simp [isomMatrix_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply,
    Matrix.one_apply, eq_comm]

theorem isomMatrix_mul (A B : E 3 ≃ₗᵢ[ℝ] E 3) :
    isomMatrix (A * B) = isomMatrix A * isomMatrix B := by
  simp only [isomMatrix]
  rw [show ((A * B).toLinearEquiv : E 3 →ₗ[ℝ] E 3)
      = (A.toLinearEquiv : E 3 →ₗ[ℝ] E 3) ∘ₗ (B.toLinearEquiv : E 3 →ₗ[ℝ] E 3) from rfl,
    LinearMap.toMatrix_comp _ stdBasis.toBasis]

theorem isomMatrix_pow (A : E 3 ≃ₗᵢ[ℝ] E 3) (k : ℕ) : isomMatrix (A ^ k) = (isomMatrix A) ^ k := by
  induction k with
  | zero => simpa using isomMatrix_one
  | succ n ih => rw [pow_succ, pow_succ, isomMatrix_mul, ih]

theorem isomMatrix_injective : Function.Injective isomMatrix := by
  intro A B hAB
  have h : ∀ j, A (stdBasis j) = B (stdBasis j) := by
    intro j
    ext i
    have := congrFun (congrFun hAB i) j
    rwa [isomMatrix_apply, isomMatrix_apply] at this
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply stdBasis.toBasis.ext
  intro j
  simpa using h j

theorem isomMatrix_eq_one_iff {A : E 3 ≃ₗᵢ[ℝ] E 3} : isomMatrix A = 1 ↔ A = 1 :=
  ⟨fun h => isomMatrix_injective (by rw [h, isomMatrix_one]), fun h => by rw [h, isomMatrix_one]⟩

theorem isomMatrix_orthogonal (A : E 3 ≃ₗᵢ[ℝ] E 3) :
    (isomMatrix A)ᵀ * isomMatrix A = 1 := by
  ext i j
  have h : ⟪A (stdBasis i), A (stdBasis j)⟫ = ⟪(stdBasis i : E 3), stdBasis j⟫ :=
    A.inner_map_map _ _
  rw [PiLp.inner_apply, PiLp.inner_apply] at h
  simp only [RCLike.inner_apply, conj_trivial] at h
  have h2 : ∑ k, (A (stdBasis i)) k * (A (stdBasis j)) k
      = ∑ k, ((stdBasis i : E 3)) k * ((stdBasis j : E 3)) k := by
    rw [Finset.sum_congr rfl (fun k _ => mul_comm ((A (stdBasis i)) k) ((A (stdBasis j)) k)), h]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, isomMatrix_apply, Matrix.one_apply]
  rw [h2]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply, eq_comm]

theorem isomMatrix_orthogonal' (A : E 3 ≃ₗᵢ[ℝ] E 3) :
    isomMatrix A * (isomMatrix A)ᵀ = 1 :=
  mul_eq_one_comm.mp (isomMatrix_orthogonal A)

theorem det_isomMatrix_sq (A : E 3 ≃ₗᵢ[ℝ] E 3) : (isomMatrix A).det ^ 2 = 1 := by
  have := congrArg Matrix.det (isomMatrix_orthogonal A)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  rw [sq]
  exact this

theorem adjugate_isomMatrix (A : E 3 ≃ₗᵢ[ℝ] E 3) :
    (isomMatrix A).adjugate = (isomMatrix A).det • (isomMatrix A)ᵀ := by
  set Q := isomMatrix A with hQ
  have hinv : Q * Qᵀ = 1 := isomMatrix_orthogonal' A
  have h1 : Q * Q.adjugate = Q.det • (1 : Matrix (Fin 3) (Fin 3) ℝ) := Matrix.mul_adjugate Q
  have h2 : Q * (Q.det • Qᵀ) = Q.det • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.mul_smul, hinv]
  have hQinv : Invertible Q := invertibleOfRightInverse Q Qᵀ hinv
  calc Q.adjugate = ⅟Q * (Q * Q.adjugate) := by rw [← Matrix.mul_assoc, invOf_mul_self, one_mul]
    _ = ⅟Q * (Q * (Q.det • Qᵀ)) := by rw [h1, h2]
    _ = Q.det • Qᵀ := by rw [← Matrix.mul_assoc, invOf_mul_self, one_mul]

theorem trace_adjugate_isomMatrix (A : E 3 ≃ₗᵢ[ℝ] E 3) :
    (isomMatrix A).adjugate.trace = (isomMatrix A).det * (isomMatrix A).trace := by
  rw [adjugate_isomMatrix, Matrix.trace_smul, Matrix.trace_transpose, smul_eq_mul]

/-! ### Orthogonal matrices preserve the dot product -/

theorem orth_dotProduct {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Qᵀ * Q = 1)
    (x y : Fin n → ℝ) : (Q *ᵥ x) ⬝ᵥ (Q *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hQ,
    Matrix.vecMul_one]

/-- An orthogonal matrix has no real eigenvalue of modulus `≠ 1`. -/
theorem sq_eq_one_of_det_smul_sub_eq_zero {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Qᵀ * Q = 1) {r : ℝ} (h : (r • (1 : Matrix (Fin n) (Fin n) ℝ) - Q).det = 0) :
    r ^ 2 = 1 := by
  obtain ⟨v, hv, hvz⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h
  have hQv : Q *ᵥ v = r • v := by
    rw [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hvz
    exact hvz.symm
  have hvv : v ⬝ᵥ v ≠ 0 := fun hc => hv (dotProduct_self_eq_zero.1 hc)
  have key : r ^ 2 * (v ⬝ᵥ v) = v ⬝ᵥ v := by
    have := orth_dotProduct hQ v v
    rw [hQv, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have := mul_right_cancel₀ hvv (by rw [key, one_mul] : r ^ 2 * (v ⬝ᵥ v) = 1 * (v ⬝ᵥ v))
  exact this

/-! ### Isometries are semisimple at the eigenvalues `± 1` -/

/-- If `Q` is orthogonal and `ε = ± 1`, then `(Q - ε)² v = 0` implies `(Q - ε) v = 0`. -/
theorem orth_semisimple {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Qᵀ * Q = 1) {eps : ℝ}
    (heps : eps * eps = 1) {v : Fin n → ℝ}
    (h : (Q - eps • 1) *ᵥ ((Q - eps • 1) *ᵥ v) = 0) : (Q - eps • 1) *ᵥ v = 0 := by
  set w := (Q - eps • 1) *ᵥ v with hw
  have hQw : Q *ᵥ w = eps • w := by
    rw [Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h
  have hww : w ⬝ᵥ w = 0 := by
    have h1 : w ⬝ᵥ w = ((Q *ᵥ v) - eps • v) ⬝ᵥ w := by
      rw [hw, Matrix.sub_mulVec, smul_mulVec, Matrix.one_mulVec]
    have hwq : w = eps • (Q *ᵥ w) := by
      rw [hQw, smul_smul, heps, one_smul]
    have h2 : (Q *ᵥ v) ⬝ᵥ w = eps * (v ⬝ᵥ w) := by
      calc (Q *ᵥ v) ⬝ᵥ w = (Q *ᵥ v) ⬝ᵥ (eps • (Q *ᵥ w)) := by rw [← hwq]
        _ = eps * ((Q *ᵥ v) ⬝ᵥ (Q *ᵥ w)) := by rw [dotProduct_smul, smul_eq_mul]
        _ = eps * (v ⬝ᵥ w) := by rw [orth_dotProduct hQ]
    rw [h1, sub_dotProduct, h2, smul_dotProduct, smul_eq_mul, sub_self]
  exact dotProduct_self_eq_zero.1 hww

/-- Matrix version: if `(Q - α)² (Q - β) = 0` for an orthogonal `Q` and `α = ± 1`, then already
`(Q - α)(Q - β) = 0`. -/
theorem orth_reduce_double_root {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Qᵀ * Q = 1)
    {a b : ℝ} (ha : a * a = 1)
    (h : (Q - a • 1) * (Q - a • 1) * (Q - b • 1) = 0) :
    (Q - a • 1) * (Q - b • 1) = 0 := by
  ext i j
  have hv : ∀ v : Fin n → ℝ, ((Q - a • 1) * (Q - b • 1)) *ᵥ v = 0 := by
    intro v
    have h1 : (Q - a • 1) *ᵥ ((Q - a • 1) *ᵥ ((Q - b • 1) *ᵥ v)) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
    have h2 := orth_semisimple hQ ha h1
    rw [← Matrix.mulVec_mulVec]
    exact h2
  have := hv (Pi.single j 1)
  have hthis := congrFun this i
  simpa [Matrix.mulVec_single] using hthis

/-- If `Q` is orthogonal and `(Q - a)² = 0` with `a = ± 1`, then `Q = a`. -/
theorem orth_reduce_sq {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Qᵀ * Q = 1)
    {a : ℝ} (ha : a * a = 1) (h : (Q - a • 1) * (Q - a • 1) = 0) : Q = a • 1 := by
  have hv : ∀ v : Fin n → ℝ, (Q - a • 1) *ᵥ v = 0 := by
    intro v
    refine orth_semisimple hQ ha ?_
    rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
  have hzero : Q - a • 1 = 0 := by
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  have := sub_eq_zero.mp hzero
  exact this

/-! ### The ten possible characteristic equations -/

/-- If an orthogonal `3 × 3` matrix satisfies `(Q - c)(Q² - sQ + 1) = 0` with `c = ± 1` and
`s ∈ {-2, -1, 0, 1, 2}`, then `Q ^ k = 1` for some `k ∈ {1, 2, 3, 4, 6}`. -/
theorem exists_pow_eq_one_of_char_eq {Q : Matrix (Fin 3) (Fin 3) ℝ} (hQ : Qᵀ * Q = 1)
    {c s : ℝ} (hc : c = 1 ∨ c = -1) (hs : s = -2 ∨ s = -1 ∨ s = 0 ∨ s = 1 ∨ s = 2)
    (hp : (Q - c • 1) * (Q ^ 2 - s • Q + 1) = 0) :
    Q ^ 1 = 1 ∨ Q ^ 2 = 1 ∨ Q ^ 3 = 1 ∨ Q ^ 4 = 1 ∨ Q ^ 6 = 1 := by
  have hone : (1 : ℝ) * 1 = 1 := by norm_num
  have hnegone : (-1 : ℝ) * -1 = 1 := by norm_num
  rcases hc with rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl | rfl
  -- c = 1
  · -- s = -2 : (Q + 1)² (Q - 1) = 0
    right; left
    have hfac : (Q - (-1 : ℝ) • 1) * (Q - (-1 : ℝ) • 1) * (Q - (1 : ℝ) • 1)
        = (Q - (1 : ℝ) • 1) * (Q ^ 2 - (-2 : ℝ) • Q + 1) := by
      noncomm_ring
      module
    have h2 := orth_reduce_double_root hQ hnegone (by rw [hfac, hp])
    have key : Q ^ 2 - 1 = (Q - (-1 : ℝ) • 1) * (Q - (1 : ℝ) • 1) := by
      noncomm_ring
      module
    rw [h2, sub_eq_zero] at key
    exact key
  · -- s = -1 : Q³ = 1
    right; right; left
    have key : Q ^ 3 - 1 = (Q - (1 : ℝ) • 1) * (Q ^ 2 - (-1 : ℝ) • Q + 1) := by
      noncomm_ring
      module
    rw [hp, sub_eq_zero] at key
    exact key
  · -- s = 0 : Q⁴ = 1
    right; right; right; left
    have key : Q ^ 4 - 1 = ((Q - (1 : ℝ) • 1) * (Q ^ 2 - (0 : ℝ) • Q + 1)) * (Q + 1) := by
      noncomm_ring
      module
    rw [hp, zero_mul, sub_eq_zero] at key
    exact key
  · -- s = 1 : Q⁶ = 1
    right; right; right; right
    have key : Q ^ 6 - 1
        = ((Q - (1 : ℝ) • 1) * (Q ^ 2 - (1 : ℝ) • Q + 1)) * ((Q + 1) * (Q ^ 2 + Q + 1)) := by
      noncomm_ring
      module
    rw [hp, zero_mul, sub_eq_zero] at key
    exact key
  · -- s = 2 : (Q - 1)³ = 0
    left
    have hfac : (Q - (1 : ℝ) • 1) * (Q - (1 : ℝ) • 1) * (Q - (1 : ℝ) • 1)
        = (Q - (1 : ℝ) • 1) * (Q ^ 2 - (2 : ℝ) • Q + 1) := by
      noncomm_ring
      module
    have h2 := orth_reduce_double_root hQ hone (by rw [hfac, hp])
    have h3 := orth_reduce_sq hQ hone h2
    rw [pow_one, h3]
    simp
  -- c = -1
  · -- s = -2 : (Q + 1)³ = 0
    right; left
    have hfac : (Q - (-1 : ℝ) • 1) * (Q - (-1 : ℝ) • 1) * (Q - (-1 : ℝ) • 1)
        = (Q - (-1 : ℝ) • 1) * (Q ^ 2 - (-2 : ℝ) • Q + 1) := by
      noncomm_ring
      module
    have h2 := orth_reduce_double_root hQ hnegone (by rw [hfac, hp])
    have h3 := orth_reduce_sq hQ hnegone h2
    rw [h3]
    ext i j
    simp [pow_two, Matrix.mul_apply, Matrix.one_apply, Finset.sum_ite_eq']
  · -- s = -1 : Q⁶ = 1
    right; right; right; right
    have key : Q ^ 6 - 1
        = ((Q - (-1 : ℝ) • 1) * (Q ^ 2 - (-1 : ℝ) • Q + 1)) * ((Q - 1) * (Q ^ 2 - Q + 1)) := by
      noncomm_ring
      module
    rw [hp, zero_mul, sub_eq_zero] at key
    exact key
  · -- s = 0 : Q⁴ = 1
    right; right; right; left
    have key : Q ^ 4 - 1 = ((Q - (-1 : ℝ) • 1) * (Q ^ 2 - (0 : ℝ) • Q + 1)) * (Q - 1) := by
      noncomm_ring
      module
    rw [hp, zero_mul, sub_eq_zero] at key
    exact key
  · -- s = 1 : Q⁶ = 1
    right; right; right; right
    have key : Q ^ 6 - 1 = ((Q - (-1 : ℝ) • 1) * (Q ^ 2 - (1 : ℝ) • Q + 1)) * (Q ^ 3 - 1) := by
      noncomm_ring
      module
    rw [hp, zero_mul, sub_eq_zero] at key
    exact key
  · -- s = 2 : (Q - 1)² (Q + 1) = 0
    right; left
    have hfac : (Q - (1 : ℝ) • 1) * (Q - (1 : ℝ) • 1) * (Q - (-1 : ℝ) • 1)
        = (Q - (-1 : ℝ) • 1) * (Q ^ 2 - (2 : ℝ) • Q + 1) := by
      noncomm_ring
      module
    have h2 := orth_reduce_double_root hQ hone (by rw [hfac, hp])
    have key : Q ^ 2 - 1 = (Q - (1 : ℝ) • 1) * (Q - (-1 : ℝ) • 1) := by
      noncomm_ring
      module
    rw [h2, sub_eq_zero] at key
    exact key

/-! ### The characteristic equation of the matrix of an isometry -/

theorem isomMatrix_char_eq (A : E 3 ≃ₗᵢ[ℝ] E 3) :
    (isomMatrix A - (isomMatrix A).det • 1) *
      ((isomMatrix A) ^ 2 - ((isomMatrix A).trace - (isomMatrix A).det) • (isomMatrix A) + 1)
      = 0 := by
  set Q := isomMatrix A with hQdef
  have hcc : Q.det * Q.det = 1 := by
    have := det_isomMatrix_sq A
    rw [sq] at this
    exact this
  have hCH : Q ^ 3 = Q.trace • Q ^ 2 - Q.adjugate.trace • Q + Q.det • 1 :=
    cayleyHamilton_fin_three Q
  rw [trace_adjugate_isomMatrix] at hCH
  have hfac : (Q - Q.det • 1) * (Q ^ 2 - (Q.trace - Q.det) • Q + 1)
      = Q ^ 3 - Q.trace • Q ^ 2 + (Q.det * Q.trace) • Q - Q.det • 1 := by
    have hexp : (Q - Q.det • 1) * (Q ^ 2 - (Q.trace - Q.det) • Q + 1)
        = Q ^ 3 - ((Q.trace - Q.det) + Q.det) • Q ^ 2
          + (1 + Q.det * (Q.trace - Q.det)) • Q - Q.det • 1 := by
      noncomm_ring
      module
    have hcoef1 : (Q.trace - Q.det) + Q.det = Q.trace := by ring
    have hcoef2 : (1 : ℝ) + Q.det * (Q.trace - Q.det) = Q.det * Q.trace := by
      linear_combination -hcc
    rw [hexp, hcoef1, hcoef2]
  rw [hfac, hCH]
  abel

/-! ### The trace of a point group element is an integer -/

theorem exists_int_trace {G : Subgroup (EuclideanIsom 3)} (hG : IsCrystallographicGroup G)
    {A : E 3 ≃ₗᵢ[ℝ] E 3} (hA : A ∈ pointGroup G) :
    ∃ m : ℤ, (isomMatrix A).trace = (m : ℝ) := by
  obtain ⟨w, hwli, hwspan, hmat⟩ := pointGroup_integral_matrix hG
  obtain ⟨M, hM⟩ := hmat A hA
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (E 3) := by simp
  let wb : Basis (Fin 3) ℝ (E 3) := basisOfLinearIndependentOfCardEqFinrank hwli hcard
  have hwb : ∀ i, wb i = w i := fun i => by
    simp [wb]
  have htoMatrix : LinearMap.toMatrix wb wb (A.toLinearEquiv : E 3 →ₗ[ℝ] E 3)
      = M.map (fun z : ℤ => (z : ℝ)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have hval : (A.toLinearEquiv : E 3 →ₗ[ℝ] E 3) (wb j) = ∑ k, (M k j : ℝ) • wb k := by
      rw [hwb j]
      rw [show ((A.toLinearEquiv : E 3 →ₗ[ℝ] E 3) (w j)) = A (w j) from rfl, hM j]
      exact Finset.sum_congr rfl fun k _ => by rw [hwb k]
    rw [hval, map_sum]
    simp [Finsupp.single_apply, eq_comm]
  refine ⟨M.trace, ?_⟩
  have h1 : LinearMap.trace ℝ (E 3) (A.toLinearEquiv : E 3 →ₗ[ℝ] E 3) = (isomMatrix A).trace := by
    rw [LinearMap.trace_eq_matrix_trace ℝ stdBasis.toBasis]
    rfl
  have h2 : LinearMap.trace ℝ (E 3) (A.toLinearEquiv : E 3 →ₗ[ℝ] E 3)
      = (M.map (fun z : ℤ => (z : ℝ))).trace := by
    rw [LinearMap.trace_eq_matrix_trace ℝ wb, htoMatrix]
  rw [← h1, h2, Matrix.trace]
  push_cast [Matrix.trace, Matrix.diag]
  rfl

/-! ### The trace of an isometry differs from its determinant by at most `2` -/

theorem abs_trace_sub_det_le_two (A : E 3 ≃ₗᵢ[ℝ] E 3) :
    |(isomMatrix A).trace - (isomMatrix A).det| ≤ 2 := by
  set Q := isomMatrix A with hQdef
  have hcc : Q.det * Q.det = 1 := by
    have := det_isomMatrix_sq A
    rw [sq] at this
    exact this
  by_contra hcon
  push_neg at hcon
  set s := Q.trace - Q.det with hs
  set u := |s| with hu
  have hu2 : 2 < u := hcon
  have hD : (0 : ℝ) ≤ u ^ 2 - 4 := by nlinarith
  set t := Real.sqrt (u ^ 2 - 4) with ht
  have htsq : t ^ 2 = u ^ 2 - 4 := Real.sq_sqrt hD
  have htnn : 0 ≤ t := Real.sqrt_nonneg _
  set r0 := (u + t) / 2 with hr0
  have hr0gt : 1 < r0 := by
    rw [hr0]
    nlinarith
  have hr0eq : r0 ^ 2 - u * r0 + 1 = 0 := by
    rw [hr0]
    nlinarith [htsq]
  set r := if 0 ≤ s then r0 else -r0 with hrdef
  have hrsq : r ^ 2 = r0 ^ 2 := by
    rw [hrdef]
    split <;> ring
  have hsr : s * r = u * r0 := by
    rw [hrdef, hu]
    split
    · rename_i h
      rw [abs_of_nonneg h]
    · rename_i h
      rw [abs_of_neg (lt_of_not_ge h)]
      ring
  have hreq : r ^ 2 - s * r + 1 = 0 := by
    rw [hrsq, hsr]
    exact hr0eq
  have hdet0 : (r • (1 : Matrix (Fin 3) (Fin 3) ℝ) - Q).det = 0 := by
    rw [det_smul_one_sub_fin_three, trace_adjugate_isomMatrix]
    have hts : Q.trace = s + Q.det := by rw [hs]; ring
    rw [hts]
    linear_combination (r - Q.det) * hreq + r * hcc
  have := sq_eq_one_of_det_smul_sub_eq_zero (isomMatrix_orthogonal A) hdet0
  rw [hrsq] at this
  nlinarith

/-- A divisor of `1`, `2`, `3`, `4` or `6` is again one of these numbers. -/
theorem order_cases_of_dvd {n k : ℕ} (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6) (h : n ∣ k) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  have hkpos : 0 < k := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hle : n ≤ k := Nat.le_of_dvd hkpos h
  have hk6 : k ≤ 6 := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hn6 : n ≤ 6 := le_trans hle hk6
  interval_cases n <;> revert h <;> rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ### The crystallographic restriction theorem -/

/-- **Crystallographic restriction theorem.** Every element of the point group of a
three-dimensional crystallographic group has order `1`, `2`, `3`, `4` or `6`. -/
theorem crystallographic_restriction {G : Subgroup (EuclideanIsom 3)}
    (hG : IsCrystallographicGroup G) {A : E 3 ≃ₗᵢ[ℝ] E 3} (hA : A ∈ pointGroup G) :
    orderOf A = 1 ∨ orderOf A = 2 ∨ orderOf A = 3 ∨ orderOf A = 4 ∨ orderOf A = 6 := by
  set Q := isomMatrix A with hQdef
  have hQorth : Qᵀ * Q = 1 := isomMatrix_orthogonal A
  have hc : Q.det = 1 ∨ Q.det = -1 := by
    have hsq := det_isomMatrix_sq A
    exact mul_self_eq_one_iff.mp (by rw [← sq]; exact hsq)
  obtain ⟨m, hm⟩ := exists_int_trace hG hA
  -- `s = trace - det` is an integer of absolute value at most `2`
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Q.trace - Q.det = (n : ℝ) := by
    rcases hc with h | h
    · exact ⟨m - 1, by rw [hm, h]; push_cast; ring⟩
    · exact ⟨m + 1, by rw [hm, h]; push_cast; ring⟩
  have habs : |((n : ℝ))| ≤ 2 := by
    rw [← hn]
    exact abs_trace_sub_det_le_two A
  have hnabs : |n| ≤ 2 := by
    have : ((|n| : ℤ) : ℝ) ≤ ((2 : ℤ) : ℝ) := by push_cast; simpa using habs
    exact_mod_cast this
  have hs : Q.trace - Q.det = -2 ∨ Q.trace - Q.det = -1 ∨ Q.trace - Q.det = 0 ∨
      Q.trace - Q.det = 1 ∨ Q.trace - Q.det = 2 := by
    have hn5 : n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 := by
      have := abs_le.mp hnabs
      omega
    rcases hn5 with h | h | h | h | h <;> rw [hn, h] <;> norm_num
  have hpow := exists_pow_eq_one_of_char_eq hQorth hc hs (isomMatrix_char_eq A)
  have hAk : ∀ k : ℕ, Q ^ k = 1 → A ^ k = 1 := by
    intro k hk
    apply isomMatrix_injective
    rw [isomMatrix_pow, hk, isomMatrix_one]
  rcases hpow with h | h | h | h | h
  · exact order_cases_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hAk 1 h))
  · exact order_cases_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hAk 2 h))
  · exact order_cases_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hAk 3 h))
  · exact order_cases_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hAk 4 h))
  · exact order_cases_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hAk 6 h))

end SpaceGroupsCrystRestriction

open SpaceGroupsCrystRestriction

theorem solution {G : Subgroup (EuclideanIsom 3)} (hG : IsCrystallographicGroup G)
    {A : E 3 ≃ₗᵢ[ℝ] E 3} (hA : A ∈ pointGroup G) :
    orderOf A = 1 ∨ orderOf A = 2 ∨ orderOf A = 3 ∨ orderOf A = 4 ∨ orderOf A = 6 :=
  crystallographic_restriction hG hA
