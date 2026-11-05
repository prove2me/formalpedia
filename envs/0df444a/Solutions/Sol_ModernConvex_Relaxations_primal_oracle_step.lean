-- Prove2me | solution 1 for ModernConvex.Relaxations.primal_oracle_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:03.642286+00:00
-- url     : https://prove2.me/submissions/ce45c8ff-ca7b-49ce-a49d-5e294e16f813

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

/-!
# The separation oracle for the Max-Cut SDP dual

The Max-Cut semidefinite relaxation has the dual

  `minimize f(λ) = (1/4)(Σ_{i,j} a_ij + Σ_i λ_i)   subject to   a + diag λ ⪰ 0`,

whose feasible set `X = {λ | a + diag λ ⪰ 0}` is a spectrahedron. An ellipsoid-method run on
`X` needs, at every centre `λ`, exactly one of two answers:

* `λ ∈ X`, and then a subgradient of `f` at `λ`; or
* `λ ∉ X`, and then a vector `w ≠ 0` with `(μ - λ) ⬝ w ≤ 0` for all `μ ∈ X`.

This file supplies the second. The certificate is a **negative direction**: since `a + diag λ` is
not positive semidefinite there is `v` with `v ⬝ᵥ ((a + diag λ) *ᵥ v) < 0`, and then
`w := -(v_i²)_i` separates, because for feasible `μ`

  `(μ - λ) ⬝ w = v ⬝ᵥ ((a + diag λ) *ᵥ v) - v ⬝ᵥ ((a + diag μ) *ᵥ v) < 0`.

Every quantity is a finite sum of products of the data, so the certificate is rational whenever
`a` and `λ` are. The elimination algorithm supplies `v`; this file turns `v` into the separating
hyperplane the ellipsoid run consumes.
-/

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- Applying a diagonal matrix: `(diag λ *ᵥ v) i = λ i * v i`. -/
theorem diagonal_mulVec_apply {n : ℕ} (lam v : Fin n → ℝ) (i : Fin n) :
    (Matrix.diagonal lam *ᵥ v) i = lam i * v i := by
  rw [Matrix.mulVec_apply_eq_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hji), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The quadratic form of `a + diag λ` splits as the quadratic form of `a` plus `Σ_i λ_i v_i²`. -/
theorem dotProduct_diagonal_add {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ)
    (v : Fin n → ℝ) :
    v ⬝ᵥ ((a + Matrix.diagonal lam) *ᵥ v) = v ⬝ᵥ (a *ᵥ v) + ∑ i, lam i * (v i) ^ 2 := by
  rw [Matrix.add_mulVec, dotProduct_add]
  congr 1
  rw [dotProduct]
  simp only [diagonal_mulVec_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **A negative direction gives a separating hyperplane.** If `v` has negative quadratic form
for `a + diag λ` and `μ` is dual feasible, then `w := -(v_i²)_i` satisfies
`(μ - λ) ⬝ w ≤ 0`. -/
theorem diag_separation {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    {lam mu : Fin n → ℝ} {v : Fin n → ℝ}
    (hneg : v ⬝ᵥ ((a + Matrix.diagonal lam) *ᵥ v) < 0)
    (hpos : (a + Matrix.diagonal mu).PosSemidef) :
    (fun i => (mu - lam) i) ⬝ᵥ (fun i => -((v i) ^ 2)) ≤ 0 := by
  have hmu : 0 ≤ v ⬝ᵥ ((a + Matrix.diagonal mu) *ᵥ v) :=
    hpos.dotProduct_mulVec_nonneg v
  rw [dotProduct_diagonal_add] at hmu hneg
  rw [dotProduct]
  simp only [Pi.sub_apply, Pi.neg_apply]
  have hsum : ∑ i, (mu i - lam i) * -((v i) ^ 2)
      = -((∑ i, mu i * (v i) ^ 2) - ∑ i, lam i * (v i) ^ 2) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  linarith

/-- A non-positive-semidefinite symmetric matrix has a vector of negative quadratic form. -/
theorem exists_neg_vector_of_not_posSemidef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.IsHermitian) (h : ¬ M.PosSemidef) : ∃ v : Fin n → ℝ, v ⬝ᵥ (M *ᵥ v) < 0 := by
  by_contra hcon
  push_neg at hcon
  exact h (posSemidef_iff_dotProduct_mulVec.mpr ⟨hM, hcon⟩)

/-- **The separation-oracle step for the dual spectrahedron.** For every `λ`, either
`a + diag λ ⪰ 0`, or there is `w ≠ 0` with `(μ - λ) ⬝ w ≤ 0` for every dual feasible `μ`.

This is exactly the answer an ellipsoid run on `X = {λ | a + diag λ ⪰ 0}` consumes. -/
theorem oracle_step {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} (ha : a.IsHermitian)
    (lam : Fin n → ℝ) :
    (a + Matrix.diagonal lam).PosSemidef ∨
      ∃ w : Fin n → ℝ, w ≠ 0 ∧ ∀ mu : Fin n → ℝ,
        (a + Matrix.diagonal mu).PosSemidef → (fun i => (mu - lam) i) ⬝ᵥ w ≤ 0 := by
  by_cases hPSD : (a + Matrix.diagonal lam).PosSemidef
  · exact Or.inl hPSD
  · right
    have hHerm : (a + Matrix.diagonal lam).IsHermitian :=
      ha.add (Matrix.isHermitian_diagonal lam)
    obtain ⟨v, hv⟩ := exists_neg_vector_of_not_posSemidef hHerm hPSD
    refine ⟨fun i => -((v i) ^ 2), ?_, ?_⟩
    · intro hw
      have hv0 : v = 0 := by
        funext i
        have hi : -((v i) ^ 2) = 0 := by
          have := congrFun hw i
          simpa using this
        have h2 : (v i) * (v i) = 0 := by
          rw [← sq]
          linarith
        exact mul_self_eq_zero.mp h2
      rw [hv0] at hv
      simpa using hv
    · intro mu hmu
      exact diag_separation a hv hmu

end ModernConvex.Relaxations

namespace ModernConvex.Relaxations

/-- The quadratic form of `Z` is the Frobenius pairing of `Z` with `v vᵀ`. -/
theorem dotProduct_mulVec_eq_sum_sum {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (Z *ᵥ v) = ∑ i, ∑ j, Z i j * (v i * v j) := by
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The separation step for the semidefinite constraint.** If `X` is symmetric and not positive
semidefinite, then `W := −v vᵀ` is a nonzero matrix whose Frobenius pairing with `Y − X` is
nonpositive for every positive semidefinite `Y`. -/
theorem primal_separation {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian)
    (h : ¬ X.PosSemidef) :
    ∃ W : Matrix (Fin n) (Fin n) ℝ, W ≠ 0 ∧
      ∀ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosSemidef →
        (∑ i, ∑ j, (Y - X) i j * W i j) ≤ 0 := by
  obtain ⟨v, hv⟩ := exists_neg_vector_of_not_posSemidef hX h
  refine ⟨fun i j => -(v i * v j), ?_, ?_⟩
  · intro hW
    have hv0 : v = 0 := by
      funext i
      have hi : -(v i * v i) = 0 := by
        have h := congrFun (congrFun hW i) i
        simpa using h
      have h2 : v i * v i = 0 := by linarith
      exact mul_self_eq_zero.mp h2
    rw [hv0] at hv
    simpa using hv
  · intro Y hY
    have hYq : 0 ≤ v ⬝ᵥ (Y *ᵥ v) := hY.dotProduct_mulVec_nonneg v
    rw [dotProduct_mulVec_eq_sum_sum] at hYq hv
    have hrow : ∀ i, (∑ j, (Y - X) i j * -(v i * v j))
        = -((∑ j, Y i j * (v i * v j)) - ∑ j, X i j * (v i * v j)) := by
      intro i
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.sub_apply]
      ring
    have hsplit : ∑ i, ∑ j, (Y - X) i j * -(v i * v j)
        = -((∑ i, ∑ j, Y i j * (v i * v j)) - ∑ i, ∑ j, X i j * (v i * v j)) := by
      simp only [hrow]
      rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib]
    rw [hsplit]
    linarith

/-- **The primal oracle step.** For every symmetric `X`: either `X ⪰ 0`, or there is a nonzero
matrix `W` separating `X` from the positive semidefinite cone by the Frobenius pairing. -/
theorem primal_oracle_step_proof {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    X.PosSemidef ∨
      ∃ W : Matrix (Fin n) (Fin n) ℝ, W ≠ 0 ∧
        ∀ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosSemidef →
          (∑ i, ∑ j, (Y - X) i j * W i j) ≤ 0 := by
  by_cases h : X.PosSemidef
  · exact Or.inl h
  · exact Or.inr (primal_separation hX h)

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    X.PosSemidef ∨
      ∃ W : Matrix (Fin n) (Fin n) ℝ, W ≠ 0 ∧
        ∀ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosSemidef →
          (∑ i, ∑ j, (Y - X) i j * W i j) ≤ 0 :=
  ModernConvex.Relaxations.primal_oracle_step_proof hX
