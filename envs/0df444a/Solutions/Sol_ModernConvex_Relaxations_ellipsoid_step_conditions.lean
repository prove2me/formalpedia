-- Prove2me | solution 1 for ModernConvex.Relaxations.ellipsoid_step_conditions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:30:50.272718+00:00
-- url     : https://prove2.me/submissions/028046ed-9d14-4cb4-aada-3ed7d1f31e16

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_LinearOptimization_Subgradient

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
open Matrix
open scoped BigOperators

/-- The dual objective of the Max-Cut relaxation as a function of the dual vector. -/
noncomputable def dualObjective {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) → ℝ :=
  fun lam => (1 / 4) * ((∑ i, ∑ j, a i j) + ∑ i, lam i)

/-- The dual feasible set: the spectrahedron `{λ | a + diag λ ⪰ 0}`. -/
def dualFeasible {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {lam | (a + Matrix.diagonal lam).PosSemidef}

/-- **The subgradient branch.** At a dual feasible centre the constant vector `(1/4, …, 1/4)` is
a subgradient of the affine dual objective on the feasible set — the answer an ellipsoid run
needs when the centre is feasible. -/
theorem affine_subgradient {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) {c : Fin n → ℝ}
    (hc : c ∈ dualFeasible a) :
    LinearOptimization.IsSubgradientOn (dualObjective a) (dualFeasible a)
      (fun _ => (1 / 4 : ℝ)) c := by
  refine ⟨hc, fun b _ => ?_⟩
  have hp : (fun _ : Fin n => (1 / 4 : ℝ)) ⬝ᵥ (b - c) = (1 / 4) * ∑ i, (b i - c i) := by
    rw [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.sub_apply]
  have hsub : ∑ i, (b i - c i) = (∑ i, b i) - ∑ i, c i :=
    Finset.sum_sub_distrib (f := b) (g := c)
  simp only [dualObjective, hp, hsub]
  linarith

/-- **The separation branch.** At an infeasible centre there is a nonzero separating vector: the
answer an ellipsoid run needs when the centre lies outside the spectrahedron. -/
theorem oracle_infeasible_step {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} (ha : a.IsHermitian)
    {c : Fin n → ℝ} (hc : c ∉ dualFeasible a) :
    ∃ w : Fin n → ℝ, w ≠ 0 ∧ ∀ x ∈ dualFeasible a, (x - c) ⬝ᵥ w ≤ 0 := by
  rcases oracle_step ha c with hPSD | ⟨w, hw, hsep⟩
  · exact absurd hPSD hc
  · refine ⟨w, hw, fun x hx => ?_⟩
    have h := hsep x hx
    simpa [dualFeasible, Pi.sub_apply, dotProduct] using h

/-- **The two step conditions of the ellipsoid run**, discharged by the oracle: at every centre,
either the centre is feasible and the constant vector `(1/4, …, 1/4)` is a subgradient of the
dual objective, or the centre is infeasible and there is a nonzero separating vector.

These are exactly the two clauses of `ConvexOptAlg.Ellipsoid.IsEllipsoidRun` that depend on the
problem, so an ellipsoid run on the dual spectrahedron can be built from this oracle alone. -/
theorem ellipsoid_step_conditions_proof {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} (ha : a.IsHermitian)
    (c : Fin n → ℝ) :
    (c ∈ dualFeasible a →
        LinearOptimization.IsSubgradientOn (dualObjective a) (dualFeasible a)
          (fun _ => (1 / 4 : ℝ)) c) ∧
      (c ∉ dualFeasible a →
        ∃ w : Fin n → ℝ, w ≠ 0 ∧ ∀ x ∈ dualFeasible a, (x - c) ⬝ᵥ w ≤ 0) :=
  ⟨fun hc => affine_subgradient a hc, fun hc => oracle_infeasible_step ha hc⟩

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} (ha : a.IsHermitian)
    (c : Fin n → ℝ) :
    (c ∈ {lam : Fin n → ℝ | (a + Matrix.diagonal lam).PosSemidef} → LinearOptimization.IsSubgradientOn (fun lam : Fin n → ℝ => (1 / 4) * ((∑ i, ∑ j, a i j) + ∑ i, lam i)) {lam : Fin n → ℝ | (a + Matrix.diagonal lam).PosSemidef} (fun _ => (1 / 4 : ℝ)) c) ∧
      (c ∉ {lam : Fin n → ℝ | (a + Matrix.diagonal lam).PosSemidef} → ∃ w : Fin n → ℝ, w ≠ 0 ∧ ∀ x ∈ {lam : Fin n → ℝ | (a + Matrix.diagonal lam).PosSemidef}, (x - c) ⬝ᵥ w ≤ 0) :=
  ⟨fun hc => ModernConvex.Relaxations.ellipsoid_step_conditions_proof (a := a) ha c |>.1 hc,
   fun hc => ModernConvex.Relaxations.ellipsoid_step_conditions_proof (a := a) ha c |>.2 hc⟩
