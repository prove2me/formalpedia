-- Prove2me | solution 1 for ModernConvex.Relaxations.sdpValue_le_dual_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:10:23.786833+00:00
-- url     : https://prove2.me/submissions/6d46f3ff-2cea-4286-9b3e-c7447a91e18c

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

/-!
# Weak duality for the Max-Cut semidefinite relaxation

The Max-Cut SDP of Ben-Tal–Nemirovski (4.3.15) is

  `maximize (1/4) Σ_{i,j} a_ij (1 - X_ij)  s.t.  X ⪰ 0, X_ii = 1`,

and `ModernConvex.Relaxations.IsMaxcutSDPValue a v` says that `v` is its optimal value.

This file proves the two inequalities that turn a *certificate pair* — a feasible `X` and a
dual vector `λ` with `a + diagonal λ ⪰ 0` — into a two-sided bound on the optimal value:

* `maxcutRelaxationObjective_le_sdpValue`: every feasible `X` gives a **lower** bound;
* `sdpValue_le_dual`: every `λ` with `a + diag λ ⪰ 0` gives an **upper** bound
  `(1/4)(Σ_{i,j} a_ij + Σ_i λ_i)`.

Their difference is `(1/4) ⟨a + diag λ, X⟩`, so a solver that exhibits a pair with small
duality gap pins the optimal value. This is the interface every numerical SDP algorithm
feeds; no machine model is involved here.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- **The trace pairing of positive semidefinite matrices is nonnegative.** If `Z ⪰ 0` and
`X ⪰ 0` then `0 ≤ (Z * X).trace`. -/
theorem trace_mul_nonneg_of_posSemidef {n : ℕ} {Z X : Matrix (Fin n) (Fin n) ℝ}
    (hZ : Z.PosSemidef) (hX : X.PosSemidef) : 0 ≤ (Z * X).trace := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.nonneg
  have hZX : (Z * X).trace = (B * X * Matrix.conjTranspose B).trace := by
    conv_lhs => rw [hB, Matrix.star_eq_conjTranspose]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [hZX]
  exact (hX.mul_mul_conjTranspose_same B).trace_nonneg

/-- `Σ_{i,j} a_ij X_ij` is the trace of `a * X` for a symmetric `X`. -/
theorem sum_sum_mul_eq_trace_mul {n : ℕ} {a X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) : (∑ i, ∑ j, a i j * X i j) = (a * X).trace := by
  have hsymm : ∀ i j : Fin n, X j i = X i j := by
    intro i j
    simpa using (hX.apply j i).symm
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsymm i j]

/-- The identity matrix is feasible, with objective `(1/4)(Σ_{i,j} a_ij - Σ_i a_ii)`. -/
theorem maxcutRelaxationObjective_one {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) :
    maxcutRelaxationObjective a (1 : Matrix (Fin n) (Fin n) ℝ)
      = (1 / 4) * ((∑ i, ∑ j, a i j) - ∑ i, a i i) := by
  have hinner : ∀ i : Fin n, (∑ j, a i j * (1 - if i = j then (1 : ℝ) else 0))
      = (∑ j, a i j) - a i i := by
    intro i
    have hterm : ∀ j : Fin n, a i j * (1 - if i = j then (1 : ℝ) else 0)
        = a i j - (if i = j then a i j else 0) := by
      intro j
      by_cases h : i = j <;> simp [h]
    simp only [hterm, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_ite_eq]
    simp
  simp only [maxcutRelaxationObjective, Matrix.one_apply, hinner, Finset.sum_sub_distrib]

/-- **Primal bound.** Every feasible `X` gives a lower bound on the optimal SDP value. -/
theorem maxcutRelaxationObjective_le_sdpValue {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ}
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : IsUnitDiagPSD X) {S : ℝ}
    (hS : IsMaxcutSDPValue a S) : maxcutRelaxationObjective a X ≤ S :=
  hS.1 ⟨X, hX, rfl⟩

/-- **Weak duality, pointwise form.** For every `λ` with `a + diag λ ⪰ 0` and every feasible
`X`, the objective at `X` is at most `(1/4)(Σ_{i,j} a_ij + Σ_i λ_i)`.

Indeed `⟨a + diag λ, X⟩ = Σ_{i,j} a_ij X_ij + Σ_i λ_i ≥ 0` because the trace pairing of two
semidefinite matrices is nonnegative, and `Σ_{i,j} a_ij X_ij = (a * X).trace`. -/
theorem maxcutRelaxationObjective_le_dual {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ)
    (lam : Fin n → ℝ) (hdual : (a + Matrix.diagonal lam).PosSemidef)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : IsUnitDiagPSD X) :
    maxcutRelaxationObjective a X ≤ (1 / 4) * ((∑ i, ∑ j, a i j) + ∑ i, lam i) := by
  have hpair : 0 ≤ ((a + Matrix.diagonal lam) * X).trace :=
    trace_mul_nonneg_of_posSemidef hdual hX.1
  have hsplit : ((a + Matrix.diagonal lam) * X).trace
      = (∑ i, ∑ j, a i j * X i j) + ∑ i, lam i := by
    rw [Matrix.add_mul, Matrix.trace_add, sum_sum_mul_eq_trace_mul hX.1.isHermitian]
    congr 1
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul, hX.2, mul_one]
  have hkey : -(∑ i, lam i) ≤ ∑ i, ∑ j, a i j * X i j := by linarith
  have hobj : maxcutRelaxationObjective a X
      = (1 / 4) * ((∑ i, ∑ j, a i j) - ∑ i, ∑ j, a i j * X i j) := by
    simp only [maxcutRelaxationObjective]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hobj]
  linarith

/-- **Weak duality: the dual bound.** For every `λ` with `a + diag λ ⪰ 0`, the optimal value
of the Max-Cut SDP is at most `(1/4)(Σ_{i,j} a_ij + Σ_i λ_i)`. -/
theorem sdpValue_le_dual {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : IsMaxcutSDPValue a S) (lam : Fin n → ℝ)
    (hdual : (a + Matrix.diagonal lam).PosSemidef) :
    S ≤ (1 / 4) * ((∑ i, ∑ j, a i j) + ∑ i, lam i) := by
  have hupper : (1 / 4) * ((∑ i, ∑ j, a i j) + ∑ i, lam i) ∈ upperBounds
      (maxcutRelaxationObjective a '' {X | IsUnitDiagPSD X}) := by
    intro y hy
    obtain ⟨X, hX, rfl⟩ := hy
    exact maxcutRelaxationObjective_le_dual a lam hdual hX
  exact hS.2 hupper

end ModernConvex.Relaxations

namespace ModernConvex.Relaxations
open Matrix
open scoped BigOperators

/-- **Weak duality with a rational Gram certificate.** If `λ` comes with an explicit real matrix
`B` such that `Bᵀ B = a + diag λ`, then `(1/4)(Σ_{i,j} a_ij + Σ_i λ_i)` bounds the SDP value from
above. This is the form a numerical solver certifies: `B` is rational, the identity
`Bᵀ B = a + diag λ` is a finite rational identity, and the bound is then pure arithmetic. -/
theorem sdpValue_le_dual_gram {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : IsMaxcutSDPValue a S) (lam : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : Matrix.transpose B * B = a + Matrix.diagonal lam) :
    S ≤ (1 / 4) * ((∑ i, ∑ j, a i j) + ∑ i, lam i) := by
  refine sdpValue_le_dual hS lam ?_
  rw [← hB]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self (R := ℝ) B)

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : IsMaxcutSDPValue a S) (lam : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : Matrix.transpose B * B = a + Matrix.diagonal lam) :
    S ≤ (1 / 4) * ((∑ i, ∑ j, a i j) + ∑ i, lam i) :=
  ModernConvex.Relaxations.sdpValue_le_dual_gram hS lam B hB
