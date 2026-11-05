-- Prove2me | solution 1 for ModernConvex.Relaxations.isCompact_primalBodyVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:57:45.949919+00:00
-- url     : https://prove2.me/submissions/9cdda4b6-eee7-485e-a7d8-afb213a1ab0e

import Mathlib
import Definitions.Def_ModernConvex_MatrixVec
import Definitions.Def_ModernConvex_PrimalBody
import Theorems.Thm_ModernConvex_Relaxations_isClosed_posSemidef
import Theorems.Thm_ModernConvex_Relaxations_abs_entry_le_one

/-!
# The primal body of the Max-Cut SDP is compact

The primal body in ellipsoid coordinates is

  `K = {x : Fin (n*n) → ℝ | (finToMat x) ⪰ 0, ∀ i, (finToMat x) i i = 1}`.

It is closed (the positive semidefinite cone is closed and the diagonal constraints are affine),
bounded (every entry of a unit-diagonal semidefinite matrix has modulus at most one, so `‖x‖ ≤ 1`
in the sup norm), and convex; hence compact in the finite-dimensional space `Fin (n*n) → ℝ`.
Together with `I ∈ interior K` this supplies the `IsConvexBody` hypothesis of Bubeck's
ellipsoid theorem.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- `finToMat` is continuous. -/
theorem continuous_finToMat {n : ℕ} :
    Continuous fun x : Fin (n * n) → ℝ => finToMat x := by
  refine continuous_matrix fun i j => ?_
  exact continuous_apply _

/-- **The primal body is closed.** -/
theorem isClosed_primalBodyVec (n : ℕ) : IsClosed (primalBodyVec n) := by
  have h1 : IsClosed {x : Fin (n * n) → ℝ | (finToMat x).PosSemidef} :=
    isClosed_posSemidef.preimage continuous_finToMat
  have h2 : IsClosed {x : Fin (n * n) → ℝ | ∀ i, (finToMat x) i i = 1} := by
    have hset : {x : Fin (n * n) → ℝ | ∀ i, (finToMat x) i i = 1}
        = ⋂ i : Fin n, {x : Fin (n * n) → ℝ | (finToMat x) i i = 1} := by
      ext x
      simp
    rw [hset]
    exact isClosed_iInter fun i =>
      isClosed_eq (continuous_finToMat.matrix_elem i i) continuous_const
  exact h1.inter h2

/-- **The primal body is bounded**: every coordinate of every point has modulus at most one. -/
theorem norm_le_one_of_mem_primalBodyVec {n : ℕ} {x : Fin (n * n) → ℝ}
    (hx : x ∈ primalBodyVec n) : ‖x‖ ≤ 1 := by
  obtain ⟨hPSD, hdiag⟩ := hx
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
  intro k
  have h := abs_entry_le_one hPSD hdiag (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
  rw [finToMat, Matrix.of_apply, Equiv.apply_symm_apply] at h
  simpa [Real.norm_eq_abs] using h

/-- **The primal body is compact.** -/
theorem isCompact_primalBodyVec_proof (n : ℕ) : IsCompact (primalBodyVec n) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨isClosed_primalBodyVec n, ?_⟩
  exact (Metric.isBounded_closedBall (x := (0 : Fin (n * n) → ℝ)) (r := 1)).subset
    (fun x hx => by
      simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
      exact norm_le_one_of_mem_primalBodyVec hx)

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution (n : ℕ) : IsCompact (primalBodyVec n) :=
  ModernConvex.Relaxations.isCompact_primalBodyVec_proof n
