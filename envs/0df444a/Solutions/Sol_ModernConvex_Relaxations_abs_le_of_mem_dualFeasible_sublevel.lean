-- Prove2me | solution 1 for ModernConvex.Relaxations.abs_le_of_mem_dualFeasible_sublevel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:35:22.109546+00:00
-- url     : https://prove2.me/submissions/38acba8c-370c-4186-9c83-4e3e5cd0ba4c

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

/-!
# The dual spectrahedron is bounded on a sublevel set

The Max-Cut SDP dual is `minimize f(λ) = (1/4)(Σ_{i,j} a_ij + Σ_i λ_i)` over the spectrahedron
`X = {λ | a + diag λ ⪰ 0}`. `X` is unbounded above, but a minimizer never leaves the sublevel set
`{λ ∈ X | Σ_i λ_i ≤ U}`, and that set **is** bounded: feasibility forces `λ_i ≥ -a_ii`, since the
diagonal of a positive semidefinite matrix is nonnegative, and then
`λ_i = Σ_j λ_j - Σ_{j≠i} λ_j ≤ U + Σ_{j≠i} a_jj`.

So the sublevel set sits in the box `Π_i [-a_ii, U + Σ_{j≠i} a_jj]`, which is compact. This is the
"bounded convex body" hypothesis that Bubeck's ellipsoid theorem
(`ConvexOptAlg.Ellipsoid.theorem_2_4`) needs, and it costs no analysis beyond the sign of the
diagonal of a semidefinite matrix.
-/

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- Feasibility forces each diagonal dual variable up: `-a_ii ≤ λ_i`. -/
theorem le_of_mem_dualFeasible {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ} {lam : Fin n → ℝ}
    (h : (a + Matrix.diagonal lam).PosSemidef) (i : Fin n) : -(a i i) ≤ lam i := by
  have hd : (0 : ℝ) ≤ a i i + lam i := by
    have h' := h.diag_nonneg (i := i)
    simpa [Matrix.add_apply, Matrix.diagonal_apply_eq] using h'
  linarith

/-- On a sublevel set the dual variables are also bounded above. -/
theorem le_of_mem_dualFeasible_sublevel {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ}
    {lam : Fin n → ℝ} (h : (a + Matrix.diagonal lam).PosSemidef) {U : ℝ}
    (hlev : ∑ j, lam j ≤ U) (i : Fin n) :
    lam i ≤ U + ∑ j ∈ Finset.univ.erase i, a j j := by
  have hge : ∀ j ∈ Finset.univ.erase i, -(a j j) ≤ lam j := fun j _ =>
    le_of_mem_dualFeasible h j
  have hsum : ∑ j ∈ Finset.univ.erase i, (-(a j j)) ≤ ∑ j ∈ Finset.univ.erase i, lam j :=
    Finset.sum_le_sum hge
  rw [Finset.sum_neg_distrib] at hsum
  have hsplit : lam i + ∑ j ∈ Finset.univ.erase i, lam j = ∑ j, lam j :=
    Finset.add_sum_erase _ (fun j => lam j) (Finset.mem_univ i) ▸ rfl
  linarith

/-- **The sublevel set of the dual is bounded**: every dual feasible `λ` with `Σ_i λ_i ≤ U` lies
in the box `Π_i [-a_ii, U + Σ_{j≠i} a_jj]`. -/
theorem abs_le_of_mem_dualFeasible_sublevel_proof {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ}
    {lam : Fin n → ℝ} (h : (a + Matrix.diagonal lam).PosSemidef) {U : ℝ}
    (hlev : ∑ j, lam j ≤ U) (i : Fin n) :
    lam i ∈ Set.Icc (-(a i i)) (U + ∑ j ∈ Finset.univ.erase i, a j j) :=
  ⟨le_of_mem_dualFeasible h i, le_of_mem_dualFeasible_sublevel h hlev i⟩

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {a : Matrix (Fin n) (Fin n) ℝ}
    {lam : Fin n → ℝ} (h : (a + Matrix.diagonal lam).PosSemidef) {U : ℝ}
    (hlev : ∑ j, lam j ≤ U) (i : Fin n) :
    lam i ∈ Set.Icc (-(a i i)) (U + ∑ j ∈ Finset.univ.erase i, a j j) :=
  ModernConvex.Relaxations.abs_le_of_mem_dualFeasible_sublevel_proof h hlev i
