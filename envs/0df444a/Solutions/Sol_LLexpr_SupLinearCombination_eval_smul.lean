-- Prove2me | solution 1 for LLexpr.SupLinearCombination.eval_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:28.35861+00:00
-- url     : https://prove2.me/submissions/41585c68-a101-4d97-a3c1-32e715578b0d

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr

set_option autoImplicit true
@[expose] public section
public section
open LLexpr
open scoped BigOperators
variable {n : ℕ}
open LLexpr.SupLinearCombination
namespace LLexpr.SupLinearCombination
theorem _root_.solution {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] {r : ℝ} (hr : 0 ≤ r)
    (A : SupLinearCombination n) (x : Fin n → X) :
    (A.smul r).eval x = r • A.eval x := by
  classical
  unfold eval smul
  rw [Finset.sup'_image]
  change A.coeffs.sup' A.nonempty (fun a => Fintype.linearCombination ℝ x (r • a)) =
    r • A.coeffs.sup' A.nonempty (fun a => Fintype.linearCombination ℝ x a)
  simp_rw [map_smul]
  exact (map_finset_sup' (smulSupHom r hr) A.nonempty
    (fun a => Fintype.linearCombination ℝ x a)).symm
end LLexpr.SupLinearCombination
