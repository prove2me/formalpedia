-- Prove2me | solution 1 for MooreGraphs.trace_sq_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:24:19.107827+00:00
-- url     : https://prove2.me/submissions/6a8bdec3-ffe5-46f0-8672-e8099a81bcf9

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
omit [Fintype V] [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution {W : Type*} [Fintype W] [DecidableEq W] {A : Matrix W W ℝ}
    (hA : A.IsHermitian) : (A ^ 2).trace = ∑ i, hA.eigenvalues i ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp
end MooreGraphs
