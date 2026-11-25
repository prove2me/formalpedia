-- Prove2me | solution 1 for MooreGraphs.adjMatrix_sq_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:20:34.387013+00:00
-- url     : https://prove2.me/submissions/947fbb9d-adb7-4a47-b9f4-36757a891a5d

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution [DecidableEq V] {n k : ℕ} (hsrg : G.IsSRGWith n k 0 1) :
    adjMatrix ℝ G ^ 2 + adjMatrix ℝ G - ((k : ℝ) - 1) • (1 : Matrix V V ℝ) =
      Matrix.of fun _ _ => 1 := by
  rw [hsrg.matrix_eq]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.natCast_apply]
  · by_cases h : G.Adj i j <;> simp [hij, h, Matrix.one_apply_ne hij, Matrix.natCast_apply]
end MooreGraphs
