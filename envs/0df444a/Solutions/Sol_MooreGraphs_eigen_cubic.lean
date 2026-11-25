-- Prove2me | solution 1 for MooreGraphs.eigen_cubic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:25:20.442611+00:00
-- url     : https://prove2.me/submissions/5047b58c-80d9-4d57-898f-542c6e593e89

module
public import Mathlib
public import Definitions.Def_MooreLib_MooreGraphsAux
public import Theorems.Thm_MooreGraphs_adjMatrix_sq_add_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Matrix
open MooreGraphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace MooreGraphs
theorem _root_.solution {n k : ℕ} (hsrg : G.IsSRGWith n k 0 1) {μ : ℝ}
    {x : V → ℝ} (hx0 : x ≠ 0) (hx : adjMatrix ℝ G *ᵥ x = μ • x) :
    (μ ^ 2 + μ - (k - 1)) * (μ - k) = 0 := by
  classical
  set A := adjMatrix ℝ G
  set c := μ ^ 2 + μ - (k - 1)
  have hB : (A ^ 2 + A - ((k : ℝ) - 1) • (1 : Matrix V V ℝ)) *ᵥ x = c • x := by
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, pow_two, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_smul, hx, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp [c, Pi.smul_apply]; ring
  rw [adjMatrix_sq_add_eq G hsrg] at hB
  have hconst : c • x = Function.const V (∑ j, x j) := by
    rw [← hB]; ext i; simp [Matrix.mulVec, dotProduct]
  have hAc : A *ᵥ (c • x) = (k : ℝ) • (c • x) := by
    rw [hconst]; ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact adjMatrix_mulVec_const_apply_of_regular hsrg.regular
  rw [Matrix.mulVec_smul, hx, smul_smul, smul_smul, ← sub_eq_zero, ← sub_smul] at hAc
  have := (smul_eq_zero.1 hAc).resolve_right hx0
  linear_combination this
end MooreGraphs
