-- Prove2me | solution 1 for LeanPool.CencovPetz.Simplex.continuous_fisherBilin_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:19.238467+00:00
-- url     : https://prove2.me/submissions/a4752417-0c99-4891-9a51-350b8840c484

module
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_FisherContinuity
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_continuous_eval
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_p_ne_zero
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
open LeanPool.CencovPetz.Simplex
variable {α : Type*} [Fintype α]
namespace LeanPool.CencovPetz.Simplex
theorem _root_.solution (u v : tangentSpace (α := α)) :
    Continuous fun p : Simplex α => fisherBilin p u v := by
  classical
  have hterm :
      ∀ a : α,
        Continuous fun p : Simplex α => ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a := by
    intro a
    have hEval : Continuous fun p : Simplex α => p.p a :=
      Simplex.continuous_eval (α := α) a
    have hInv : Continuous fun p : Simplex α => (p.p a)⁻¹ :=
      hEval.inv₀ (fun p => p.p_ne_zero a)
    have hMul :
        Continuous fun p : Simplex α => (((u : α → ℝ) a) * ((v : α → ℝ) a)) * (p.p a)⁻¹ :=
      continuous_const.mul hInv
    simpa [div_eq_mul_inv, mul_assoc] using hMul
  have hsum :
      Continuous fun p : Simplex α =>
        ∑ a : α, ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a := by
    simpa using
      (continuous_finsetSum (s := (Finset.univ : Finset α))
        (f := fun a (p : Simplex α) => ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a)
        (by
          simp_all))
  simpa [fisherBilin] using hsum
end LeanPool.CencovPetz.Simplex
