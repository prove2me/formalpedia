-- Prove2me | solution 1 for LeanPool.CencovPetz.fisherBilin_pushforward_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:23:21.924262+00:00
-- url     : https://prove2.me/submissions/493c7c65-bda7-4aee-ac5c-4b8950947c69

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_SufficientStatistic
public import Theorems.Thm_LeanPool_CencovPetz_tangentPushforward_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_pos
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply


attribute [local simp] LeanPool.CencovPetz.tangentPushforward_apply

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
namespace LeanPool.CencovPetz
theorem _root_.solution (g : α → β) (hg : Function.Surjective g)
    (p : Simplex α) (u : tangentSpace (α := α)) :
    fisherBilin (Simplex.pushforward (α := α) (β := β) g hg p)
        (tangentPushforward (α := α) (β := β) g u)
        (tangentPushforward (α := α) (β := β) g u)
      ≤ fisherBilin p u u := by
  classical
  -- Fiberwise, use Titu's lemma / Engel form.
  have hb (b : β) :
      ((∑ a with g a = b, ((u : α → ℝ) a)) ^ 2) / (∑ a with g a = b, p.p a)
        ≤ ∑ a with g a = b, (((u : α → ℝ) a) ^ 2) / p.p a := by
    -- Convert the filtered sums to explicit finset sums over the fiber, then apply the lemma.
    simpa using
      (Finset.sq_sum_div_le_sum_sq_div (s := (Finset.univ.filter fun a : α => g a = b))
        (f := fun a => (u : α → ℝ) a) (g := fun a => p.p a)
        (hg := fun a _ => p.pos a))
  -- Sum the inequalities over `b`.
  have hsum :
      (∑ b : β, ((∑ a with g a = b, ((u : α → ℝ) a)) ^ 2) / (∑ a with g a = b, p.p a))
        ≤ ∑ b : β, ∑ a with g a = b, (((u : α → ℝ) a) ^ 2) / p.p a := by
    simpa using (Finset.sum_le_sum fun b _ => hb b)
  -- Collapse the right-hand side back to a total sum over `a`.
  have hfib_sq :
      (∑ b : β, ∑ a with g a = b, (((u : α → ℝ) a) ^ 2) / p.p a)
        = ∑ a : α, (((u : α → ℝ) a) ^ 2) / p.p a := by
    simpa using
      (Finset.sum_fiberwise (s := (Finset.univ : Finset α)) (g := g)
        (f := fun a => (((u : α → ℝ) a) ^ 2) / p.p a))
  -- Rewrite both sides as Fisher forms.
  -- LHS: Fisher on β after pushforward.
  have hL :
      fisherBilin (Simplex.pushforward (α := α) (β := β) g hg p)
          (tangentPushforward (α := α) (β := β) g u)
          (tangentPushforward (α := α) (β := β) g u)
        = ∑ b : β, ((∑ a with g a = b, ((u : α → ℝ) a)) ^ 2) / (∑ a with g a = b, p.p a) := by
    -- Expand, then use the pushforward definitions.
    simp [fisherBilin.apply, Simplex.pushforward_apply, tangentPushforward_apply, pow_two]
  have hR :
      fisherBilin p u u = ∑ a : α, (((u : α → ℝ) a) ^ 2) / p.p a := by
    simp [fisherBilin.apply, pow_two]
  -- Assemble.
  simp_all
end LeanPool.CencovPetz
