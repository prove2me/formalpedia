-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.merge_pushforward_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:48.419968+00:00
-- url     : https://prove2.me/submissions/c46d7ebd-0153-4eae-8769-f5a34392b400

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_Splitting
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_split_pushforward_apply
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
open LeanPool.CencovPetz.MarkovMorphism
variable {α : Type u} [Fintype α]
variable (m : α → ℕ) (hm : ∀ a, 0 < m a)
namespace LeanPool.CencovPetz.MarkovMorphism
theorem _root_.solution (p : Simplex α) :
    (merge (α := α) m hm).pushforward ((split (α := α) m hm).pushforward p) = p := by
  classical
  ext a
  have hm_ne : (m a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm a))
  -- Expand `merge` pushforward, rewrite the sigma-sum, and evaluate the resulting constant sum.
  calc
    ((merge (α := α) m hm).pushforward ((split (α := α) m hm).pushforward p)).p a
        = ∑ b : SplitTarget (α := α) m,
            ((split (α := α) m hm).pushforward p).p b * if b.1 = a then (1 : ℝ) else 0 := by
              simp [MarkovMorphism.pushforward_apply, merge]
    _ = ∑ x : α, ∑ i : Fin (m x),
            ((split (α := α) m hm).pushforward p).p ⟨x, i⟩ * if x = a then (1 : ℝ) else 0 := by
          simpa [SplitTarget] using
            (Fintype.sum_sigma (f := fun b : SplitTarget (α := α) m =>
              ((split (α := α) m hm).pushforward p).p b * if b.1 = a then (1 : ℝ) else 0))
    _ = ∑ x : α, if x = a
          then ∑ i : Fin (m x),
            ((split (α := α) m hm).pushforward p).p ⟨x, i⟩
          else 0 := by
          simp_all
    _ = ∑ i : Fin (m a), ((split (α := α) m hm).pushforward p).p ⟨a, i⟩ := by
          -- Only the `x = a` term survives.
          simp [eq_comm]
    _ = ∑ _i : Fin (m a), p.p a / (m a : ℝ) := by
          simp only [split_pushforward_apply]
    _ = p.p a := by
          -- `m a` copies, each `p(a)/m(a)`.
          have :
              (∑ _i : Fin (m a), p.p a / (m a : ℝ)) =
                (m a : ℝ) * (p.p a / (m a : ℝ)) := by
            classical
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          -- Cancel `m a`.
          calc
            (∑ _i : Fin (m a), p.p a / (m a : ℝ))
                = (m a : ℝ) * (p.p a / (m a : ℝ)) := this
            _ = p.p a := by
                  field_simp [hm_ne]
end LeanPool.CencovPetz.MarkovMorphism
