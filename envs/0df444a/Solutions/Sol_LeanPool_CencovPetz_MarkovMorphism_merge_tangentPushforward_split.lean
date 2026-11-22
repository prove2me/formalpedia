-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.merge_tangentPushforward_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:41.46243+00:00
-- url     : https://prove2.me/submissions/ace4497c-e257-4751-a591-84d5470edb82

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_Splitting
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_split_tangentPushforward_apply
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
theorem _root_.solution (u : tangentSpace (α := α)) :
    (merge (α := α) m hm).tangentPushforward ((split (α := α) m hm).tangentPushforward u) = u := by
  classical
  ext a
  have hm_ne : (m a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm a))
  calc
    ((merge (α := α) m hm).tangentPushforward
        ((split (α := α) m hm).tangentPushforward u) :
        α → ℝ) a
        = ∑ b : SplitTarget (α := α) m,
            (((split (α := α) m hm).tangentPushforward u : SplitTarget (α := α) m → ℝ) b) *
              if b.1 = a then (1 : ℝ) else 0 := by
              simp [MarkovMorphism.tangentPushforward_apply, merge]
    _ = ∑ x : α, ∑ i : Fin (m x),
            (((split (α := α) m hm).tangentPushforward u : SplitTarget (α := α) m → ℝ) ⟨x, i⟩) *
              if x = a then (1 : ℝ) else 0 := by
          simpa [SplitTarget] using
            (Fintype.sum_sigma (f := fun b : SplitTarget (α := α) m =>
              (((split (α := α) m hm).tangentPushforward u : SplitTarget (α := α) m → ℝ) b) *
                if b.1 = a then (1 : ℝ) else 0))
    _ = ∑ x : α, if x = a
          then ∑ i : Fin (m x),
            (((split (α := α) m hm).tangentPushforward u :
              SplitTarget (α := α) m → ℝ) ⟨x, i⟩)
          else 0 := by
          simp_all
    _ = ∑ i : Fin (m a),
          ((split (α := α) m hm).tangentPushforward u :
            SplitTarget (α := α) m → ℝ) ⟨a, i⟩ := by
          simp [eq_comm]
    _ = ∑ _i : Fin (m a), (u : α → ℝ) a / (m a : ℝ) := by
          simp only [split_tangentPushforward_apply]
    _ = (u : α → ℝ) a := by
          have :
              (∑ _i : Fin (m a), (u : α → ℝ) a / (m a : ℝ)) =
                (m a : ℝ) * ((u : α → ℝ) a / (m a : ℝ)) := by
            classical
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          calc
            (∑ _i : Fin (m a), (u : α → ℝ) a / (m a : ℝ))
                = (m a : ℝ) * ((u : α → ℝ) a / (m a : ℝ)) := this
            _ = (u : α → ℝ) a := by
                  field_simp [hm_ne]
end LeanPool.CencovPetz.MarkovMorphism
