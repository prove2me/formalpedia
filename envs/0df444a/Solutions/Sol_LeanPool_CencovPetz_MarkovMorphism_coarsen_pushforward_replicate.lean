-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.coarsen_pushforward_replicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:50.515507+00:00
-- url     : https://prove2.me/submissions/23082455-aea7-4844-a0e2-f3cd15ccbeba

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_Replication
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_replicate_pushforward_apply
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_pushforward_apply
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
open LeanPool.CencovPetz.MarkovMorphism
namespace LeanPool.CencovPetz.MarkovMorphism
theorem _root_.solution (m : ℕ) (hm : 0 < m) (p : Simplex α) :
    (coarsen (α := α) m hm).pushforward ((replicate (α := α) m hm).pushforward p) = p := by
  classical
  ext a
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  set q : Simplex (α × Fin m) := (replicate (α := α) m hm).pushforward p
  have hq (b : α × Fin m) : q.p b = p.p b.1 / m := by
    rcases b with ⟨a', i⟩
    simpa [q] using (replicate_pushforward_apply (α := α) m hm p a' i)
  -- Coarsening is a deterministic pushforward along `Prod.fst`, so it sums `q` over the fiber.
  calc
    ((coarsen (α := α) m hm).pushforward q).p a
        = ∑ b with b.1 = a, q.p b := by
              simpa [coarsen, q] using
                (MarkovMorphism.deterministic_pushforward_apply (α := α × Fin m) (β := α)
                  (g := Prod.fst) (hg := fun a => ⟨(a, ⟨0, hm⟩), rfl⟩) q a)
    _ = ∑ b : α × Fin m, if b.1 = a then q.p b else 0 := by
          -- Convert a filtered sum to an `if`-sum.
          simpa using
            (Finset.sum_filter
              (s := (Finset.univ : Finset (α × Fin m)))
              (p := fun b : α × Fin m => b.1 = a)
              (f := fun b => q.p b))
    _ = ∑ b : α × Fin m, if b.1 = a then p.p b.1 / m else 0 := by
          simp [hq]
    _ = p.p a := by
          -- Split the sum over `α × Fin m` and evaluate.
          have : (m : ℝ) * (p.p a * (m : ℝ)⁻¹) = p.p a := by
            -- Rearrange to use `m * m⁻¹ = 1`.
            calc
              (m : ℝ) * (p.p a * (m : ℝ)⁻¹)
                  = p.p a * ((m : ℝ) * (m : ℝ)⁻¹) := by
                      simp [mul_assoc, mul_comm]
              _ = p.p a := by simp [hm0]
          simpa [Fintype.sum_prod_type, Finset.sum_const,
            Finset.card_univ, div_eq_mul_inv] using this
end LeanPool.CencovPetz.MarkovMorphism
