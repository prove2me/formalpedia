-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.coarsen_tangentPushforward_replicate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:46.771579+00:00
-- url     : https://prove2.me/submissions/71882116-b713-4ae0-9b5d-6e8568af795c

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_Replication
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_replicate_tangentPushforward_apply
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_tangentPushforward_apply
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
theorem _root_.solution (m : ℕ) (hm : 0 < m)
    (u : tangentSpace (α := α)) :
    (coarsen (α := α) m hm).tangentPushforward
      ((replicate (α := α) m hm).tangentPushforward u) = u := by
  classical
  ext a
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  set q : tangentSpace (α := α × Fin m) := (replicate (α := α) m hm).tangentPushforward u
  have hq (b : α × Fin m) : (q : α × Fin m → ℝ) b = (u : α → ℝ) b.1 / m := by
    rcases b with ⟨a', i⟩
    simpa [q] using (replicate_tangentPushforward_apply (α := α) m hm u a' i)
  calc
    ((coarsen (α := α) m hm).tangentPushforward q : α → ℝ) a
        = ∑ b with b.1 = a, (q : α × Fin m → ℝ) b := by
              simpa [coarsen, q] using
                (MarkovMorphism.deterministic_tangentPushforward_apply (α := α × Fin m) (β := α)
                  (g := Prod.fst) (hg := fun a => ⟨(a, ⟨0, hm⟩), rfl⟩) q a)
    _ = ∑ b : α × Fin m, if b.1 = a then (q : α × Fin m → ℝ) b else 0 := by
          simpa using
            (Finset.sum_filter
              (s := (Finset.univ : Finset (α × Fin m)))
              (p := fun b : α × Fin m => b.1 = a)
              (f := fun b => (q : α × Fin m → ℝ) b))
    _ = ∑ b : α × Fin m, if b.1 = a then (u : α → ℝ) b.1 / m else 0 := by
          simp [hq]
    _ = (u : α → ℝ) a := by
          have : (m : ℝ) * ((u : α → ℝ) a * (m : ℝ)⁻¹) = (u : α → ℝ) a := by
            calc
              (m : ℝ) * ((u : α → ℝ) a * (m : ℝ)⁻¹)
                  = (u : α → ℝ) a * ((m : ℝ) * (m : ℝ)⁻¹) := by
                      simp [mul_assoc, mul_comm]
              _ = (u : α → ℝ) a := by simp [hm0]
          simpa [Fintype.sum_prod_type, Finset.sum_const,
            Finset.card_univ, div_eq_mul_inv] using this
end LeanPool.CencovPetz.MarkovMorphism
