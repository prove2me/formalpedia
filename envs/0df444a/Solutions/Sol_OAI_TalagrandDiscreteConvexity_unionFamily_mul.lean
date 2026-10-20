-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.unionFamily_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:02:05.294204+00:00
-- url     : https://prove2.me/submissions/faa8a176-8249-4271-8900-d1b6cacd7468

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/UnionTuples.lean:L44-L73
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.unionFamily_mul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_SignedArrays
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_ProductProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_LabelCoupling
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_MandatoryCoupling
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_UnionTuples

-- ---- from OAI.Combinatorics.DiscreteConvexity.UnionTuples ----
namespace OAI

/-!
# Grouping and repeating union tuples

Grouping `a * b` entries into `a` rows of length `b` preserves exactly the
possible unions. Repetition is allowed throughout, as in the definition of
the exceptional family. No positivity assumption is needed for grouping.
-/

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem unionTuple_flatten {a b : ℕ} (f : Fin a → Fin b → Finset α) :
    unionTuple (flattenTuple f) = unionTuple (fun i => unionTuple (f i)) := by
  ext x
  simp only [mem_unionTuple]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨(finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2, ht⟩
  · rintro ⟨i, j, hij⟩
    refine ⟨finProdFinEquiv (i, j), ?_⟩
    simpa only [flattenTuple, Equiv.symm_apply_apply] using hij

omit [Fintype α] in
theorem unionTuple_rows {a b : ℕ} (f : Fin (a * b) → Finset α) :
    unionTuple (fun i : Fin a => unionTuple (fun j : Fin b => f (finProdFinEquiv (i, j)))) =
      unionTuple f := by
  rw [← unionTuple_flatten]
  apply congrArg (fun g : Fin (a * b) → Finset α => unionTuple g)
  funext t
  exact congrArg f (finProdFinEquiv.apply_symm_apply t)

/-- Iterated unions are exactly unions of the product number of entries. -/
theorem unionFamily_mul (a b : ℕ) (D : Family α) :
    unionFamily a (unionFamily b D) = unionFamily (a * b) D := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨f, hf, hfS⟩ := mem_unionFamily.mp hS
    have hrows : ∀ i : Fin a, ∃ g : Fin b → Finset α,
        (∀ j, g j ∈ D) ∧ unionTuple g = f i :=
      fun i => mem_unionFamily.mp (hf i)
    choose g hg hgUnion using hrows
    apply mem_unionFamily.mpr
    refine ⟨flattenTuple g, ?_, ?_⟩
    · intro t
      exact hg (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2
    · rw [unionTuple_flatten]
      have hfun : (fun i => unionTuple (g i)) = f := funext hgUnion
      rw [hfun]
      exact hfS
  · intro hS
    obtain ⟨f, hf, hfS⟩ := mem_unionFamily.mp hS
    apply mem_unionFamily.mpr
    refine ⟨fun i : Fin a => unionTuple (fun j : Fin b => f (finProdFinEquiv (i, j))),
      ?_, ?_⟩
    · intro i
      exact mem_unionFamily.mpr
        ⟨fun j => f (finProdFinEquiv (i, j)), fun j => hf _, rfl⟩
    · rw [unionTuple_rows]
      exact hfS

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.unionFamily_mul := @_root_.OAI.TalagrandDiscreteConvexity.unionFamily_mul
