-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.tupleWeightSum_le_allTupleWeightSum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:36:41.347609+00:00
-- url     : https://prove2.me/submissions/df710cb8-7305-4bd3-ab00-ccc5a7629d28

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringResidualTuples.lean:L117-L132
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.tupleWeightSum_le_allTupleWeightSum. The node keeps its source
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

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringResidualTuples ----
namespace OAI

/-!
# The total weight of residual tuples

We bound the sum over injective edge tuples by the sum over all edge tuples.
Splitting an unrestricted tuple into its first edge and its tail gives an
exact weighted recurrence. The per-union extension bound then controls every
step. No nonemptiness assumption on the edge family is needed.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

noncomputable section

/-- Discarding the injectivity restriction increases the sum of nonnegative weights. -/
theorem tupleWeightSum_le_allTupleWeightSum (H : Family V) {rho : ℝ}
    (hrho : 0 ≤ rho) (t : ℕ) :
    tupleWeightSum H rho t ≤ allTupleWeightSum H rho t := by
  classical
  calc
    tupleWeightSum H rho t =
        ∑ f ∈ Finset.univ.filter (fun f : Fin t → ↥H => Function.Injective f),
          rho ^ (allTupleUnion f).card := by
      exact (Finset.sum_subtype
        (p := fun f : Fin t → ↥H => Function.Injective f)
        (Finset.univ.filter (fun f : Fin t → ↥H => Function.Injective f))
        (fun f => by simp) (fun f => rho ^ (allTupleUnion f).card)).symm
    _ ≤ allTupleWeightSum H rho t := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun f _ _ => pow_nonneg hrho _)

end

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.tupleWeightSum_le_allTupleWeightSum := @_root_.OAI.TalagrandDiscreteConvexity.Covering.tupleWeightSum_le_allTupleWeightSum
