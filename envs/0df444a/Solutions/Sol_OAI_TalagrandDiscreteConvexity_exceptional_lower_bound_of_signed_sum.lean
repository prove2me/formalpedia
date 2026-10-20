-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.exceptional_lower_bound_of_signed_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:54:02.88349+00:00
-- url     : https://prove2.me/submissions/08c45bd1-2974-487b-bf1a-b66e886c825a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/ExceptionalWeightBound.lean:L21-L53
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.exceptional_lower_bound_of_signed_sum. The node keeps its source
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

-- ---- from OAI.Combinatorics.DiscreteConvexity.ExceptionalWeightBound ----
namespace OAI

/-!
# An exceptional-weight lower bound from a signed identity

Separating the empty subset in a vanishing signed sum bounds its weight by
the total unsigned weight of the nonempty subsets. This scalar argument does
not depend on how the weights or their signed identity were constructed.
-/

namespace TalagrandDiscreteConvexity

open scoped BigOperators

/-- A vanishing signed 32nd-power sum and an empty-subset value at least one
half force a lower bound on the sum of the nonempty squared weights. -/
theorem exceptional_lower_bound_of_signed_sum {V : Type*} [DecidableEq V]
    (S : Finset V) (b : Finset V → ℝ)
    (hsum : ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * b U ^ 32 = 0)
    (hb0 : (1 / 2 : ℝ) ≤ b ∅) :
    (1 / 2 : ℝ) ^ 32 ≤ ∑ U ∈ S.powerset.erase ∅, (b U ^ 2) ^ 16 := by
  have hpower (U : Finset V) : b U ^ 32 = (b U ^ 2) ^ 16 := by
    rw [← pow_mul]
  have hnonneg (U : Finset V) : 0 ≤ b U ^ 32 := by
    rw [hpower]
    exact pow_nonneg (sq_nonneg (b U)) 16
  have hsplit :
      (∑ U ∈ S.powerset.erase ∅, (-1 : ℝ) ^ U.card * b U ^ 32) +
        b ∅ ^ 32 = 0 := by
    simpa only [Finset.card_empty, pow_zero, one_mul] using
      (Finset.sum_erase_add S.powerset
        (fun U => (-1 : ℝ) ^ U.card * b U ^ 32)
        (Finset.empty_mem_powerset S)).trans hsum
  have hrest :
      (∑ U ∈ S.powerset.erase ∅, (-1 : ℝ) ^ U.card * b U ^ 32) =
        -(b ∅ ^ 32) := eq_neg_of_add_eq_zero_left hsplit
  calc
    (1 / 2 : ℝ) ^ 32 ≤ b ∅ ^ 32 :=
      pow_le_pow_left₀ (div_nonneg zero_le_one zero_le_two) hb0 32
    _ = |∑ U ∈ S.powerset.erase ∅, (-1 : ℝ) ^ U.card * b U ^ 32| := by
      rw [hrest, abs_neg, abs_of_nonneg (hnonneg ∅)]
    _ ≤ ∑ U ∈ S.powerset.erase ∅, |(-1 : ℝ) ^ U.card * b U ^ 32| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ U ∈ S.powerset.erase ∅, (b U ^ 2) ^ 16 := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [abs_mul, abs_neg_one_pow, one_mul, abs_of_nonneg (hnonneg U), hpower]

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.exceptional_lower_bound_of_signed_sum := @_root_.OAI.TalagrandDiscreteConvexity.exceptional_lower_bound_of_signed_sum
