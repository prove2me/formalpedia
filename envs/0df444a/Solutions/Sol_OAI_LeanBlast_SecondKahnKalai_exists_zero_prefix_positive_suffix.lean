-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.exists_zero_prefix_positive_suffix
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:11:34.595256+00:00
-- url     : https://prove2.me/submissions/424adcd9-b140-4ef1-9311-da255952f9ce

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreeCovering.lean:L28-L52
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.exists_zero_prefix_positive_suffix. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreePotential
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeCovering

-- ---- from OAI.Combinatorics.GraphThreshold.TreeCovering ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Covering a probability tree by iterative reductions

Recovery keeps the original and retained path histories distinct, even when
their labels agree. All draws are retained in the accumulating union.
-/

noncomputable section
open Classical

namespace LeanBlast.SecondKahnKalai

/-- A nondecreasing finite list of capacities has a zero prefix followed by
strictly positive capacities. The empty positive suffix is permitted. -/
theorem exists_zero_prefix_positive_suffix (m : ℕ → ℕ) (d : ℕ)
    (hmono : MonotoneOn m (Set.Iio d)) :
    ∃ k, k ≤ d ∧ (∀ i, i < k → m i = 0) ∧
      (∀ i, i < d - k → 0 < m (i + k)) := by
  classical
  by_cases h : ∃ k, k < d ∧ 0 < m k
  · let k := Nat.find h
    have hk : k < d ∧ 0 < m k := Nat.find_spec h
    refine ⟨k, hk.1.le, ?_, ?_⟩
    · intro i hi
      by_contra hzero
      have hip : 0 < m i := Nat.pos_of_ne_zero hzero
      have hki : k ≤ i := Nat.find_min' h ⟨lt_trans hi hk.1, hip⟩
      omega
    · intro i hi
      have hik : i + k < d := by omega
      exact lt_of_lt_of_le hk.2 (hmono hk.1 hik (by omega))
  · refine ⟨d, le_rfl, ?_, ?_⟩
    · intro i hi
      by_contra hzero
      exact h ⟨i, hi, Nat.pos_of_ne_zero hzero⟩
    · intro i hi
      omega

namespace ProbabilityTree

variable {X : Type} [DecidableEq X]

namespace CoverState

variable {k : ℕ} {original : ProbabilityTree X k} {σ : ℝ}

end CoverState

end ProbabilityTree

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Classical


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.exists_zero_prefix_positive_suffix := @_root_.OAI.LeanBlast.SecondKahnKalai.exists_zero_prefix_positive_suffix
