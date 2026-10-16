-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.choose_le_exp_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:22:31.449578+00:00
-- url     : https://prove2.me/submissions/db4e9df2-f50a-4413-8fd7-0119a971702b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/Predecessor.lean:L25-L45
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.choose_le_exp_div_pow. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.Predecessor ----
namespace OAI

/-!
# Maximizing predecessors

The predecessor is chosen by maximization over the actual finite powerset,
including its empty member.  The graph application uses distinct group-orbit
copies and the actual containment probability, not labeled embeddings.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

/-- The standard real binomial upper bound, derived directly from the
exponential series and the factorial upper bound on `choose`. -/
theorem choose_le_exp_div_pow (h r : ℕ) (hr : 0 < r) :
    (h.choose r : ℝ) ≤ (Real.exp 1 * (h : ℝ) / (r : ℝ)) ^ r := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hexp : (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp 1 ^ r := by
    simpa only [← Real.exp_nat_mul, mul_one] using
      Real.pow_div_factorial_le_exp (r : ℝ) (show 0 ≤ (r : ℝ) by positivity) r
  calc
    (h.choose r : ℝ) ≤ (h : ℝ) ^ r / (r.factorial : ℝ) := Nat.choose_le_pow_div r h
    _ = ((h : ℝ) / (r : ℝ)) ^ r * ((r : ℝ) ^ r / (r.factorial : ℝ)) := by
      rw [div_pow]
      field_simp
    _ ≤ ((h : ℝ) / (r : ℝ)) ^ r * Real.exp 1 ^ r :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (Real.exp 1 * (h : ℝ) / (r : ℝ)) ^ r := by
      rw [← mul_pow]
      congr 1
      ring

section FiniteMaximum

variable {X : Type*}

end FiniteMaximum

section OrbitPredecessor

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type*} [DecidableEq X] [MulAction G X]

end OrbitPredecessor

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.choose_le_exp_div_pow := @_root_.OAI.LeanBlast.SecondKahnKalai.choose_le_exp_div_pow
