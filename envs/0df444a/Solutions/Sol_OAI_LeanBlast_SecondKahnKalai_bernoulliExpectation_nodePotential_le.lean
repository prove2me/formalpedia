-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_nodePotential_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:08:24.302978+00:00
-- url     : https://prove2.me/submissions/ca449a78-3f1c-409e-b062-7092a6994027

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreePotential.lean:L87-L124
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_nodePotential_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.TreePotential ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# The bad-node potential for simultaneous tree reduction

All nodes in a reduction use the same random set. The expectation argument
uses an outside-coordinate change of measure, rather than independence of
node outcomes.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace LeanBlast.SecondKahnKalai

theorem bernoulliExpectation_nodePotential {X B : Type*} [Fintype X] [DecidableEq X]
    [Fintype B] (p : ℝ) (m : ℕ) (failure : Finset X → ℝ)
    (target childPotential : B → Finset X → ℝ) :
    bernoulliExpectation p (fun W => nodePotential m (failure W)
      (fun b => target b W) (fun b => childPotential b W)) =
      (bernoulliExpectation p failure +
        ∑ b, bernoulliExpectation p (fun W => target b W * childPotential b W)) /
        Real.exp (-(m : ℝ)) := by
  unfold bernoulliExpectation nodePotential
  dsimp only
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro W _
  rw [← mul_div_assoc, mul_add, Finset.mul_sum]

/-- The expectation recursion uses one change-of-measure estimate per child;
it does not factor a product of dependent random variables. -/
theorem bernoulliExpectation_nodePotential_le {X B : Type*} [Fintype X] [DecidableEq X]
    [Fintype B] (p : ℝ) (m : ℕ) (ν : FiniteLaw B) (failure : Finset X → ℝ)
    (target childPotential : B → Finset X → ℝ)
    (hfailure : bernoulliExpectation p failure ≤ Real.exp (-9 * (m : ℝ)))
    (hchild : ∀ b,
      bernoulliExpectation p (fun W => target b W * childPotential b W) ≤
        Real.exp (11 * (m : ℝ)) * ν.weight b * bernoulliExpectation p (childPotential b)) :
    bernoulliExpectation p (fun W => nodePotential m (failure W)
      (fun b => target b W) (fun b => childPotential b W)) ≤
      Real.exp (-8 * (m : ℝ)) + Real.exp (12 * (m : ℝ)) *
        ν.expectation (fun b => bernoulliExpectation p (childPotential b)) := by
  rw [bernoulliExpectation_nodePotential]
  have hs := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hchild b)
  have hsum : (∑ b, Real.exp (11 * (m : ℝ)) * ν.weight b *
      bernoulliExpectation p (childPotential b)) =
      Real.exp (11 * (m : ℝ)) * ν.expectation
        (fun b => bernoulliExpectation p (childPotential b)) := by
    unfold FiniteLaw.expectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hbound := div_le_div_of_nonneg_right (add_le_add hfailure hs) (Real.exp_pos (-(m : ℝ))).le
  rw [hsum] at hbound
  refine hbound.trans_eq ?_
  have hfirst : Real.exp (-9 * (m : ℝ)) / Real.exp (-(m : ℝ)) =
      Real.exp (-8 * (m : ℝ)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hsecond : Real.exp (11 * (m : ℝ)) / Real.exp (-(m : ℝ)) =
      Real.exp (12 * (m : ℝ)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [add_div, hfirst, mul_div_right_comm, hsecond]

section Trees

variable {X : Type} [Fintype X] [DecidableEq X]

end Trees

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_nodePotential_le := @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_nodePotential_le
