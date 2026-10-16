-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.one_lt_nodePotential_of_bad
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:07:30.40305+00:00
-- url     : https://prove2.me/submissions/ae67c341-9f71-4252-bbad-a017f087e1ed

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreePotential.lean:L44-L70
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.one_lt_nodePotential_of_bad. The node keeps its source
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
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

/-- A failed good-mass threshold forces the recursively defined potential
above one. Children with zero target mass require no special treatment. -/
theorem one_lt_nodePotential_of_bad {B : Type*} [Fintype B]
    (m : ℕ) (failure : ℝ) (target childPotential : B → ℝ) (good : B → Prop)
    (ht : ∀ b, 0 ≤ target b) (hc : ∀ b, 0 ≤ childPotential b)
    (hmass : failure + ∑ b, target b = 1)
    (hchild : ∀ b, ¬good b → 1 < childPotential b)
    (hbad : (∑ b, if good b then target b else 0) < 1 - Real.exp (-(m : ℝ))) :
    1 < nodePotential m failure target childPotential := by
  classical
  have hsplit : (∑ b, if good b then target b else 0) +
      (∑ b, if good b then 0 else target b) = ∑ b, target b := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : good b <;> simp [hb]
  have hsum : (∑ b, if good b then 0 else target b) ≤
      ∑ b, target b * childPotential b := by
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : good b
    · simpa only [ite_eq_left hb] using mul_nonneg (ht b) (hc b)
    · simpa only [ite_eq_right hb, mul_one] using
        mul_le_mul_of_nonneg_left (hchild b hb).le (ht b)
  unfold nodePotential
  apply (lt_div_iff₀ (Real.exp_pos _)).mpr
  nlinarith

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


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.one_lt_nodePotential_of_bad := @_root_.OAI.LeanBlast.SecondKahnKalai.one_lt_nodePotential_of_bad
