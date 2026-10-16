-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.localFailureMass_add_successfulTargetMass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:45:22.636816+00:00
-- url     : https://prove2.me/submissions/a4c2f3fe-dc0b-4efb-a344-b20ddef0032a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreeReductionData.lean:L46-L64
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.localFailureMass_add_successfulTargetMass. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.TreeReductionData ----
namespace OAI

/-! Fixed-input local masses and the deterministic good-node predicate. -/

noncomputable section
open scoped BigOperators
open Classical

namespace LeanBlast.SecondKahnKalai

section LocalMasses

variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem localFailureMass_add_successfulTargetMass (μ : FiniteLaw B)
    (A : B → Finset X) {ρ : ℝ} (hμ : μ.IsPositive) (hρ : 0 < ρ)
    (m : ℕ) (W : Finset X) :
    localFailureMass μ A ρ m W + ∑ b, successfulTargetMass μ A ρ m W b = 1 := by
  classical
  calc
    _ = ∑ b, ∑ c, resamplingWeight μ A ρ W (c, b) := by
      unfold localFailureMass successfulTargetMass LocalFailure
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : LocalSuccess μ A ρ m W c b <;> simp [h]
    _ = ∑ c, ∑ b, resamplingWeight μ A ρ W (c, b) := Finset.sum_comm
    _ = 1 := by
      simp_rw [resampling_source_marginal μ A hμ hρ W]
      exact μ.total

end LocalMasses

variable {X : Type} [DecidableEq X]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.localFailureMass_add_successfulTargetMass := @_root_.OAI.LeanBlast.SecondKahnKalai.localFailureMass_add_successfulTargetMass
