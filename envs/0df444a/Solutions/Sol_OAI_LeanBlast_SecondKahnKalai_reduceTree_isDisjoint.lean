-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.reduceTree_isDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:46:54.355722+00:00
-- url     : https://prove2.me/submissions/4c08b730-39a4-4f65-8dab-343be07f61ec

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreeReduction.lean:L209-L224
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.reduceTree_isDisjoint. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.TreeReduction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Classical

noncomputable section

namespace LeanBlast.SecondKahnKalai

section RetainedLaw

variable {B X : Type*} [Fintype B] [DecidableEq X]

end RetainedLaw

section Construction

variable {X : Type} [DecidableEq X]

theorem reduceTree_support_subset (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) : (reduceTree ρ m W T hρ hm hg).support ⊆ T.support := by
  induction T generalizing m with
  | leaf => simp [reduceTree, ProbabilityTree.support]
  | @node n B inst μ hμ A child ih =>
      simp only [reduceTree, ProbabilityTree.support]
      intro x hx
      obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hx
      refine Finset.mem_biUnion.mpr ⟨b.val, Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hb with hb | hb
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hb).1
      · exact Finset.mem_union_right _
          (ih b.val (fun j => m (j + 1))
            (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1 hb)

theorem reduceTree_isDisjoint (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) (hT : T.IsDisjoint) :
    (reduceTree ρ m W T hρ hm hg).IsDisjoint := by
  induction T generalizing m with
  | leaf => simp only [reduceTree, ProbabilityTree.IsDisjoint]
  | @node n B inst μ hμ A child ih =>
      simp only [reduceTree, ProbabilityTree.IsDisjoint]
      constructor
      · intro b
        exact (hT.1 b.val).mono Finset.sdiff_subset
          (reduceTree_support_subset ρ (fun j => m (j + 1)) W (child b.val) hρ
            (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1)
      · intro b
        exact ih b.val (fun j => m (j + 1))
          (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1 (hT.2 b.val)

end Construction

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.reduceTree_isDisjoint := @_root_.OAI.LeanBlast.SecondKahnKalai.reduceTree_isDisjoint
