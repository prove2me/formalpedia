-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_isDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:28:48.738274+00:00
-- url     : https://prove2.me/submissions/1db42c7b-acfe-42b8-9944-e33001af6b81

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphHierarchy.lean:L193-L209
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_isDisjoint. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_orbitExtensionTree_support_disjoint

-- ---- from OAI.Combinatorics.GraphThreshold.GraphHierarchy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! The finite hierarchy and the actual tree of extensions used in the graph
application. Histories are represented by the probability tree's dependent
paths; equal set labels do not identify distinct histories. -/

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

namespace SetHierarchy

variable {X : Type*} [DecidableEq X]
variable {R : Finset X → Finset X → Prop} {H : Finset X}

end SetHierarchy

section OrbitTrees

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type} [DecidableEq X] [MulAction G X]

/-- Every constructed tree has the strong recursive disjointness property. -/
theorem orbitExtensionTree_isDisjoint (d : ℕ) (A : ℕ → Finset X)
    (hnested : ∀ i, i < d → A i ⊆ A (i + 1))
    (S0 : Finset X) (hS0 : S0 ∈ copyOrbit G (A 0)) :
    (orbitExtensionTree G d A hnested S0 hS0).IsDisjoint := by
  induction d generalizing A S0 with
  | zero => trivial
  | succ d ih =>
      simp only [orbitExtensionTree, ProbabilityTree.IsDisjoint]
      constructor
      · intro b
        exact (orbitExtensionTree_support_disjoint G d (fun i => A (i + 1))
          (fun i hi => hnested (i + 1) (by omega)) b.val.val b.val.property).mono_left
          Finset.sdiff_subset
      · intro b
        exact ih (fun i => A (i + 1))
          (fun i hi => hnested (i + 1) (by omega)) b.val.val b.val.property

end OrbitTrees

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_isDisjoint := @_root_.OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_isDisjoint
