-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_hasSpread
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:31:57.245128+00:00
-- url     : https://prove2.me/submissions/a29b4d2c-bb40-4a0a-b3a0-c5aed60b0528

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphHierarchy.lean:L247-L268
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_hasSpread. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.CopyOrbits ----
namespace OAI

/-!
# Distinct subset copies under a finite group action

Copies are distinct orbit elements, not group elements or labeled embeddings.
All counting and probability statements therefore retain the stabilizer
multiplicities correctly, including for the empty subset.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace LeanBlast.SecondKahnKalai

universe u v

variable (G : Type u) [Group G] [Fintype G]
variable {X : Type v} [DecidableEq X] [MulAction G X]

theorem card_extension_filter (I S J : Finset X) :
    ((Finset.univ : Finset (ExtensionCopy G I S)).filter
      (fun C => J ⊆ C.val.val)).card = containingCopyCount G I (S ∪ J) := by
  calc
    _ = Fintype.card {C : ExtensionCopy G I S // J ⊆ C.val.val} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card (ExtensionCopy G I (S ∪ J)) :=
      Fintype.card_congr (extensionIntersectionEquiv G I S J)
    _ = _ := card_ExtensionCopy G I (S ∪ J)

theorem extensionLaw_prob (I S J : Finset X) (hpos : 0 < containmentProb G I S) :
    (extensionLaw G I S hpos).prob (fun C => J ⊆ C.val.val) =
      containmentProb G I (S ∪ J) / containmentProb G I S := by
  let : Nonempty (ExtensionCopy G I S) := extensionCopy_nonempty G hpos
  change (FiniteLaw.uniform (ExtensionCopy G I S)).prob _ = _
  rw [uniform_prob_count]
  calc
    _ = (containingCopyCount G I (S ∪ J) : ℝ) / containingCopyCount G I S :=
      congrArg₂ (fun a b : ℕ => (a : ℝ) / (b : ℝ))
        (card_extension_filter G I S J) (card_ExtensionCopy G I S)
    _ = _ := by
      rw [containmentProb_eq_count, containmentProb_eq_count]
      have hI : (orbitCount G I : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (orbitCount_pos G I))
      have hS : (containingCopyCount G I S : ℝ) ≠ 0 := by
        apply ne_of_gt
        apply Nat.cast_pos.mpr
        exact (containingCopyCount_pos_iff G I S).mpr ((containmentProb_pos_iff G I S).mp hpos)
      field_simp [hI, hS]

/-- For a set disjoint from the predecessor, containment in the added label
is exactly the usual conditional containment event. -/
theorem extensionLaw_added_prob (I S J : Finset X) (hpos : 0 < containmentProb G I S)
    (hdis : Disjoint J S) :
    (extensionLaw G I S hpos).prob (fun C => J ⊆ C.val.val \ S) =
      containmentProb G I (S ∪ J) / containmentProb G I S := by
  simpa only [Finset.subset_sdiff, hdis, and_true] using extensionLaw_prob G I S J hpos

/-- A set meeting the predecessor cannot lie in any added label. -/
theorem extensionLaw_added_prob_eq_zero (I S J : Finset X)
    (hpos : 0 < containmentProb G I S) (hdis : ¬ Disjoint J S) :
    (extensionLaw G I S hpos).prob (fun C => J ⊆ C.val.val \ S) = 0 := by
  simp [FiniteLaw.prob, Finset.subset_sdiff, hdis]

end LeanBlast.SecondKahnKalai

end

end OAI

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

/-- A conditional containment-ratio estimate is exactly spreadness of the
added set. Requests intersecting the existing set have probability zero. -/
theorem extensionLaw_isSpread_of_ratio (I S : Finset X)
    (hp : 0 < containmentProb G I S) (σ : ℝ) (hσ : 0 ≤ σ)
    (hratio : ∀ J : Finset X, J.Nonempty → Disjoint S J →
      containmentProb G I (S ∪ J) / containmentProb G I S ≤ σ ^ J.card) :
    IsSpread (extensionLaw G I S hp) (fun b => b.val.val \ S) σ := by
  intro J hJ
  by_cases hd : Disjoint J S
  · rw [extensionLaw_added_prob G I S J hp hd]
    exact hratio J hJ hd.symm
  · rw [extensionLaw_added_prob_eq_zero G I S J hp hd]
    exact pow_nonneg hσ _

/-- Local conditional containment ratios give spread at every node, including
nodes reached through different histories with the same current copy. -/
theorem orbitExtensionTree_hasSpread (σ : ℝ) (hσ : 0 ≤ σ)
    (d : ℕ) (A : ℕ → Finset X)
    (hnested : ∀ i, i < d → A i ⊆ A (i + 1))
    (hratio : ∀ i, i < d → ∀ S0 ∈ copyOrbit G (A i),
      ∀ J : Finset X, J.Nonempty → Disjoint S0 J →
        containmentProb G (A (i + 1)) (S0 ∪ J) /
          containmentProb G (A (i + 1)) S0 ≤ σ ^ J.card)
    (S0 : Finset X) (hS0 : S0 ∈ copyOrbit G (A 0)) :
    (orbitExtensionTree G d A hnested S0 hS0).HasSpread (fun _ => σ) := by
  induction d generalizing A S0 with
  | zero => trivial
  | succ d ih =>
      simp only [orbitExtensionTree, ProbabilityTree.HasSpread]
      constructor
      · exact extensionLaw_isSpread_of_ratio G (A 1) S0 _ σ hσ
          (hratio 0 (by omega) S0 hS0)
      · intro b
        exact ih (fun i => A (i + 1))
          (fun i hi => hnested (i + 1) (by omega))
          (fun i hi => hratio (i + 1) (by omega)) b.val.val b.val.property

end OrbitTrees

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_hasSpread := @_root_.OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_hasSpread
