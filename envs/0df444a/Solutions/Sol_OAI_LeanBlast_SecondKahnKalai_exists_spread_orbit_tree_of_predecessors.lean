-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.exists_spread_orbit_tree_of_predecessors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:32:48.467806+00:00
-- url     : https://prove2.me/submissions/3bcb0bb4-0cec-42d9-be90-7169ecd18f51

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/GraphHierarchy.lean:L270-L304
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.exists_spread_orbit_tree_of_predecessors. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_exists_setHierarchy
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_orbitExtensionTree_hasCapacities
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_orbitExtensionTree_hasSpread
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_orbitExtensionTree_isDisjoint

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

theorem stage_subset_stage (h : SetHierarchy R H) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ h.depth) : h.stage i ⊆ h.stage j := by
  induction j, hij using Nat.le_induction with
  | base => exact Subset.rfl
  | succ j hij ih =>
      exact (ih (by omega)).trans (h.nested j (by omega))

theorem stage_subset (h : SetHierarchy R H) {i : ℕ} (hi : i ≤ h.depth) :
    h.stage i ⊆ H := by
  simpa only [h.last] using h.stage_subset_stage hi (le_refl h.depth)

theorem depth_pos (h : SetHierarchy R H) (hH : H.Nonempty) : 0 < h.depth := by
  by_contra hn
  have hd : h.depth = 0 := by omega
  have : H = ∅ := by rw [← h.last, hd, h.first]
  simp [this] at hH

theorem capacity_pos (h : SetHierarchy R H) {i : ℕ} (hi : i < h.depth) :
    0 < h.capacity i := by
  have hs := h.sparse i hi
  unfold capacity
  omega

theorem capacity_growth (h : SetHierarchy R H) {i : ℕ} (hi : i + 1 < h.depth) :
    16 * h.capacity i ≤ h.capacity (i + 1) := by
  have hs := h.sparse (i + 1) hi
  unfold capacity
  omega

theorem capacity_le (h : SetHierarchy R H) {i : ℕ} (hi : i < h.depth) :
    h.capacity i ≤ H.card := by
  exact (Nat.sub_le _ _).trans (Finset.card_le_card (h.stage_subset (by omega)))

end SetHierarchy

section OrbitTrees

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type} [DecidableEq X] [MulAction G X]

/-- Adding a path's labels to its starting copy recovers an actual terminal
copy. In particular an empty root gives an actual copy as its path union. -/
theorem orbitExtensionTree_pathUnion (d : ℕ) (A : ℕ → Finset X)
    (hnested : ∀ i, i < d → A i ⊆ A (i + 1))
    (S0 : Finset X) (hS0 : S0 ∈ copyOrbit G (A 0))
    (p : (orbitExtensionTree G d A hnested S0 hS0).Path) :
    S0 ∪ (orbitExtensionTree G d A hnested S0 hS0).pathUnion p ∈
      copyOrbit G (A d) := by
  induction d generalizing A S0 with
  | zero => simpa only [orbitExtensionTree, ProbabilityTree.pathUnion, Finset.union_empty] using hS0
  | succ d ih =>
      rcases p with ⟨b, p⟩
      have hp := ih (fun i => A (i + 1))
        (fun i hi => hnested (i + 1) (by omega)) b.val.val b.val.property p
      simpa only [orbitExtensionTree, ProbabilityTree.pathUnion, ← Finset.union_assoc,
        Finset.union_sdiff_of_subset b.property] using hp

/-- The constructive assembly from a strict predecessor rule. In particular,
the tree and its chain are outputs, not hypotheses. The concrete maximizing
rule below discharges the two local predecessor requirements. -/
theorem exists_spread_orbit_tree_of_predecessors
    (H : Finset X) (hH : H.Nonempty) (σ : ℝ) (hσ : 0 ≤ σ)
    (R : Finset X → Finset X → Prop)
    (hpred : ∀ I, I ⊆ H → I.Nonempty →
      ∃ S, S ⊆ I ∧ 17 * S.card < I.card ∧ R S I)
    (hratio : ∀ I, I ⊆ H → ∀ S, R S I →
      ∀ S0 ∈ copyOrbit G S, ∀ J : Finset X, J.Nonempty → Disjoint S0 J →
        containmentProb G I (S0 ∪ J) / containmentProb G I S0 ≤ σ ^ J.card) :
    ∃ k : ℕ, ∃ m : ℕ → ℕ, ∃ T : ProbabilityTree X k,
      0 < k ∧ T.IsDisjoint ∧ T.HasCapacities m ∧ T.HasSpread (fun _ => σ) ∧
      (∀ i, i < k → 0 < m i) ∧
      (∀ i, i + 1 < k → 16 * m i ≤ m (i + 1)) ∧
      m (k - 1) ≤ H.card ∧
      ∀ p : T.Path, T.pathUnion p ∈ copyOrbit G H := by
  obtain ⟨a⟩ := exists_setHierarchy R H hpred
  have hk : 0 < a.depth := a.depth_pos hH
  have hroot : (∅ : Finset X) ∈ copyOrbit G (a.stage 0) := by
    rw [a.first]
    exact self_mem_copyOrbit G ∅
  let T := orbitExtensionTree G a.depth a.stage a.nested ∅ hroot
  refine ⟨a.depth, a.capacity, T, hk,
    orbitExtensionTree_isDisjoint G _ _ _ _ _,
    orbitExtensionTree_hasCapacities G _ _ _ _ _, ?_,
    (fun i hi => a.capacity_pos hi), (fun i hi => a.capacity_growth hi),
    a.capacity_le (by omega), ?_⟩
  · apply orbitExtensionTree_hasSpread G σ hσ
    intro i hi S0 hS0 J hJ hd
    exact hratio (a.stage (i + 1)) (a.stage_subset (by omega))
      (a.stage i) (a.selected i hi) S0 hS0 J hJ hd
  · intro p
    simpa only [Finset.empty_union, a.last] using
      orbitExtensionTree_pathUnion G a.depth a.stage a.nested ∅ hroot p

end OrbitTrees

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.exists_spread_orbit_tree_of_predecessors := @_root_.OAI.LeanBlast.SecondKahnKalai.exists_spread_orbit_tree_of_predecessors
