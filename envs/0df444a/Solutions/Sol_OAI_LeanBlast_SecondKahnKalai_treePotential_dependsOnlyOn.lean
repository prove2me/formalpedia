-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.treePotential_dependsOnlyOn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:09:23.826985+00:00
-- url     : https://prove2.me/submissions/275d3350-8d5b-4353-a37f-340ce0fe5076

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreePotential.lean:L192-L212
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.treePotential_dependsOnlyOn. The node keeps its source
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

-- ---- from OAI.Combinatorics.GraphThreshold.ProbabilityTreeFacts ----
namespace OAI

/-! Path and locality facts for the stable finite probability-tree representation. -/

noncomputable section

namespace LeanBlast.SecondKahnKalai

section Locality

variable {X β : Type*} [DecidableEq X] {S T A : Finset X} {f : Finset X → β}

theorem DependsOnlyOn.mono (hf : DependsOnlyOn S f) (hST : S ⊆ T) :
    DependsOnlyOn T f := by
  intro W V hWV
  apply hf W V
  apply Finset.ext
  intro x
  by_cases hx : x ∈ S
  · have hxT := hST hx
    have he := Finset.ext_iff.mp hWV x
    simpa [hx, hxT] using he
  · simp [hx]

end Locality

namespace ProbabilityTree

variable {X : Type}

section Labels

variable [DecidableEq X]

theorem label_subset_support {d : ℕ} {B : Type} [Fintype B]
    (law : FiniteLaw B) (positive : law.IsPositive) (label : B → Finset X)
    (child : B → ProbabilityTree X d) (b : B) :
    label b ⊆ (node B law positive label child).support := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, Finset.mem_union_left _ hx⟩

theorem child_support_subset {d : ℕ} {B : Type} [Fintype B]
    (law : FiniteLaw B) (positive : law.IsPositive) (label : B → Finset X)
    (child : B → ProbabilityTree X d) (b : B) :
    (child b).support ⊆ (node B law positive label child).support := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, Finset.mem_union_right _ hx⟩

theorem labels_support_subset {d : ℕ} {B : Type} [Fintype B]
    (law : FiniteLaw B) (positive : law.IsPositive) (label : B → Finset X)
    (child : B → ProbabilityTree X d) :
    (Finset.univ.biUnion label) ⊆ (node B law positive label child).support := by
  intro x hx
  obtain ⟨b, _, hxb⟩ := Finset.mem_biUnion.mp hx
  exact label_subset_support law positive label child b hxb

end Labels

end ProbabilityTree

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.Resampling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

omit [Fintype B] in
theorem resampling_target_subset_iff_fragment (A : B → Finset X)
    (W : Finset X) (c b : B) :
    A b ⊆ resamplingY A W c ↔ resamplingFragment A W b ⊆ A c := by
  constructor
  · intro h x hx
    have hx' := Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp (h hx'.1) with hW | hc
    · exact (hx'.2 hW).elim
    · exact hc
  · intro h x hx
    by_cases hW : x ∈ W
    · exact Finset.mem_union.mpr (Or.inl hW)
    · exact Finset.mem_union.mpr (Or.inr (h (Finset.mem_sdiff.mpr ⟨hx, hW⟩)))

/-- The transition depends on W only through its intersections with the
labels, expressed equivalently by their retained fragments. -/
theorem resamplingWeight_congr_fragments (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) {W W' : Finset X}
    (hW : ∀ b, resamplingFragment A W b = resamplingFragment A W' b) (cb : B × B) :
    resamplingWeight ν A ρ W cb = resamplingWeight ν A ρ W' cb := by
  have hsub (c b : B) : A b ⊆ resamplingY A W c ↔ A b ⊆ resamplingY A W' c := by
    rw [resampling_target_subset_iff_fragment, resampling_target_subset_iff_fragment, hW]
  have hn (c b : B) :
      resamplingNumerator ν A ρ (resamplingY A W c) b =
        resamplingNumerator ν A ρ (resamplingY A W' c) b := by
    simp only [resamplingNumerator, hsub]
  simp only [resamplingWeight, resamplingTargetWeight, resamplingZ, hn]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.TreeReductionData ----
namespace OAI

/-! Fixed-input local masses and the deterministic good-node predicate. -/

noncomputable section
open scoped BigOperators
open Classical

namespace LeanBlast.SecondKahnKalai

section LocalMasses

variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem resamplingZ_congr_fragments (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) {W V : Finset X}
    (hWV : ∀ b, resamplingFragment A W b = resamplingFragment A V b) (c : B) :
    resamplingZ μ A ρ (W ∪ A c) = resamplingZ μ A ρ (V ∪ A c) := by
  unfold resamplingZ
  apply Finset.sum_congr rfl
  intro b _
  have hsub : A b ⊆ resamplingY A W c ↔ A b ⊆ resamplingY A V c := by
    rw [resampling_target_subset_iff_fragment, resampling_target_subset_iff_fragment, hWV]
  unfold resamplingNumerator
  exact if_congr hsub rfl rfl

theorem localSuccess_congr_fragments (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) {W V : Finset X}
    (hWV : ∀ b, resamplingFragment A W b = resamplingFragment A V b) (c b : B) :
    LocalSuccess μ A ρ m W c b ↔ LocalSuccess μ A ρ m V c b := by
  unfold LocalSuccess
  rw [resamplingZ_congr_fragments μ A ρ hWV c]
  change (_ ∧ (resamplingFragment A W b).card ≤ m / 2) ↔
    (_ ∧ (resamplingFragment A V b).card ≤ m / 2)
  rw [hWV b]

theorem successfulTargetMass_congr_fragments (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) {W V : Finset X}
    (hWV : ∀ b, resamplingFragment A W b = resamplingFragment A V b) (b : B) :
    successfulTargetMass μ A ρ m W b = successfulTargetMass μ A ρ m V b := by
  unfold successfulTargetMass
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : LocalSuccess μ A ρ m W c b
  · have hv := (localSuccess_congr_fragments μ A ρ m hWV c b).mp h
    simp [h, hv, resamplingWeight_congr_fragments μ A ρ hWV]
  · have hv : ¬LocalSuccess μ A ρ m V c b :=
      fun hv => h ((localSuccess_congr_fragments μ A ρ m hWV c b).mpr hv)
    simp [h, hv]

theorem localFailureMass_congr_fragments (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) {W V : Finset X}
    (hWV : ∀ b, resamplingFragment A W b = resamplingFragment A V b) :
    localFailureMass μ A ρ m W = localFailureMass μ A ρ m V := by
  unfold localFailureMass LocalFailure
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : LocalSuccess μ A ρ m W c b
  · have hv := (localSuccess_congr_fragments μ A ρ m hWV c b).mp h
    simp [h, hv]
  · have hv : ¬LocalSuccess μ A ρ m V c b :=
      fun hv => h ((localSuccess_congr_fragments μ A ρ m hWV c b).mpr hv)
    simp [h, hv, resamplingWeight_congr_fragments μ A ρ hWV]

theorem fragments_eq_of_inter_label_union_eq (A : B → Finset X) {W V : Finset X}
    (hWV : W ∩ Finset.univ.biUnion A = V ∩ Finset.univ.biUnion A) (b : B) :
    resamplingFragment A W b = resamplingFragment A V b := by
  apply Finset.ext
  intro x
  by_cases hx : x ∈ A b
  · have hxU : x ∈ Finset.univ.biUnion A :=
      Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ b, hx⟩
    have hmem : x ∈ W ↔ x ∈ V := by
      simpa only [Finset.mem_inter, hxU, and_true] using Finset.ext_iff.mp hWV x
    simp [resamplingFragment, hx, hmem]
  · simp [resamplingFragment, hx]

theorem successfulTargetMass_dependsOnlyOn (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) (b : B) :
    DependsOnlyOn (Finset.univ.biUnion A) (fun W => successfulTargetMass μ A ρ m W b) := by
  intro W V hWV
  exact successfulTargetMass_congr_fragments μ A ρ m
    (fragments_eq_of_inter_label_union_eq A hWV) b

theorem localFailureMass_dependsOnlyOn (μ : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (m : ℕ) :
    DependsOnlyOn (Finset.univ.biUnion A) (fun W => localFailureMass μ A ρ m W) := by
  intro W V hWV
  exact localFailureMass_congr_fragments μ A ρ m
    (fragments_eq_of_inter_label_union_eq A hWV)

end LocalMasses

variable {X : Type} [DecidableEq X]

end LeanBlast.SecondKahnKalai

end

end OAI

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

section Trees

variable {X : Type} [Fintype X] [DecidableEq X]

omit [Fintype X] in
/-- The potential only inspects the labels belonging to the fixed subtree. -/
theorem treePotential_dependsOnlyOn (p : ℝ) (m : ℕ → ℕ) {d : ℕ}
    (T : ProbabilityTree X d) : DependsOnlyOn T.support (fun W => treePotential p m W T) := by
  induction T generalizing m with
  | leaf => intro W V _; simp only [treePotential]
  | @node d B inst ν hν A child ih =>
      intro W V hWV
      have hd := ((localFailureMass_dependsOnlyOn ν A p (m 0)).mono
        (ProbabilityTree.labels_support_subset ν hν A child)) W V hWV
      have ht (b : B) := ((successfulTargetMass_dependsOnlyOn ν A p (m 0) b).mono
        (ProbabilityTree.labels_support_subset ν hν A child)) W V hWV
      have hc (b : B) := ((ih b (fun j => m (j + 1))).mono
        (ProbabilityTree.child_support_subset ν hν A child b)) W V hWV
      dsimp only at hd ht hc
      simp only [treePotential, nodePotential]
      rw [hd]
      congr 2
      apply Finset.sum_congr rfl
      intro b _
      rw [ht b, hc b]

end Trees

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
open Classical


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.treePotential_dependsOnlyOn := @_root_.OAI.LeanBlast.SecondKahnKalai.treePotential_dependsOnlyOn
