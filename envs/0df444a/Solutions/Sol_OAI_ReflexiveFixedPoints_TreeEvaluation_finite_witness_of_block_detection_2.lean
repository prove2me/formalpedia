-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.finite_witness_of_block_detection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T18:01:22.177248+00:00
-- url     : https://prove2.me/submissions/ec73736c-71af-4109-ba68-28d62eed5d50

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/FiniteWitness.lean:L43-L96
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.finite_witness_of_block_detection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeEvaluation
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeFrontier
import Definitions.Def_OAI_Analysis_Nonexpansive_PredictionCompact
import Definitions.Def_OAI_Analysis_Nonexpansive_PredictionOutputs
import Definitions.Def_OAI_Analysis_Nonexpansive_PrefixPredictionOutputs
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeBudget
import Definitions.Def_OAI_Analysis_Nonexpansive_Resolvents
import Definitions.Def_OAI_Analysis_Nonexpansive_GeneratedMaps
import Definitions.Def_OAI_Analysis_Nonexpansive_TailMaps
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateRecords
import Definitions.Def_OAI_Analysis_Nonexpansive_Diametral
import Definitions.Def_OAI_Analysis_Nonexpansive_CompactDetector
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateThreshold
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidatePreparation
import Definitions.Def_OAI_Analysis_Nonexpansive_SequentialHistory
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveRun
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveConvexPrefix
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveSelection
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveParentReturn
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakSelfMap
import Definitions.Def_OAI_Analysis_Nonexpansive_PointwiseWeakApproximation
import Definitions.Def_OAI_Analysis_Nonexpansive_CompactMapSemigroup
import Definitions.Def_OAI_Analysis_Nonexpansive_TailMapSemigroup
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakNestedConvexHull
import Definitions.Def_OAI_Analysis_Nonexpansive_Anchor
import Definitions.Def_OAI_Analysis_Nonexpansive_AnchorAdaptiveSelection
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateSelection
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedGroupConcat
import Definitions.Def_OAI_Analysis_Nonexpansive_FrontierFromGroups
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLevel
import Definitions.Def_OAI_Analysis_Nonexpansive_FrontierTower
import Definitions.Def_OAI_Analysis_Nonexpansive_TerminalSequence
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateStages
import Definitions.Def_OAI_Analysis_Nonexpansive_GlobalCandidateOrdinals
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLabels
import Definitions.Def_OAI_Analysis_Nonexpansive_ParentReturnHistory
import Definitions.Def_OAI_Analysis_Nonexpansive_FinitePrefixEmbedding
import Definitions.Def_OAI_Analysis_Nonexpansive_ListRunPrefix
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLevelHistory
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLedger
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLedgerJoin
import Definitions.Def_OAI_Analysis_Nonexpansive_PrefixPredictionReindex
import Definitions.Def_OAI_Analysis_Nonexpansive_PredictionCutoff
import Definitions.Def_OAI_Analysis_Nonexpansive_SubtreeEvaluation
import Definitions.Def_OAI_Analysis_Nonexpansive_SubtreeErrors
import Definitions.Def_OAI_Analysis_Nonexpansive_BlockBefore
import Definitions.Def_OAI_Analysis_Nonexpansive_SwitchingStates
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTreeIntervals
import Definitions.Def_OAI_Analysis_Nonexpansive_SwitchingBlocks
import Definitions.Def_OAI_Analysis_Nonexpansive_TransmittedSubtreeErrors
import Definitions.Def_OAI_Analysis_Nonexpansive_BlockEstimates
import Definitions.Def_OAI_Analysis_Nonexpansive_LedgerPredictionLimits
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidatePredictions
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateAncestors
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateDetectors
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeTolerance
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateTolerance
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateTreeTolerance
import Definitions.Def_OAI_Analysis_Nonexpansive_SwitchingTreeData
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeProducer
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedDeficit
import Definitions.Def_OAI_Analysis_Nonexpansive_FiniteWitness
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_evaluate_norm_sub_le
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_switchVector_block_telescope
import Theorems.Thm_OAI_ReflexiveFixedPoints_WeightedTree_sum_pathWeight_parent
import Theorems.Thm_OAI_ReflexiveFixedPoints_finite_weighted_deficit

-- ---- from OAI.Analysis.Nonexpansive.OrderedTree ----
namespace OAI

/-!
# Ordered trees with finite nonempty levels

The parent maps are monotone surjections. Thus every node has children,
and the children of consecutive parents occur in consecutive groups.
Ancestor maps are actual finite composites of parent maps.
-/

namespace ReflexiveFixedPoints

namespace OrderedTree

variable (T : OrderedTree)

theorem ancestorLE_step_apply {i j : ℕ} (h : i ≤ j) (v : T.Node (j + 1)) :
    T.ancestorLE (Nat.le_succ_of_le h) v = T.ancestorLE h (T.parent j v) := by
  rw [T.ancestorLE_step h]
  rfl

end OrderedTree
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.WeightedTree ----
namespace OAI

/-!
# Positive edge weights and the actual path mass

Path mass is defined recursively from the parent maps and edge weights.
Its normalization and its mass on every descendant block are consequences
of the normalization at each parent.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

namespace WeightedTree

variable {T : OrderedTree} (W : WeightedTree T)

theorem pathWeight_pos (k : ℕ) (v : T.Node k) : 0 < W.pathWeight k v := by
  induction k with
  | zero => exact zero_lt_one
  | succ k ih => exact mul_pos (ih (T.parent k v)) (W.weight_pos k v)

theorem pathWeight_nonneg (k : ℕ) (v : T.Node k) : 0 ≤ W.pathWeight k v :=
  (W.pathWeight_pos k v).le

theorem sum_pathWeight (k : ℕ) : (∑ v, W.pathWeight k v) = 1 := by
  induction k with
  | zero => simp [pathWeight, OrderedTree.Node, T.size_zero]
  | succ k ih =>
      calc
        (∑ v, W.pathWeight (k + 1) v) = ∑ p, W.pathWeight k p := by
          simpa only [mul_one] using W.sum_pathWeight_parent k (fun _ => 1)
        _ = 1 := ih

/-- Every ancestor map pushes later-level path masses to earlier-level masses. -/
theorem sum_pathWeight_ancestor {i j : ℕ} (h : i ≤ j) (f : T.Node i → ℝ) :
    (∑ v, W.pathWeight j v * f (T.ancestorLE h v)) =
      ∑ p, W.pathWeight i p * f p := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le j h ih =>
      calc
        _ = ∑ v, W.pathWeight (j + 1) v * f (T.ancestorLE h (T.parent j v)) := by
          simp only [T.ancestorLE_step_apply h]
        _ = ∑ p, W.pathWeight j p * f (T.ancestorLE h p) :=
          W.sum_pathWeight_parent j (fun p => f (T.ancestorLE h p))
        _ = _ := ih

/-- The total mass below a node is exactly that node's path mass. -/
theorem descendant_sum_pathWeight {i j : ℕ} (h : i ≤ j) (p : T.Node i) :
    (∑ v ∈ T.descendants h p, W.pathWeight j v) = W.pathWeight i p := by
  classical
  have hf := W.sum_pathWeight_ancestor h (fun q => if q = p then (1 : ℝ) else 0)
  simpa [OrderedTree.descendants, Finset.sum_filter, mul_ite] using hf

end WeightedTree
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.TreeEvaluation ----
namespace OAI

/-!
# Actual nonlinear evaluation on a weighted ordered tree

The maps act on the literal subtype of a convex subset of a real normed
space. A cutoff value is an output: its own node map is not applied again.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace TreeEvaluation

variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Changing just one cutoff output has its actual path weight as sensitivity. -/
theorem evaluate_norm_sub_le_single (k : ℕ) (H H' : T.Node k → K)
    (v : T.Node k) (heq : ∀ w, w ≠ v → H w = H' w) :
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤
      W.pathWeight k v * ‖(H v : X) - H' v‖ := by
  classical
  refine (E.evaluate_norm_sub_le k H H').trans_eq ?_
  apply Finset.sum_eq_single v
  · intro w hw hwv
    rw [heq w hwv, sub_self, norm_zero, mul_zero]
  · simp

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- from OAI.Analysis.Nonexpansive.SwitchingNorm ----
namespace OAI

/-!
# Norm estimates for the actual switching differences

These elementary estimates are applied to root outputs from one chronological
switching experiment.  The construction of those outputs and their before- and
after-block bounds is separate from the linear-functional calculations here.
-/

noncomputable section

namespace ReflexiveFixedPoints

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A functional of operator norm at most one is bounded by the given norm. -/
theorem abs_functional_apply_le_norm (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) (z : X) :
    |f z| ≤ ‖z‖ := by
  calc
    |f z| = ‖f z‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f‖ * ‖z‖ := f.le_opNorm z
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hf (norm_nonneg z)
    _ = ‖z‖ := one_mul _

/-- Normalization of a single actual root increment preserves its subspace,
puts it in the unit ball, and reconstructs it upon multiplication by its weight.
The weight may be arbitrarily small; only strict positivity is required. -/
theorem normalized_switch_difference (Y : Submodule ℝ X)
    (U V : X) (W : ℝ) (hW : 0 < W)
    (hmem : U - V ∈ Y) (hnorm : ‖U - V‖ ≤ W) :
    W⁻¹ • (U - V) ∈ Y ∧
      ‖W⁻¹ • (U - V)‖ ≤ 1 ∧
      W • (W⁻¹ • (U - V)) = U - V := by
  refine ⟨Y.smul_mem W⁻¹ hmem, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hW)]
    calc
      W⁻¹ * ‖U - V‖ ≤ W⁻¹ * W :=
        mul_le_mul_of_nonneg_left hnorm (le_of_lt (inv_pos.mpr hW))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hW)
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hW), one_smul]

/-- Unit-ball vectors have detector score at most one. -/
theorem functional_apply_le_one (f : X →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1)
    (z : X) (hz : ‖z‖ ≤ 1) : f z ≤ 1 :=
  (le_abs_self _).trans ((abs_functional_apply_le_norm f hf z).trans hz)

end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.SwitchingStates ----
namespace OAI

/-!
# Actual root states during right-to-left switching

At cutoff `t`, the leaves with index strictly below `t` retain their labels;
all other leaves have the common terminal value.  Decreasing `t` by one is one
actual switch.  Every increment below is a difference of these evaluated root
states, so finite telescoping never assumes that a node map is linear.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints
namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Two consecutive cutoff states differ only at the leaf being switched. -/
theorem switchLeaves_succ_eq_of_ne (N : ℕ) (y : T.Node N → K) (b : K)
    (s w : T.Node N) (hws : w ≠ s) :
    E.switchLeaves N y b (s.val + 1) w = E.switchLeaves N y b s.val w := by
  have hv : w.val ≠ s.val := fun h => hws (Fin.ext h)
  have hc : (w.val < s.val + 1) ↔ (w.val < s.val) := by omega
  simp only [switchLeaves, hc]

/-- The root increment of one leaf has its actual path weight as its norm
bound. -/
theorem switchRoot_single_norm_le (N : ℕ) (y : T.Node N → K) (b : K)
    (s : T.Node N) :
    ‖(E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val‖ ≤
      W.pathWeight N s * ‖(y s : X) - b‖ := by
  have h := E.evaluate_norm_sub_le_single N
    (E.switchLeaves N y b (s.val + 1)) (E.switchLeaves N y b s.val) s
    (fun w hw => E.switchLeaves_succ_eq_of_ne N y b s w hw)
  simpa only [switchRoot, switchLeaves, Nat.lt_succ_self, ite_true,
    lt_self_iff_false, ite_false] using h

/-- Diameter one bounds the actual single-leaf root increment by its weight. -/
theorem switchRoot_single_norm_le_weight (N : ℕ) (y : T.Node N → K) (b : K)
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1) (s : T.Node N) :
    ‖(E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val‖ ≤
      W.pathWeight N s := by
  refine (E.switchRoot_single_norm_le N y b s).trans ?_
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hdiam (y s) b) (le_of_lt (W.pathWeight_pos N s))

/-- The actual normalized switch vector lies in the whole unit ball of any
subspace containing all differences of points in K. -/
theorem switchVector_mem_norm_reconstruct (N : ℕ) (y : T.Node N → K) (b : K)
    (Y : Submodule ℝ X) (hY : ∀ a c : K, (a : X) - c ∈ Y)
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1) (s : T.Node N) :
    E.switchVector N y b s ∈ Y ∧ ‖E.switchVector N y b s‖ ≤ 1 ∧
      W.pathWeight N s • E.switchVector N y b s =
        (E.switchRoot N y b (s.val + 1) : X) - E.switchRoot N y b s.val := by
  exact normalized_switch_difference Y
    (E.switchRoot N y b (s.val + 1)) (E.switchRoot N y b s.val)
    (W.pathWeight N s) (W.pathWeight_pos N s)
    (hY _ _) (E.switchRoot_single_norm_le_weight N y b hdiam s)

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.WeightedDeficit ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Finite weighted deficits used after the actual leaf-switching estimates.

The scalar argument allows zero leaf weights and returns a positive-weight leaf.
The application constructs its vectors using the strictly positive path weights,
then supplies the row estimates through `block_deficit_of_detection`.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- A block's actual telescoping identity turns detection into weighted deficit.

Only the detector is linear. The block outputs may come from nonlinear maps;
their actual finite telescoping identity is the input `htelescope`.
-/
theorem block_deficit_of_detection
    {X S : Type*} [AddCommGroup X] [Module ℝ X]
    (block : Finset S) (w : S → ℝ) (d : S → X)
    (f : X →ₗ[ℝ] ℝ) (U V : X) (W e : ℝ)
    (hmass : (∑ s ∈ block, w s) = W)
    (htelescope : (∑ s ∈ block, w s • d s) = U - V)
    (hdetect : W - 5 * e ≤ f (U - V)) :
    (∑ s ∈ block, w s * (1 - f (d s))) ≤ 5 * e := by
  have hlinear : (∑ s ∈ block, w s * f (d s)) = f (U - V) := by
    rw [← htelescope, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    simp only [map_smul, smul_eq_mul]
  calc
    (∑ s ∈ block, w s * (1 - f (d s))) = W - f (U - V) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hmass, hlinear]
    _ ≤ 5 * e := by linarith

end ReflexiveFixedPoints

end

end OAI

-- ---- from OAI.Analysis.Nonexpansive.FiniteWitness ----
namespace OAI

/-!
# A common path witness from actual block detection

Every vector in this finite argument is the normalized increment of the same
actual right-to-left switching experiment.  The construction of the terminal
point and the proof of block detection are supplied by the later tree-data
integration; they are not assumptions of the final fixed-point theorem.
-/

noncomputable section

open scoped BigOperators

namespace ReflexiveFixedPoints

namespace OrderedTree

namespace TruncationNode

variable {T : OrderedTree} {N : ℕ}

end TruncationNode
end OrderedTree

namespace TreeEvaluation

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

/-- Actual before/after block detection yields one leaf whose own normalized
root increment is detected at every nonroot point of its ancestor path.
There is no lower bound on the positive path weights. -/
theorem finite_witness_of_block_detection
    (N : ℕ) (y : T.Node N → K) (b : K)
    (Y : Submodule ℝ X) (hY : ∀ a c : K, (a : X) - c ∈ Y)
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1)
    (f : (k : ℕ) → T.Node k → X →L[ℝ] ℝ)
    (hf : ∀ k v, ‖f k v‖ ≤ 1)
    (e : T.TruncationNode N → ℝ)
    (he : (∑ v, e v) ≤ (1 : ℝ) / 128)
    (hblock : ∀ v : T.TruncationNode N,
      W.pathWeight (v.1.val + 1) v.2 - 5 * e v ≤
        f (v.1.val + 1) v.2
          ((E.beforeBlock v.levelBound y b v.2 : X) -
            E.afterBlock v.levelBound y b v.2)) :
    ∃ s : T.Node N,
      E.switchVector N y b s ∈ Y ∧ ‖E.switchVector N y b s‖ ≤ 1 ∧
        ∀ i (hi : i ≤ N), 0 < i →
          (1 : ℝ) / 2 ≤ f i (T.ancestorLE hi s) (E.switchVector N y b s) := by
  classical
  let R : T.TruncationNode N → T.Node N → Prop :=
    fun v s => T.ancestorLE v.levelBound s = v.2
  let a : T.TruncationNode N → T.Node N → ℝ :=
    fun v s => f (v.1.val + 1) v.2 (E.switchVector N y b s)
  have hvector (s : T.Node N) :=
    E.switchVector_mem_norm_reconstruct N y b Y hY hdiam s
  have ha : ∀ v s, R v s → a v s ≤ 1 := by
    intro v s hrs
    exact functional_apply_le_one (f (v.1.val + 1) v.2)
      (hf _ _) (E.switchVector N y b s) (hvector s).2.1
  have hrow : ∀ v : T.TruncationNode N,
      (∑ s, if R v s then W.pathWeight N s * (1 - a v s) else 0) ≤ 5 * e v := by
    intro v
    have hv := block_deficit_of_detection
      (T.descendants v.levelBound v.2) (W.pathWeight N) (E.switchVector N y b)
      (f (v.1.val + 1) v.2).toLinearMap
      (E.beforeBlock v.levelBound y b v.2) (E.afterBlock v.levelBound y b v.2)
      (W.pathWeight (v.1.val + 1) v.2) (e v)
      (W.descendant_sum_pathWeight v.levelBound v.2)
      (E.switchVector_block_telescope v.levelBound y b v.2) (hblock v)
    simpa only [OrderedTree.descendants, Finset.sum_filter, R, a,
      ContinuousLinearMap.coe_coe] using hv
  obtain ⟨_, _, s, _, hgood⟩ := finite_weighted_deficit R (W.pathWeight N) e a
    (W.pathWeight_nonneg N) (W.sum_pathWeight N) ha hrow he
  refine ⟨s, (hvector s).1, (hvector s).2.1, ?_⟩
  intro i hi hipos
  cases i with
  | zero => omega
  | succ k =>
      have hk : k < N := Nat.lt_of_succ_le hi
      let v : T.TruncationNode N := ⟨⟨k, hk⟩, T.ancestorLE hi s⟩
      have hv : R v s := rfl
      exact le_of_lt (hgood v hv)

end TreeEvaluation
end ReflexiveFixedPoints

end

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.finite_witness_of_block_detection := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.finite_witness_of_block_detection
