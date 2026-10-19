-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.TreeEvaluation.before_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:54:23.71395+00:00
-- url     : https://prove2.me/submissions/91f41717-4538-4f74-8233-3534108017c4

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

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)
theorem rfp_pw_nonneg (W : WeightedTree T) (k : ℕ) (v : T.Node k) : 0 ≤ W.pathWeight k v := by
  induction k with
  | zero => simp
  | succ k ih => rw [WeightedTree.pathWeight_succ]; exact mul_nonneg (ih _) (W.weight_nonneg k v)

theorem rfp_avg_le (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) :
    ‖(E.childAverage k H p : X) - E.childAverage k H' p‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - H' c‖ := by
  rw [childAverage_val, childAverage_val, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun c _ => ?_)))
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (W.weight_pos k c)]

theorem rfp_map_le (k : ℕ) (v : T.Node k) (a b : K) :
    ‖(E.map k v a : X) - E.map k v b‖ ≤ ‖(a : X) - b‖ := by
  have := (E.nonexpansive k v).dist_le_mul a b
  simpa [Subtype.dist_eq, dist_eq_norm] using this

theorem rfp_weight_le_one (W : WeightedTree T) (k : ℕ) (c : T.Node (k + 1)) : W.weight k c ≤ 1 := by
  have h := W.weight_sum k (T.parent k c)
  rw [← h]
  exact Finset.single_le_sum (f := fun c => W.weight k c) (fun c _ => W.weight_nonneg k c)
    (by simp)

theorem rfp_pw_anc {i j : ℕ} (h : i ≤ j) (W : WeightedTree T) :
    ∀ s : T.Node j, W.pathWeight j s ≤ W.pathWeight i (T.ancestorLE h s) := by
  induction h using Nat.leRec with
  | refl => intro s; simp
  | @le_succ_of_le j h ih =>
    intro s
    rw [T.ancestorLE_step h, WeightedTree.pathWeight_succ, Function.comp_apply]
    calc W.pathWeight j (T.parent j s) * W.weight j s ≤ W.pathWeight j (T.parent j s) * 1 :=
          mul_le_mul_of_nonneg_left (rfp_weight_le_one W j s) (rfp_pw_nonneg W j _)
      _ ≤ _ := by rw [mul_one]; exact ih _

theorem rfp_pw_le_one (W : WeightedTree T) (k : ℕ) (v : T.Node k) : W.pathWeight k v ≤ 1 := by
  have := rfp_pw_anc (Nat.zero_le k) W v
  simpa using this

theorem rfp_focus
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (k : ℕ) : ∀ (H : T.Node k → K) (v : T.Node k) (z : K),
    ‖(E.evaluate k H : X) - z‖ ≤
      W.pathWeight k v * ‖(H v : X) - z‖ + (1 - W.pathWeight k v) +
        E.weightedPathDisplacement k v z := by
  induction k with
  | zero =>
    intro H v z
    have hv : v = T.root := by
      apply Fin.ext
      have h1 : (v : ℕ) < T.size 0 := v.isLt
      have h2 := T.size_zero
      simp [OrderedTree.root]; omega
    subst hv
    simp
  | succ k ih =>
    intro H v z
    set p := T.parent k v
    rw [evaluate_succ]
    refine (ih _ p z).trans ?_
    have hδ : ‖(E.collapse k H p : X) - z‖ ≤
        (W.weight k v * ‖(H v : X) - z‖ + (1 - W.weight k v)) + ‖(E.map k p z : X) - z‖ := by
      have h1 : ‖(E.collapse k H p : X) - z‖ ≤
          ‖(E.childAverage k H p : X) - z‖ + ‖(E.map k p z : X) - z‖ := by
        calc ‖(E.collapse k H p : X) - z‖
            ≤ ‖(E.collapse k H p : X) - E.map k p z‖ + ‖(E.map k p z : X) - z‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ _ := add_le_add_left (rfp_map_le E k p _ _) _
      refine h1.trans (add_le_add_left ?_ _)
      have h2 := rfp_avg_le E k H (fun _ => z) p
      rw [childAverage_const] at h2
      refine h2.trans ?_
      have hv : v ∈ Finset.univ.filter (fun c => T.parent k c = p) := by simp [p]
      rw [← Finset.add_sum_erase _ _ hv]
      have hsum := W.weight_sum k p
      rw [← Finset.add_sum_erase _ _ hv] at hsum
      have : ∑ c ∈ (Finset.univ.filter (fun c => T.parent k c = p)).erase v,
          W.weight k c * ‖(H c : X) - z‖ ≤
          ∑ c ∈ (Finset.univ.filter (fun c => T.parent k c = p)).erase v, W.weight k c :=
        Finset.sum_le_sum (fun c _ => by
          have := hdiam (H c) z
          nlinarith [W.weight_nonneg k c])
      linarith
    have hp := rfp_pw_nonneg W k p
    rw [WeightedTree.pathWeight_succ, weightedPathDisplacement_succ]
    have := mul_le_mul_of_nonneg_left hδ hp
    nlinarith

theorem rfp_wpd_le (k : ℕ) : ∀ (v : T.Node k) (z : K),
    E.weightedPathDisplacement k v z ≤ E.pathDisplacement k v z := by
  induction k with
  | zero => intro v z; simp
  | succ k ih =>
    intro v z
    rw [weightedPathDisplacement_succ, pathDisplacement_succ]
    have h1 := ih (T.parent k v) z
    have h2 := rfp_pw_le_one W k (T.parent k v)
    have h3 := norm_nonneg ((E.map k (T.parent k v) z : X) - z)
    nlinarith

theorem solution
    (hdiam : ∀ a b : K, ‖(a : X) - b‖ ≤ 1)
    (k : ℕ) (H : T.Node k → K) (v : T.Node k) (z : K) {e : ℝ}
    (hfocused : ‖(H v : X) - z‖ ≤ e)
    (hpath : E.pathDisplacement k v z ≤ e) :
    ‖(E.evaluate k H : X) - z‖ ≤ 1 - W.pathWeight k v + 2 * e := by
  have h1 := rfp_focus E hdiam k H v z
  have h2 := rfp_wpd_le E k v z
  have h3 := rfp_pw_le_one W k v
  have h4 := rfp_pw_nonneg W k v
  have he : 0 ≤ e := (norm_nonneg _).trans hfocused
  have h5 : W.pathWeight k v * ‖(H v : X) - z‖ ≤ e := by
    calc _ ≤ 1 * e := mul_le_mul h3 hfocused (norm_nonneg _) zero_le_one
      _ = e := one_mul e
  linarith
