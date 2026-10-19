-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.TreeEvaluation.sum_descendant_weighted_children
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:49:18.637656+00:00
-- url     : https://prove2.me/submissions/3125664f-5096-449e-a500-e820d82f619e

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

theorem rfp_eval_le (k : ℕ) : ∀ (H H' : T.Node k → K),
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤
      ∑ v, W.pathWeight k v * ‖(H v : X) - H' v‖ := by
  induction k with
  | zero =>
    intro H H'
    simp only [evaluate_zero, WeightedTree.pathWeight_zero, one_mul]
    exact Finset.single_le_sum (f := fun v => ‖(H v : X) - H' v‖)
      (fun v _ => norm_nonneg _) (Finset.mem_univ _)
  | succ k ih =>
    intro H H'
    rw [evaluate_succ, evaluate_succ]
    refine (ih _ _).trans ?_
    calc ∑ p, W.pathWeight k p * ‖(E.collapse k H p : X) - E.collapse k H' p‖
        ≤ ∑ p, W.pathWeight k p * ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
            W.weight k c * ‖(H c : X) - H' c‖ := by
          refine Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left ?_ ?_)
          · exact (rfp_map_le E k p _ _).trans (rfp_avg_le E k H H' p)
          · exact rfp_pw_nonneg W k p
      _ = ∑ c, W.pathWeight (k + 1) c * ‖(H c : X) - H' c‖ := by
          rw [← Finset.sum_fiberwise Finset.univ (T.parent k)
            (fun c => W.pathWeight (k + 1) c * ‖(H c : X) - H' c‖)]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun c hc => ?_)
          rw [WeightedTree.pathWeight_succ, (Finset.mem_filter.mp hc).2]; ring

theorem rfp_sum_desc_children {k n : ℕ} (h : k ≤ n)
    (v : T.Node k) (f : T.Node (n + 1) → ℝ) :
    (∑ p ∈ T.descendants h v, W.pathWeight n p *
      (∑ c ∈ Finset.univ.filter (fun c => T.parent n c = p), W.weight n c * f c)) =
      ∑ c ∈ T.descendants (Nat.le_succ_of_le h) v, W.pathWeight (n + 1) c * f c := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := T.descendants (Nat.le_succ_of_le h) v)
    (t := T.descendants h v) (g := T.parent n)]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mul_sum]
    have hs : (T.descendants (Nat.le_succ_of_le h) v).filter (fun c => T.parent n c = p) =
        Finset.univ.filter (fun c => T.parent n c = p) := by
      ext c
      simp only [Finset.mem_filter, OrderedTree.mem_descendants, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro hc
        refine ⟨?_, hc⟩
        rw [T.ancestorLE_step h]
        simp only [Function.comp_apply, hc]
        exact (OrderedTree.mem_descendants _ _ _ _).1 hp
    rw [hs]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [WeightedTree.pathWeight_succ, (Finset.mem_filter.mp hc).2]; ring
  · intro c hc
    rw [OrderedTree.mem_descendants] at hc ⊢
    rw [T.ancestorLE_step h] at hc
    exact hc

theorem rfp_sub_congr {i j : ℕ} (h : i ≤ j) :
    ∀ (H H' : T.Node j → K) (v : T.Node i),
      (∀ s, T.ancestorLE h s = v → H s = H' s) →
      E.subtreeOutput h H v = E.subtreeOutput h H' v := by
  induction h using Nat.leRec with
  | refl =>
    intro H H' v hv
    simp only [subtreeOutput_refl_apply]
    exact hv v (by simp)
  | @le_succ_of_le j h ih =>
    intro H H' v hv
    rw [E.subtreeOutput_step h, E.subtreeOutput_step h]
    apply ih
    intro s hs
    simp only [collapse]
    congr 1
    apply Subtype.ext
    simp only [childAverage_val]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [hv c (by rw [T.ancestorLE_step h]; simp [(Finset.mem_filter.mp hc).2, hs])]

theorem rfp_sub_scaled {k N : ℕ} (h : k ≤ N) :
    ∀ (H H' : T.Node N → K) (v : T.Node k),
      W.pathWeight k v *
          ‖(E.subtreeOutput h H v : X) - E.subtreeOutput h H' v‖ ≤
        ∑ s ∈ T.descendants h v, W.pathWeight N s * ‖(H s : X) - H' s‖ := by
  induction h using Nat.leRec with
  | refl =>
    intro H H' v
    simp only [subtreeOutput_refl_apply]
    rw [Finset.sum_eq_single v]
    · intro b hb hbv
      simp at hb; exact absurd hb hbv
    · intro hv; simp at hv
  | @le_succ_of_le j h ih =>
    intro H H' v
    rw [E.subtreeOutput_step h, E.subtreeOutput_step h]
    refine (ih _ _ v).trans ?_
    rw [← rfp_sum_desc_children h v]
    refine Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left ?_ (rfp_pw_nonneg W j p))
    exact (rfp_map_le E j p _ _).trans (rfp_avg_le E j H H' p)

theorem solution {k n : ℕ} (h : k ≤ n)
    (v : T.Node k) (f : T.Node (n + 1) → ℝ) :
    (∑ p ∈ T.descendants h v, W.pathWeight n p *
      (∑ c ∈ Finset.univ.filter (fun c => T.parent n c = p), W.weight n c * f c)) =
      ∑ c ∈ T.descendants (Nat.le_succ_of_le h) v, W.pathWeight (n + 1) c * f c :=
  rfp_sum_desc_children h v f
