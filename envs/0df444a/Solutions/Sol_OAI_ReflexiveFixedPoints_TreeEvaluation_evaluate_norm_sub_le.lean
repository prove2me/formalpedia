-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:49:10.299087+00:00
-- url     : https://prove2.me/submissions/9efc58b5-5be0-45a9-a45e-f32633d8d027

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

theorem solution (k : ℕ) (H H' : T.Node k → K) :
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤
      ∑ v, W.pathWeight k v * ‖(H v : X) - H' v‖ :=
  rfp_eval_le E k H H'
