-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_norm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:14:08.306884+00:00
-- url     : https://prove2.me/submissions/8687a699-c724-4b96-86d3-98118fb9b451

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/TreeEvaluation.lean:L118-L154
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_norm_sub_le. The node keeps its source
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
import Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_childAverage_norm_sub_le

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

theorem eq_root (v : T.Node 0) : v = T.root := by
  apply Fin.ext
  have hv : v.val < 1 := T.size_zero ▸ v.isLt
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hv)

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

/-- Each actual parent map is nonexpansive after taking its child average. -/
theorem collapse_norm_sub_le (k : ℕ) (H H' : T.Node (k + 1) → K)
    (p : T.Node k) :
    ‖(E.collapse k H p : X) - E.collapse k H' p‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
        W.weight k c * ‖(H c : X) - H' c‖ := by
  have hm : ‖(E.collapse k H p : X) - E.collapse k H' p‖ ≤
      ‖(E.childAverage k H p : X) - E.childAverage k H' p‖ := by
    simpa only [collapse, Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
      using (E.nonexpansive k p).dist_le_mul (E.childAverage k H p)
        (E.childAverage k H' p)
  exact hm.trans (E.childAverage_norm_sub_le k H H' p)

/-- The sensitivity estimate for actual nonlinear root outputs. -/
theorem evaluate_norm_sub_le (k : ℕ) (H H' : T.Node k → K) :
    ‖(E.evaluate k H : X) - E.evaluate k H'‖ ≤
      ∑ v, W.pathWeight k v * ‖(H v : X) - H' v‖ := by
  classical
  induction k with
  | zero =>
      have hsingle : (Finset.univ : Finset (T.Node 0)) = {T.root} := by
        ext v
        simp [T.eq_root v]
      simp [evaluate, hsingle, WeightedTree.pathWeight]
  | succ k ih =>
      calc
        ‖(E.evaluate (k + 1) H : X) - E.evaluate (k + 1) H'‖ ≤
            ∑ p, W.pathWeight k p *
              ‖(E.collapse k H p : X) - E.collapse k H' p‖ :=
          ih (E.collapse k H) (E.collapse k H')
        _ ≤ ∑ p, W.pathWeight k p *
            ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
              W.weight k c * ‖(H c : X) - H' c‖ := by
          apply Finset.sum_le_sum
          intro p hp
          exact mul_le_mul_of_nonneg_left (E.collapse_norm_sub_le k H H' p)
            (le_of_lt (W.pathWeight_pos k p))
        _ = ∑ p, ∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
            W.pathWeight k (T.parent k c) * W.weight k c *
              ‖(H c : X) - H' c‖ := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          have hcp := (Finset.mem_filter.mp hc).2
          rw [hcp, mul_assoc]
        _ = ∑ c, W.pathWeight (k + 1) c * ‖(H c : X) - H' c‖ := by
          rw [Finset.sum_fiberwise]
          rfl

end TreeEvaluation
end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_norm_sub_le.{u} := @_root_.OAI.ReflexiveFixedPoints.TreeEvaluation.evaluate_norm_sub_le.{u}
