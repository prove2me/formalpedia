-- Prove2me | solution 1 for OAI.ReflexiveFixedPoints.WeightedTree.sum_pathWeight_parent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:45:24.484981+00:00
-- url     : https://prove2.me/submissions/cfd2f9d2-abac-44f3-840b-9a542da4baba

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedTree

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.WeightedTree
open scoped BigOperators
variable {T : OrderedTree} (W : WeightedTree T)
theorem solution (k : ℕ) (f : T.Node k → ℝ) :
    (∑ c, W.pathWeight (k + 1) c * f (T.parent k c)) =
      ∑ p, W.pathWeight k p * f p := by
  simp only [pathWeight_succ]
  rw [← Finset.sum_fiberwise Finset.univ (T.parent k)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have : ∀ c ∈ Finset.univ.filter (fun c => T.parent k c = p),
      W.pathWeight k (T.parent k c) * W.weight k c * f (T.parent k c) =
        W.pathWeight k p * f p * W.weight k c := by
    intro c hc
    rw [(Finset.mem_filter.mp hc).2]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, W.weight_sum k p, mul_one]
