-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_head_integer_degrees_53_to_251
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:43:44.358592+00:00
-- url     : https://prove2.me/submissions/16479480-cb1f-4c51-b183-31a64ff8e594
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_degree251_table_comparisons
import Theorems.Thm_GrothendieckLB_Supplement_cq_degree251_covariance_powers
import Theorems.Thm_GrothendieckLB_Supplement_cq_degree251_hermite_weights

open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic

theorem solution : verifyList 251 (List.range' 25 100) = true := by
  unfold verifyList
  rw [cq_degree251_hermite_weights, cq_degree251_covariance_powers]
  apply List.all_eq_true.mpr
  intro j hj
  have hj' : j<125 := by
    exact (List.mem_range'_1.mp hj).2
  exact decide_eq_true (cq_degree251_table_comparisons ⟨j,hj'⟩)
