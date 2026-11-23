-- Prove2me | solution 2 for GrothendieckLB.Supplement.cq_nonlinear_head_check
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T20:06:09.179797+00:00
-- url     : https://prove2.me/submissions/ba96dc7d-70ca-4116-80b3-e83532081e47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_head_cutoff_invariance
import Theorems.Thm_GrothendieckLB_Supplement_cq_head_integer_comparisons_51
import Theorems.Thm_GrothendieckLB_Supplement_cq_head_integer_degrees_53_to_251
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic

private theorem concatenate (N : ℕ) (xs ys : List ℕ) :
    verifyList N (xs++ys) = (verifyList N xs && verifyList N ys) := by
  unfold verifyList
  exact List.all_append

theorem solution : cqNonlinearHeadCheck = true := by
  have hprefix : verifyList 251 (List.range 25) = true :=
    (cq_head_cutoff_invariance (n:=51) (N:=251) (by decide) (List.range 25)
      (fun j hj => by have := List.mem_range.mp hj; omega)).symm.trans cq_head_integer_comparisons_51
  have hparts : List.range 125 = List.range 25 ++ List.range' 25 100 := by decide +kernel
  rw [cqNonlinearHeadCheck,hparts,concatenate,hprefix,cq_head_integer_degrees_53_to_251]
  rfl
