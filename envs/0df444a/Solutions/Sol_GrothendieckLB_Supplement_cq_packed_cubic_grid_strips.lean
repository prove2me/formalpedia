-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_packed_cubic_grid_strips
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:33:33.578098+00:00
-- url     : https://prove2.me/submissions/1257b7e0-6efb-4539-beea-c255c279a0c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_cubic_grid_strips_0_to_7
import Theorems.Thm_GrothendieckLB_Supplement_cq_cubic_grid_strips_8_to_14
import Theorems.Thm_GrothendieckLB_Supplement_cq_final_cubic_grid_strip
open GrothendieckLB.Supplement CQHeadCertificate
theorem solution : ∀ c : ℕ, c < 16 → ∃ xs : Array Packed, stripChecks c xs=true := by
  intro c hc
  by_cases h0 : c < 8
  · exact cq_cubic_grid_strips_0_to_7 c (by omega) h0
  by_cases h1 : c < 15
  · exact cq_cubic_grid_strips_8_to_14 c (by omega) h1
  obtain rfl : c=15 := by omega
  exact cq_final_cubic_grid_strip
