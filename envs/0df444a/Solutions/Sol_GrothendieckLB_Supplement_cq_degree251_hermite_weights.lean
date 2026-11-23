-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_degree251_hermite_weights
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:29:31.663378+00:00
-- url     : https://prove2.me/submissions/39a83a5d-a275-4c84-b3cd-02537d99c9bd

import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite251_initial_grid
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_0_to_8
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_8_to_16
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_16_to_25
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_25_to_35
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_35_to_46
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_46_to_58
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_58_to_71
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_71_to_85
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_85_to_100
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_100_to_116
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_116_to_134
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_134_to_154
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_154_to_176
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_176_to_200
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_200_to_226
import Theorems.Thm_GrothendieckLB_Supplement_cq_hermite_rows_226_to_251

set_option maxRecDepth 150000
set_option maxHeartbeats 3000000
open GrothendieckLB.Supplement

theorem solution : (CQHeadArithmetic.grid 251 (CQHeadArithmetic.startAt 251) 251).weights = CQDegree251.weights := by
  have h0 := cq_hermite251_initial_grid
  have h1 := cq_hermite_rows_0_to_8 (CQHeadArithmetic.startAt 251) h0
  have h2 := cq_hermite_rows_8_to_16 (CQHeadArithmetic.startAt 251) h1
  have h3 := cq_hermite_rows_16_to_25 (CQHeadArithmetic.startAt 251) h2
  have h4 := cq_hermite_rows_25_to_35 (CQHeadArithmetic.startAt 251) h3
  have h5 := cq_hermite_rows_35_to_46 (CQHeadArithmetic.startAt 251) h4
  have h6 := cq_hermite_rows_46_to_58 (CQHeadArithmetic.startAt 251) h5
  have h7 := cq_hermite_rows_58_to_71 (CQHeadArithmetic.startAt 251) h6
  have h8 := cq_hermite_rows_71_to_85 (CQHeadArithmetic.startAt 251) h7
  have h9 := cq_hermite_rows_85_to_100 (CQHeadArithmetic.startAt 251) h8
  have h10 := cq_hermite_rows_100_to_116 (CQHeadArithmetic.startAt 251) h9
  have h11 := cq_hermite_rows_116_to_134 (CQHeadArithmetic.startAt 251) h10
  have h12 := cq_hermite_rows_134_to_154 (CQHeadArithmetic.startAt 251) h11
  have h13 := cq_hermite_rows_154_to_176 (CQHeadArithmetic.startAt 251) h12
  have h14 := cq_hermite_rows_176_to_200 (CQHeadArithmetic.startAt 251) h13
  have h15 := cq_hermite_rows_200_to_226 (CQHeadArithmetic.startAt 251) h14
  have h16 := cq_hermite_rows_226_to_251 (CQHeadArithmetic.startAt 251) h15
  calc
    _ = (CQHermite251.state 16).weights := congrArg CQHeadArithmetic.Grid.weights h16
    _ = _ := by
      exact congrArg (fun n => CQHeadArithmetic.tab n CQHermite251.weightRow) (show CQHermite251.cut 16+1=252 by decide +kernel)
