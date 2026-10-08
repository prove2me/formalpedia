-- Prove2me | solution 1 for MazurTransfer.order27_zero_complete_aggregate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:17:08.59082+00:00
-- url     : https://prove2.me/submissions/76404933-c7a5-45d1-ab98-4eeca81c04b5

import Definitions.Def_MazurTransfer_Order27ZeroAggregateData
import Theorems.Thm_MazurTransfer_order27_zero_row_reordering
import Theorems.Thm_MazurTransfer_order27_zero_columns_0_5
import Theorems.Thm_MazurTransfer_order27_zero_columns_6_7
import Theorems.Thm_MazurTransfer_order27_zero_columns_8_9
import Theorems.Thm_MazurTransfer_order27_zero_columns_10_11
import Theorems.Thm_MazurTransfer_order27_zero_columns_12_17
import Theorems.Thm_MazurTransfer_order27_zero_columns_18_23

noncomputable section

open MazurTorsion.Kubert

theorem solution :
∀ f ξ : ℚ, tlAggregate f ξ = 0 := by
  intro f ξ
  rw [MazurTransfer.order27_zero_row_reordering f ξ]
  apply Finset.sum_eq_zero
  intro band _
  fin_cases band
  · exact (MazurTransfer.order27_zero_columns_0_5 f ξ).1
  · exact (MazurTransfer.order27_zero_columns_0_5 f ξ).2.1
  · exact (MazurTransfer.order27_zero_columns_0_5 f ξ).2.2.1
  · exact (MazurTransfer.order27_zero_columns_0_5 f ξ).2.2.2.1
  · exact (MazurTransfer.order27_zero_columns_0_5 f ξ).2.2.2.2.1
  · exact (MazurTransfer.order27_zero_columns_0_5 f ξ).2.2.2.2.2
  · exact (MazurTransfer.order27_zero_columns_6_7 f ξ).1
  · exact (MazurTransfer.order27_zero_columns_6_7 f ξ).2
  · exact (MazurTransfer.order27_zero_columns_8_9 f ξ).1
  · exact (MazurTransfer.order27_zero_columns_8_9 f ξ).2
  · exact (MazurTransfer.order27_zero_columns_10_11 f ξ).1
  · exact (MazurTransfer.order27_zero_columns_10_11 f ξ).2
  · exact (MazurTransfer.order27_zero_columns_12_17 f ξ).1
  · exact (MazurTransfer.order27_zero_columns_12_17 f ξ).2.1
  · exact (MazurTransfer.order27_zero_columns_12_17 f ξ).2.2.1
  · exact (MazurTransfer.order27_zero_columns_12_17 f ξ).2.2.2.1
  · exact (MazurTransfer.order27_zero_columns_12_17 f ξ).2.2.2.2.1
  · exact (MazurTransfer.order27_zero_columns_12_17 f ξ).2.2.2.2.2
  · exact (MazurTransfer.order27_zero_columns_18_23 f ξ).1
  · exact (MazurTransfer.order27_zero_columns_18_23 f ξ).2.1
  · exact (MazurTransfer.order27_zero_columns_18_23 f ξ).2.2.1
  · exact (MazurTransfer.order27_zero_columns_18_23 f ξ).2.2.2.1
  · exact (MazurTransfer.order27_zero_columns_18_23 f ξ).2.2.2.2.1
  · exact (MazurTransfer.order27_zero_columns_18_23 f ξ).2.2.2.2.2

#print axioms solution
end
