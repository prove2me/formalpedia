-- Prove2me | solution 1 for MultiwayGap2325.Main.beta_le_approximationFactor_eleven
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T05:30:26.944432+00:00
-- url     : https://prove2.me/submissions/18192304-9663-47e2-aa97-37e45c32461e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MultiwayGap2325_Main_Supplement_flow_lower_bound
import Theorems.Thm_MultiwayGap2325_Main_Supplement_computer_aided_flow_instance

open MeasureTheory Filter
open MultiwayGap2325.Main
open MultiwayGap2325.Main.Supplement

theorem solution
    (Ξ : Type) [MeasurableSpace Ξ]
    (P : MeasureTheory.Measure Ξ) [MeasureTheory.IsProbabilityMeasure P]
    (C : RandomNonOppositeCut 11 Ξ P) (α : ℝ) :
    HasApproximationFactor C α → beta ≤ α := by
  intro hα
  obtain ⟨D, hD, hL, hvalue⟩ :=
    MultiwayGap2325.Main.Supplement.computer_aided_flow_instance
  have h := MultiwayGap2325.Main.Supplement.flow_lower_bound
    11 (by norm_num) (249 / 400 : ℝ) (by norm_num) (by norm_num)
    D hD hL Ξ P C α hα
  have hratio := h.2.2.2.2.2.2.1
  rw [hvalue] at hratio
  exact hratio
