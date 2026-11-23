-- Prove2me | solution 1 for Kyprianou.Ch01.nonnegativeSInfTranslatedImage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:55:41.509623+00:00
-- url     : https://prove2.me/submissions/796f12c9-7df3-4b65-91b8-59a0abd9c1a4

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (a : ℝ≥0) (S : Set ℝ≥0) (hS : S.Nonempty) :
    sInf ((fun s : ℝ≥0 => a + s) '' S) = a + sInf S := by
  classical
  have hNE : ((fun s : ℝ≥0 => a + s) '' S).Nonempty := hS.image _
  have ha : a ≤ sInf ((fun s : ℝ≥0 => a + s) '' S) := by
    refine le_csInf hNE ?_
    rintro u ⟨s, hs, rfl⟩
    exact le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ s from zero_le)
  have hupper : a + sInf S ≤ sInf ((fun s : ℝ≥0 => a + s) '' S) := by
    refine le_csInf hNE ?_
    rintro u ⟨s, hs, rfl⟩
    simpa only [add_comm] using
      (add_le_add_left (csInf_le (OrderBot.bddBelow S) hs) a)
  have hdiff : sInf ((fun s : ℝ≥0 => a + s) '' S) - a ≤ sInf S := by
    refine le_csInf hS ?_
    intro s hs
    apply tsub_le_iff_right.mpr
    have hBound : sInf ((fun z : ℝ≥0 => a + z) '' S) ≤ a + s :=
      csInf_le (OrderBot.bddBelow _) ⟨s, hs, rfl⟩
    simpa only [add_comm] using hBound
  refine le_antisymm ?_ hupper
  calc
    sInf ((fun s : ℝ≥0 => a + s) '' S) =
        a + (sInf ((fun s : ℝ≥0 => a + s) '' S) - a) :=
      (add_tsub_cancel_of_le ha).symm
    _ ≤ a + sInf S := by
      simpa only [add_comm] using (add_le_add_left hdiff a)
