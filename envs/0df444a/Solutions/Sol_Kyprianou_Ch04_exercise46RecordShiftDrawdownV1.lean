-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46RecordShiftDrawdownV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:27:05.378957+00:00
-- url     : https://prove2.me/submissions/9b060a33-7e78-4391-8517-4978e8481e8f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (f : NNReal → Real) (s t : NNReal)
    (hrecord : ∀ u ≤ s, f u ≤ f s)
    (hb : BddAbove (f '' Iic (s+t))) :
    sSup ((fun u : NNReal => f (s+u)-f s) '' Iic t) -
      (f (s+t)-f s) = sSup (f '' Iic (s+t)) - f (s+t) := by
  let A : Set Real := f '' Iic (s+t)
  let B : Set Real := (fun u : NNReal => f (s+u)) '' Iic t
  have hsub : B ⊆ A := by
    rintro x ⟨u, hu, rfl⟩
    exact ⟨s+u, add_le_add_right hu s, rfl⟩
  have hbB : BddAbove B := hb.mono hsub
  have h0 : f s ∈ B := ⟨0, by simp, by simp⟩
  have he : sSup A = sSup B := by
    apply le_antisymm
    · apply csSup_le ⟨f s, hsub h0⟩
      rintro x ⟨u, hu, rfl⟩
      by_cases h : u ≤ s
      · exact (hrecord u h).trans (le_csSup hbB h0)
      · have hs : s ≤ u := le_of_not_ge h
        apply le_csSup hbB
        refine ⟨u-s, ?_, ?_⟩
        · exact tsub_le_iff_left.mpr (by simpa [add_comm] using hu)
        · change f (s + (u-s)) = f u
          rw [add_tsub_cancel_of_le hs]
    · exact csSup_le_csSup hb ⟨f s,h0⟩ hsub
  have hIcc : Icc (0 : NNReal) t = Iic t := by ext u; simp
  have hshift := AvramDividend.Classical.shiftedSup_increment_eq_sup_sub f s t
    (by simpa [B,hIcc] using hbB)
  rw [hIcc] at hshift
  rw [hshift]
  change sSup B - f s - (f (s+t)-f s) = sSup A - f (s+t)
  rw [he]
  ring
