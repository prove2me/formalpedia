-- Prove2me | solution 1 for Kyprianou.Ch04.finiteExtendedSupToRealV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:28:41.056282+00:00
-- url     : https://prove2.me/submissions/d63ba1cc-c459-4a63-97cf-9156820807ef

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite extended supremum of a nonnegative path equals the real supremum. -/
theorem solution (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hn : ∀ t, 0 ≤ f t) (S : ℝ≥0∞) (hS : S < ⊤)
    (heq : (⨆ t : Iic T, ENNReal.ofReal (f t)) = S) :
    sSup (f '' Iic T) = S.toReal := by
  have hle (t : ℝ≥0) (ht : t ≤ T) : f t ≤ S.toReal := by
    have h : ENNReal.ofReal (f t) ≤ S := by
      rw [← heq]
      exact le_iSup (fun t : Iic T => ENNReal.ofReal (f t)) ⟨t,ht⟩
    simpa only [ENNReal.toReal_ofReal (hn t)] using ENNReal.toReal_mono hS.ne h
  have hb : BddAbove (f '' Iic T) := ⟨S.toReal, by
    rintro _ ⟨t,ht,rfl⟩
    exact hle t ht⟩
  have hmem : f 0 ∈ f '' Iic T := ⟨0,show (0 : ℝ≥0) ≤ T from zero_le,rfl⟩
  have hnn : 0 ≤ sSup (f '' Iic T) := (hn 0).trans (le_csSup hb hmem)
  refine le_antisymm (csSup_le ⟨_,hmem⟩ ?_) ?_
  · rintro _ ⟨t,ht,rfl⟩
    exact hle t ht
  · have hh : S ≤ ENNReal.ofReal (sSup (f '' Iic T)) := by
      rw [← heq]
      exact iSup_le fun t => ENNReal.ofReal_le_ofReal (le_csSup hb ⟨t,t.2,rfl⟩)
    simpa only [ENNReal.toReal_ofReal hnn] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
