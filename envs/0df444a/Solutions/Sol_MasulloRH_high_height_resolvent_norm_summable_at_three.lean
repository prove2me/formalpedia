-- Prove2me | solution 1 for MasulloRH.high_height_resolvent_norm_summable_at_three
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T03:50:54.930916+00:00
-- url     : https://prove2.me/submissions/38693c7a-6f85-4eae-b0b4-9f9c09930e41

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_full_strip_resolvent_norm_summable_at_three

set_option autoImplicit false

open MasulloRH

theorem solution :
    Summable (fun ρ : ZetaZerosInTraceStrip (1 / 2) =>
      if 36 ≤ |ρ.val.im| ^ 2 then
        ‖zeroResolventTerm (1 / 2) (3 : ℂ) ρ‖
      else 0) := by
  have hsum := MasulloRH.full_strip_resolvent_norm_summable_at_three
  refine Summable.of_nonneg_of_le ?_ ?_ hsum
  · intro ρ
    by_cases h : 36 ≤ |ρ.val.im| ^ 2
    · have h' : 36 ≤ ρ.val.im ^ 2 := by simpa only [sq_abs] using h
      simp [h']
    · have h' : ¬36 ≤ ρ.val.im ^ 2 := by
        intro h'
        exact h (by simpa only [sq_abs] using h')
      simp [h']
  · intro ρ
    by_cases h : 36 ≤ |ρ.val.im| ^ 2
    · have h' : 36 ≤ ρ.val.im ^ 2 := by simpa only [sq_abs] using h
      simp [h']
    · have h' : ¬36 ≤ ρ.val.im ^ 2 := by
        intro h'
        exact h (by simpa only [sq_abs] using h')
      simp [h']
