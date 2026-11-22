-- Prove2me | solution 1 for MasulloRH.low_height_resolvent_tsum_zero_at_three
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T03:55:01.162998+00:00
-- url     : https://prove2.me/submissions/6c0cb504-b3a1-468a-abd2-2e29063afd9e

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_low_height_trace_zero_set_empty

set_option autoImplicit false

open MasulloRH Set

theorem solution :
    (∑' ρ : ZetaZerosInTraceStrip (1 / 2),
      (if |ρ.val.im| ^ 2 < 36 then
        zeroResolventTerm (1 / 2) (3 : ℂ) ρ
       else 0)) = 0 := by
  have hEmpty := MasulloRH.low_height_trace_zero_set_empty
  have hzero : ∀ ρ : ZetaZerosInTraceStrip (1 / 2),
      (if |ρ.val.im| ^ 2 < 36 then
        zeroResolventTerm (1 / 2) (3 : ℂ) ρ
       else 0) = 0 := by
    intro ρ
    by_cases h : |ρ.val.im| ^ 2 < 36
    · have hmem : ρ ∈ {ρ : ZetaZerosInTraceStrip (1 / 2) | |ρ.val.im| ^ 2 < 36} := h
      rw [hEmpty] at hmem
      simpa using hmem
    · have h' : ¬ ρ.val.im ^ 2 < 36 := by
        intro h'
        exact h (by simpa only [sq_abs] using h')
      simp [h']
  simp_rw [hzero]
  exact tsum_zero
