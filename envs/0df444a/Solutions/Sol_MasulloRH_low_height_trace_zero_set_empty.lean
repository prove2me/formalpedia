-- Prove2me | solution 1 for MasulloRH.low_height_trace_zero_set_empty
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T03:45:18.35454+00:00
-- url     : https://prove2.me/submissions/0bd38885-d551-4854-89c1-e876d1a64c19

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six

set_option autoImplicit false

open MasulloRH Set

theorem solution :
    {ρ : ZetaZerosInTraceStrip (1 / 2) | |ρ.val.im| ^ 2 < 36} = (∅ : Set (ZetaZerosInTraceStrip (1 / 2))) := by
  ext ρ
  constructor
  · intro hρ
    change |ρ.val.im| ^ 2 < 36 at hρ
    have habs : 0 ≤ |ρ.val.im| := abs_nonneg _
    have hbound : |ρ.val.im| ≤ 6 := by
      nlinarith [hρ]
    exact (ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six
      ρ.property.2.1 ρ.property.2.2.1 hbound) ρ.property.1
  · intro hρ
    simpa using hρ
