-- Prove2me | solution 2 for MasulloRH.low_height_trace_zero_set_empty
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T03:45:22.421415+00:00
-- url     : https://prove2.me/submissions/3b8a94ba-4e5c-4666-b95f-50d30d0ba208

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
