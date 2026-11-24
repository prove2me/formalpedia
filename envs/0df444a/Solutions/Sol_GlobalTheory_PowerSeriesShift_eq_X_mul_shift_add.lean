-- Prove2me | solution 1 for GlobalTheory.PowerSeriesShift.eq_X_mul_shift_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:32.13028+00:00
-- url     : https://prove2.me/submissions/5b458bd3-df4f-4a9b-bfbf-9d05febb29bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqXMulShiftAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesShift
namespace GlobalTheory.PowerSeriesShift
theorem _root_.solution {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) :
    f = MvPowerSeries.X i * shift i f + free i f := by
  classical
  ext m
  rw [map_add, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases h : m i = 0
  · have h1 : ¬ Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [if_neg h1, zero_add]
    change _ = if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
    rw [if_pos h]
  · have h1 : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [if_pos h1, one_mul]
    change _ = MvPowerSeries.coeff (Finsupp.single i 1 + (m - Finsupp.single i 1)) f +
      if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
    rw [if_neg h, add_zero, add_tsub_cancel_of_le h1]
end GlobalTheory.PowerSeriesShift
