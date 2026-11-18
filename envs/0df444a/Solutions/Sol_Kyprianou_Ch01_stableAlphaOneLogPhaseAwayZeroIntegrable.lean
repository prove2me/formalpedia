-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseAwayZeroIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:48:15.459894+00:00
-- url     : https://prove2.me/submissions/e799b7f3-a49b-4904-a0df-1895b49bad2e

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseKernelPointwiseTailBound
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseKernelMeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real Complex
set_option autoImplicit false
/-! Away from zero, the compensated index-one Levy kernel is dominated by (2+z)/r². -/
theorem solution
    (z delta : ℝ) (hz : 0 < z) (hdelta : 0 < delta) :
    IntegrableOn (fun r : ℝ => ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ))
      (Set.Ioi delta) := by
  have hpow : IntegrableOn (fun r : ℝ => r ^ (-2 : ℝ))
      (Ioi delta) :=
    (integrableOn_Ioi_rpow_iff hdelta).2 (by norm_num)
  apply (hpow.const_mul (2 + z)).mono'
  · exact (Kyprianou.Ch01.stableAlphaOneLogPhaseKernelMeasurable z).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact Kyprianou.Ch01.stableAlphaOneLogPhaseKernelPointwiseTailBound z r hz
      (hdelta.trans hr)
