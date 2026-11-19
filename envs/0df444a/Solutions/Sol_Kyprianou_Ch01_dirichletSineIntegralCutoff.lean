-- Prove2me | solution 1 for Kyprianou.Ch01.dirichletSineIntegralCutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:10:51.690036+00:00
-- url     : https://prove2.me/submissions/b8eeafd5-b033-4061-bc53-7d83b99e9093

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_dirichletSineFiniteCutoffByParts
import Theorems.Thm_Kyprianou_Ch01_cosineKernelIntegralCutoffTendsto
import Theorems.Thm_Kyprianou_Ch01_cosineEndpointDivTendstoZero
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineIntegralValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem solution :
    Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sin x / x)
    atTop (𝓝 (Real.pi / 2)) := by
  have hcos := Kyprianou.Ch01.cosineKernelIntegralCutoffTendsto
  have hbd := Kyprianou.Ch01.cosineEndpointDivTendstoZero
  have hsum := hcos.add hbd
  have heq :
      (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sin x / x) =ᶠ[atTop]
        (fun R : ℝ =>
          (∫ x in Set.Ioc (0 : ℝ) R,
            (1 - Real.cos x) / x ^ 2 ∂volume) +
          (1 - Real.cos R) / R) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact Kyprianou.Ch01.dirichletSineFiniteCutoffByParts R hR
  have htarget := hsum.congr' heq.symm
  simpa only [add_zero, Kyprianou.Ch01.stableAlphaOneCosineIntegralValue] using htarget
