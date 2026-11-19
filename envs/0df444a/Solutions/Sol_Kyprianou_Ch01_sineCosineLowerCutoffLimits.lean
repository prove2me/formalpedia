-- Prove2me | solution 1 for Kyprianou.Ch01.sineCosineLowerCutoffLimits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:26:46.135939+00:00
-- url     : https://prove2.me/submissions/5b0916e5-4b4e-456b-927e-4c06e07d1e74

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_intervalIntegralLowerCutoffTendsto
import Theorems.Thm_Kyprianou_Ch01_sineCosineFiniteIntervalIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem solution (R : ℝ) (hR : 0 < R) :
    Tendsto (fun a : ℝ => ∫ x in a..R, Real.sin x / x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in (0 : ℝ)..R, Real.sin x / x)) ∧
    Tendsto (fun a : ℝ => ∫ x in a..R, (1 - Real.cos x) / x ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in Set.Ioc (0 : ℝ) R,
        (1 - Real.cos x) / x ^ 2 ∂volume)) := by
  obtain ⟨hSin, hCos⟩ :=
    Kyprianou.Ch01.sineCosineFiniteIntervalIntegrable R hR
  have hs := Kyprianou.Ch01.intervalIntegralLowerCutoffTendsto
    (fun x : ℝ => Real.sin x / x) R hR hSin
  have hc := Kyprianou.Ch01.intervalIntegralLowerCutoffTendsto
    (fun x : ℝ => (1 - Real.cos x) / x ^ 2) R hR hCos
  rw [intervalIntegral.integral_of_le (le_of_lt hR)] at hc
  exact ⟨hs, hc⟩
