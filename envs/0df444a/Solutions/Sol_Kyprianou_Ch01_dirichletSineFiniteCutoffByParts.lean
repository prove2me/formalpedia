-- Prove2me | solution 1 for Kyprianou.Ch01.dirichletSineFiniteCutoffByParts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:36:20.88255+00:00
-- url     : https://prove2.me/submissions/a6ab8ddf-22ad-4032-86b8-fae814befa43

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_sineCosineLowerCutoffLimits
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineFiniteIntegrationByParts
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineEndpointZero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem solution (R : ℝ) (hR : 0 < R) :
    (∫ x in (0 : ℝ)..R, Real.sin x / x) =
      (∫ x in Set.Ioc (0 : ℝ) R, (1 - Real.cos x) / x ^ 2 ∂volume) +
      (1 - Real.cos R) / R := by
  have hlimits := Kyprianou.Ch01.sineCosineLowerCutoffLimits R hR
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a ∧ a ≤ R := by
    have hRnhds : Set.Iio R ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds hR
    have hRwithin : Set.Iio R ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds hRnhds
    filter_upwards [self_mem_nhdsWithin, hRwithin] with a ha hlt
    exact ⟨ha, le_of_lt hlt⟩
  have hfinite : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      (∫ x in a..R, Real.sin x / x) =
        (∫ x in a..R, (1 - Real.cos x) / x ^ 2) +
          (1 - Real.cos R) / R - (1 - Real.cos a) / a := by
    filter_upwards [hsmall] with a ha
    have h := Kyprianou.Ch01.stableAlphaOneCosineFiniteIntegrationByParts
      a R ha.1 ha.2
    linarith
  have hzero := Kyprianou.Ch01.stableAlphaOneCosineEndpointZero
  have hConst : Tendsto
      (fun _ : ℝ => (1 - Real.cos R) / R)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 - Real.cos R) / R)) :=
    tendsto_const_nhds
  have hAdd : Tendsto
      (fun a : ℝ =>
        (∫ x in a..R, (1 - Real.cos x) / x ^ 2) +
          (1 - Real.cos R) / R)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ x in Set.Ioc (0 : ℝ) R,
        (1 - Real.cos x) / x ^ 2 ∂volume) +
          (1 - Real.cos R) / R)) :=
    hlimits.2.add hConst
  have hsum := hAdd.sub hzero
  have hfinite' :
      (fun a : ℝ =>
        (∫ x in a..R, (1 - Real.cos x) / x ^ 2) +
          (1 - Real.cos R) / R - (1 - Real.cos a) / a) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun a : ℝ => ∫ x in a..R, Real.sin x / x) := by
    filter_upwards [hfinite] with a ha
    exact ha.symm
  have htarget' := hsum.congr' hfinite'
  have htarget : Tendsto
      (fun a : ℝ => ∫ x in a..R, Real.sin x / x)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∫ x in Set.Ioc (0 : ℝ) R,
        (1 - Real.cos x) / x ^ 2 ∂volume) +
          (1 - Real.cos R) / R)) := by
    simpa using htarget'
  exact tendsto_nhds_unique hlimits.1 htarget
