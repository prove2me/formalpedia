-- Prove2me | solution 1 for Kyprianou.Ch01.cosineKernelIntegralCutoffTendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:12:38.709059+00:00
-- url     : https://prove2.me/submissions/399adec5-e276-4258-90c7-f614e520862f

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem solution :
    Tendsto
      (fun R : ℝ =>
        ∫ x in Set.Ioc (0 : ℝ) R, (1 - Real.cos x) / x ^ 2 ∂volume)
      atTop
      (𝓝 (∫ x in Set.Ioi (0 : ℝ), (1 - Real.cos x) / x ^ 2 ∂volume)) := by
  have hUnion :
      (⋃ R : ℝ, Set.Ioc (0 : ℝ) R) = Set.Ioi (0 : ℝ) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨R, hx, _⟩
      exact hx
    · intro hx
      exact ⟨x, hx, le_rfl⟩
  have hMono : Monotone (fun R : ℝ => Set.Ioc (0 : ℝ) R) := by
    intro a b hab
    exact Set.Ioc_subset_Ioc_right hab
  have hInt :
      IntegrableOn (fun x : ℝ => (1 - Real.cos x) / x ^ 2)
        (⋃ R : ℝ, Set.Ioc (0 : ℝ) R) volume := by
    rw [hUnion]
    exact Kyprianou.Ch01.stableAlphaOneCosineIntegral.1
  have h :=
    MeasureTheory.tendsto_setIntegral_of_monotone
      (s := fun R : ℝ => Set.Ioc (0 : ℝ) R)
      (f := fun x : ℝ => (1 - Real.cos x) / x ^ 2)
      (μ := volume)
      (fun R => measurableSet_Ioc)
      hMono hInt
  simpa only [hUnion] using h
