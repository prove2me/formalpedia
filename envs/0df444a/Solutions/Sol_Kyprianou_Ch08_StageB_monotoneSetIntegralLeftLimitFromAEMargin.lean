-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.monotoneSetIntegralLeftLimitFromAEMargin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:41:05.517228+00:00
-- url     : https://prove2.me/submissions/e64fca2f-0008-4071-9801-b67f07bf1f79

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → ℝ) (A : ℝ → Set Ω)
    (hMeas : ∀ h : ℝ, MeasurableSet (A h))
    (hMono : Monotone A)
    (hInt : Integrable g P)
    (hMargin : ∀ y : ℝ, ∀ᵐ ω ∂P,
      g ω ≠ 0 → ω ∈ A y →
        ∃ h : ℝ, h < y ∧ ω ∈ A h) :
    ∀ y : ℝ,
      Tendsto (fun h : ℝ => (∫ ω in A h, g ω ∂P))
        (nhdsWithin y (Set.Iio y))
        (nhds (∫ ω in A y, g ω ∂P)) := by
  classical
  intro y
  let U : Set Ω := ⋃ i : Set.Iio y, A (i : ℝ)
  have hSubMono : Monotone (fun i : Set.Iio y => A (i : ℝ)) := by
    intro i j hij
    exact hMono hij
  have hUmeas : MeasurableSet U := by
    exact MeasurableSet.iUnion_of_monotone hSubMono (fun i => hMeas _)
  have hUsub : U ⊆ A y := by
    intro ω hω
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hω
    exact hMono (le_of_lt i.property) hi
  have hAe :
      ∀ᵐ ω ∂P, U.indicator g ω = (A y).indicator g ω := by
    filter_upwards [hMargin y] with ω hω
    by_cases hy : ω ∈ A y
    · by_cases hg : g ω = 0
      · simp [Set.indicator, hg]
      · obtain ⟨z, hz, hAz⟩ := hω hg hy
        have hu : ω ∈ U := Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hAz⟩
        simp [hu, hy]
    · have hu : ω ∉ U := fun hMem => hy (hUsub hMem)
      simp [hu, hy]
  have hEq :
      (∫ ω in U, g ω ∂P) = (∫ ω in A y, g ω ∂P) := by
    rw [← integral_indicator hUmeas, ← integral_indicator (hMeas y)]
    exact integral_congr_ae hAe
  have hTendsto :
      Tendsto (fun i : Set.Iio y => (∫ ω in A (i : ℝ), g ω ∂P))
        atTop (nhds (∫ ω in U, g ω ∂P)) := by
    exact tendsto_setIntegral_of_monotone (fun i => hMeas _)
      hSubMono (hInt.mono_measure Measure.restrict_le_self)
  rw [hEq] at hTendsto
  have hMap :
      Filter.map (fun i : Set.Iio y => (i : ℝ)) atTop =
        nhdsWithin y (Set.Iio y) := map_coe_Iio_atTop y
  rw [← hMap]
  exact (Filter.tendsto_map'_iff).mpr hTendsto
