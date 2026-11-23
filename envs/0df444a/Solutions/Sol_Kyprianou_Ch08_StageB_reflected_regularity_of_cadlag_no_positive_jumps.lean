-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.reflected_regularity_of_cadlag_no_positive_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:48:04.636868+00:00
-- url     : https://prove2.me/submissions/71b6199e-53c1-4468-b476-2fb9ce361428

import Mathlib.Topology.Order.LeftRight
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Theorems.Thm_AvramDividend_Classical_runningSup_left_continuous_of_no_upward_jump

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (X : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hc : IsCadlag fun t => X t ω) (hX0 : X 0 ω = 0)
    (hmono : Monotone (fun t : ℝ≥0 => runningSup X t ω))
    (hdom : ∀ t : ℝ≥0, X t ω ≤ runningSup X t ω)
    (hrepr : ∀ T : ℝ≥0, runningSup X T ω = ⨆ u : Icc (0 : ℝ≥0) T, X u.1 ω)
    (hNoUp : ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l) → X t ω ≤ l) :
    (∀ t : ℝ≥0, ContinuousWithinAt (fun s : ℝ≥0 => reflectAtSup X 0 s ω) (Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => reflectAtSup X 0 s ω) (nhdsWithin t (Iio t)) (nhds l)) ∧
    (∀ (t : ℝ≥0) (l : ℝ), 0 < t → Tendsto (fun s : ℝ≥0 => reflectAtSup X 0 s ω) (nhdsWithin t (Iio t)) (nhds l) → l ≤ reflectAtSup X 0 t ω) := by
  let f : ℝ≥0 → ℝ := fun s => X s ω
  let M : ℝ≥0 → ℝ := fun s => runningSup X s ω
  have hcadlag : ∀ t, IsCadlagAt f t := hc
  have hMr (t : ℝ≥0) : ContinuousWithinAt M (Ici t) t :=
    runningSup_right_continuous_of_right_continuous f M
      hmono hdom hrepr (fun s => (hcadlag s).1) t
  have hMl (t : ℝ≥0) (ht : 0 < t) (l : ℝ)
      (hl : Tendsto f (𝓝[<] t) (𝓝 l)) :
      ContinuousWithinAt M (Iio t) t :=
    runningSup_left_continuous_of_no_upward_jump f M
      hmono hdom hrepr t ht l hl (hNoUp t l ht hl)
  have hRr (t : ℝ≥0) :
      ContinuousWithinAt (fun s : ℝ≥0 => reflectAtSup X 0 s ω) (Ici t) t := by
    have hmax : Tendsto (fun s => max (0 : ℝ) (M s)) (𝓝[≥] t)
        (𝓝 (max 0 (M t))) :=
      tendsto_const_nhds.max (hMr t)
    have hsub := hmax.sub ((hcadlag t).1)
    change Tendsto (fun s : ℝ≥0 => reflectAtSup X 0 s ω)
      (𝓝[≥] t) (𝓝 (reflectAtSup X 0 t ω))
    simpa only [reflectAtSup] using hsub
  have hRl (t : ℝ≥0) (ht : 0 < t) :
      ∃ l : ℝ, Tendsto (fun s : ℝ≥0 => reflectAtSup X 0 s ω)
        (𝓝[<] t) (𝓝 l) := by
    obtain ⟨l, hl⟩ := (hcadlag t).2
    have hmax : Tendsto (fun s => max (0 : ℝ) (M s)) (𝓝[<] t)
        (𝓝 (max 0 (M t))) :=
      tendsto_const_nhds.max (hMl t ht l hl)
    refine ⟨max 0 (M t) - l, ?_⟩
    simpa only [reflectAtSup] using hmax.sub hl
  refine ⟨hRr, hRl, ?_⟩
  intro t r ht hr
  obtain ⟨l, hl⟩ := (hcadlag t).2
  have hmax : Tendsto (fun s => max (0 : ℝ) (M s)) (𝓝[<] t)
      (𝓝 (max 0 (M t))) :=
    tendsto_const_nhds.max (hMl t ht l hl)
  have hRlim : Tendsto (fun s : ℝ≥0 => reflectAtSup X 0 s ω)
      (𝓝[<] t) (𝓝 (max 0 (M t) - l)) := by
    simpa only [reflectAtSup] using hmax.sub hl
  haveI : NeBot (𝓝[<] t) :=
    nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have heq : r = max 0 (M t) - l :=
    tendsto_nhds_unique hr hRlim
  rw [heq]
  change max 0 (M t) - l ≤ max 0 (M t) - f t
  exact sub_le_sub_left (hNoUp t l ht hl) _
