-- Prove2me | solution 1 for InvIntegration.Behavioral.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:47:06.886339+00:00
-- url     : https://prove2.me/submissions/43c22e8e-3028-4190-99ee-c2f28023940b

import Mathlib
set_option autoImplicit false

open Filter Topology

theorem solution {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
    (f : X × Y → X) (hf : Continuous f) (γ : Y → X)
    (hγ : ∀ y : Y, f (γ y, y) = γ y) (huniq : ∀ (y : Y) (x : X), f (x, y) = x → x = γ y) :
    Continuous γ := by
  rw [continuous_iff_continuousAt]
  intro y
  refine tendsto_nhds_of_unique_mapClusterPt (l := 𝓝 y) (y := γ y) (f := γ) ?_
  intro x' hx'
  refine huniq y x' ?_
  rw [mapClusterPt_iff_ultrafilter] at hx'
  obtain ⟨U, hU, hUt⟩ := hx'
  have h1 : Tendsto (fun y' => (γ y', y')) U (𝓝 (x', y)) :=
    hUt.prodMk_nhds (tendsto_id.mono_right (by simpa using hU))
  have h2 : Tendsto (fun y' => f (γ y', y')) U (𝓝 (f (x', y))) :=
    (hf.tendsto _).comp h1
  have h3 : Tendsto (fun y' => f (γ y', y')) U (𝓝 x') := by
    simpa [hγ] using hUt
  exact tendsto_nhds_unique h2 h3
