-- Prove2me | solution 1 for Kyprianou.Ch06.rightContinuousSandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:00:57.6794+00:00
-- url     : https://prove2.me/submissions/23d1cbd2-e424-4246-a4d3-edd38ea26e3f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (F : NNReal → ENNReal) (t : NNReal) (y : ENNReal)
    (hCont : ContinuousAt F t)
    (hUpper : y ≤ F t)
    (hLower : ∀ s : NNReal, t < s → F s ≤ y) :
    y = F t := by
  apply le_antisymm hUpper
  have hTendsto :
      Tendsto F (𝓝[>] t) (𝓝 (F t)) :=
    hCont.tendsto.mono_left nhdsWithin_le_nhds
  have hEventually : ∀ᶠ s in 𝓝[>] t, F s ≤ y := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hLower s hs
  exact le_of_tendsto hTendsto hEventually
