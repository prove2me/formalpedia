-- Prove2me | solution 1 for Giddings1999.multiparticle_boundary_suppression
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T09:38:46.073131+00:00
-- url     : https://prove2.me/submissions/93c20e3a-3bc7-4848-a8d4-44a794a4e962

import Mathlib
import Definitions.Def_Giddings1999_AdSModes

open Real Filter Topology
open Giddings1999

theorem solution (Δ Δb : ℝ) (h : Δ < Δb) :
    Tendsto (fun r => cos r ^ (Δb - Δ)) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hp : 0 < Δb - Δ := sub_pos.2 h
  have hc : ContinuousAt (fun r => cos r ^ (Δb - Δ)) (π / 2) :=
    (Real.continuousAt_rpow_const _ _ (Or.inr hp.le)).comp continuous_cos.continuousAt
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (π/2)))
  simpa [cos_pi_div_two, Real.zero_rpow hp.ne'] using this
