-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_packet_interpolation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T04:49:49.92941+00:00
-- url     : https://prove2.me/submissions/640ff9ff-8758-4b58-9aa3-3c5494681472
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_unbounded_packet_interpolation
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_packet_degree_reduction

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    (nu : ℝ) (hnu : 2 < nu) (d : FixedData nu) :
    ∃ R : ℚ, 0 < R ∧ ∀ᶠ n : ℕ in atTop,
      Function.Surjective (FormalInterpolation.packetMap d ((n : ℝ) * (R : ℝ))) := by
  obtain ⟨R, hR, hreduce⟩ :=
    FormalInterpolation.eventual_packet_degree_reduction nu hnu d
  refine ⟨R, hR, ?_⟩
  filter_upwards [hreduce] with n hn
  intro y
  obtain ⟨P, hP⟩ :=
    FormalInterpolation.unbounded_packet_interpolation d ((n : ℝ) * (R : ℝ)) y
  obtain ⟨Q, hQ⟩ := hn P
  refine ⟨Q, funext fun ρ => ?_⟩
  exact (hQ ρ).trans (hP ρ)
