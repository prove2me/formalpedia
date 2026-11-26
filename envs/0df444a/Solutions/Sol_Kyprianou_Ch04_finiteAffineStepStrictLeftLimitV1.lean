-- Prove2me | solution 1 for Kyprianou.Ch04.finiteAffineStepStrictLeftLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:29:35.441617+00:00
-- url     : https://prove2.me/submissions/cfc4de66-0441-47c0-9403-1fe58564249c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_marked_step_sum_left_limit
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- The strict left limit of a locally affine finite step path is the strict jump sum. -/
theorem solution (S : Finset NNReal) (j : NNReal → ℝ) (d : ℝ)
    (T : NNReal) (Y L : NNReal → ℝ)
    (hY : ∀ u ≤ T, Y u = d * (u : ℝ) + ∑ r ∈ S, if r ≤ u then j r else 0)
    (hL : ∀ u, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (L u))) :
    ∀ u, 0 < u → u ≤ T →
      L u = d * (u : ℝ) + ∑ r ∈ S, if r < u then j r else 0 := by
  intro u hu huT
  have hD : Tendsto (fun v : NNReal => d * (v : ℝ)) (𝓝[<] u) (𝓝 (d * (u : ℝ))) :=
    (continuous_const.mul NNReal.continuous_coe).continuousAt.continuousWithinAt
  have hs := AvramDividend.Classical.finite_marked_step_sum_left_limit S id j u
  have h := hD.add hs
  have he : Y =ᶠ[𝓝[<] u] (fun v => d * (v : ℝ) + ∑ r ∈ S, if r ≤ v then j r else 0) := by
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact hY v (hv.le.trans huT)
  haveI : NeBot (𝓝[<] u) := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    rw [closure_Iio' (show (Iio u).Nonempty from ⟨0,hu⟩)]
    exact (show u ≤ u from le_rfl)
  exact tendsto_nhds_unique (hL u hu) (h.congr' he.symm)
