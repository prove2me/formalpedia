-- Prove2me | solution 1 for MasulloAudit.biorthogonal_norm_tendsto_top_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:32:26.718258+00:00
-- url     : https://prove2.me/submissions/5b6d6ea1-6b9c-495e-8eac-b9d330b54f98

import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

/-- If `η` is continuous at `t` and `f s` are continuous linear functionals with
`f s (η t) = 1` and `f s (η s) = 0` for `s ≠ t`, then `‖f s‖ → ∞` as `s → t`, `s ≠ t`. -/
theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (η : ℝ → E) (t : ℝ) (hη : ContinuousAt η t) (f : ℝ → E →L[𝕜] 𝕜)
    (h₁ : ∀ s, s ≠ t → f s (η t) = 1) (h₀ : ∀ s, s ≠ t → f s (η s) = 0) :
    Tendsto (fun s => ‖f s‖) (𝓝[≠] t) atTop := by
  -- lower bound `1 / ‖η t - η s‖ ≤ ‖f s‖`
  have key : ∀ s, s ≠ t → 0 < ‖η t - η s‖ ∧ 1 / ‖η t - η s‖ ≤ ‖f s‖ := by
    intro s hs
    have hval : f s (η t - η s) = 1 := by rw [map_sub, h₁ s hs, h₀ s hs, sub_zero]
    have hne : η t - η s ≠ 0 := by
      intro h; rw [h, map_zero] at hval; exact zero_ne_one hval
    have hpos : 0 < ‖η t - η s‖ := norm_pos_iff.mpr hne
    refine ⟨hpos, ?_⟩
    rw [div_le_iff₀ hpos]
    calc (1 : ℝ) = ‖f s (η t - η s)‖ := by rw [hval, norm_one]
      _ ≤ ‖f s‖ * ‖η t - η s‖ := (f s).le_opNorm _
  -- the denominator tends to `0⁺`
  have hd : Tendsto (fun s => ‖η t - η s‖) (𝓝[≠] t) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun s => ‖η t - η s‖) (𝓝 t) (𝓝 ‖η t - η t‖) :=
        (tendsto_const_nhds.sub hη).norm
      rw [sub_self, norm_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (key s hs).1
  have hinv : Tendsto (fun s => 1 / ‖η t - η s‖) (𝓝[≠] t) atTop := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hd
  refine tendsto_atTop_mono' _ ?_ hinv
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (key s hs).2

