-- Prove2me | solution 1 for LinParamBandits.PEGE.unit_ball_sbar
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T09:17:44.182976+00:00
-- url     : https://prove2.me/submissions/a463904c-625b-4d17-97b5-4c95f58bcd1b

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open LinParamBandits.PEGE
open LinParamBandits.LowerBound

private theorem sbar_of_unit {r : ℕ} (U : Set (Vec r))
    (bounded : ∀ u ∈ U, ‖u‖ ≤ 1)
    (units : ∀ u : Vec r, ‖u‖ = 1 → u ∈ U) : SBAR U 1 := by
  have best_unit : ∀ z u : Vec r, ‖z‖ = 1 → IsBestArm U z u → u = z := by
    intro z u hz hu
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ)
    · simpa [hz] using bounded u hu.1
    · have hlo := hu.2 z (units z hz)
      have hhi := (real_inner_le_norm u z).trans (by
        simpa [hz] using bounded u hu.1)
      simpa [hz, real_inner_self_eq_norm_sq] using le_antisymm hhi (by simpa [hz, real_inner_self_eq_norm_sq] using hlo)
  constructor
  · intro z hz
    let w : Vec r := ‖z‖⁻¹ • z
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hw : ‖w‖ = 1 := by
      simp [w, norm_smul, abs_of_pos (inv_pos.mpr hn), hn.ne']
    have zw : z = ‖z‖ • w := by
      simp [w, smul_smul, hn.ne']
    have linear : ∀ a : Vec r, inner ℝ a z = ‖z‖ * inner ℝ a w := by
      intro a
      calc
        inner ℝ a z = inner ℝ a (‖z‖ • w) := congrArg (inner ℝ a) zw
        _ = ‖z‖ * inner ℝ a w := real_inner_smul_right _ _ _
    have bw : IsBestArm U z w := by
      refine ⟨units w hw, ?_⟩
      intro v hv
      rw [linear v, linear w]
      apply mul_le_mul_of_nonneg_left _ hn.le
      have hi := real_inner_le_norm v w
      simpa [hw, real_inner_self_eq_norm_sq] using hi.trans (by simpa [hw] using bounded v hv)
    refine ⟨w, bw, ?_⟩
    intro v hv
    apply best_unit w v hw
    refine ⟨hv.1, ?_⟩
    intro a ha
    have hi := hv.2 a ha
    rw [linear a, linear v] at hi
    exact (mul_le_mul_iff_right₀ hn).mp hi
  · intro z y u v hz hy hu hv
    rw [best_unit z u hz hu, best_unit y v hy hv, one_mul]

theorem solution (r : ℕ) : SBAR (Metric.closedBall (0 : LinParamBandits.LowerBound.Vec r) 1) 1 := by
  apply sbar_of_unit
  · intro u hu
    simpa [Metric.mem_closedBall, dist_zero_right] using hu
  · intro u hu
    simp [Metric.mem_closedBall, dist_zero_right, hu]

#print axioms solution
