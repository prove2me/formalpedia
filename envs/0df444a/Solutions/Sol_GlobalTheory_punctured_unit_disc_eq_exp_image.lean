-- Prove2me | solution 1 for GlobalTheory.punctured_unit_disc_eq_exp_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:38.832155+00:00
-- url     : https://prove2.me/submissions/5f8d2c1a-7cfa-4552-ba1c-f4e9b35b08ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPreconnectedPolydiscFirstCoordsNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    Metric.ball (0:ℂ) 1 \ {0} = Complex.exp '' {z : ℂ | z.re < 0} := by
  ext w
  constructor
  · rintro ⟨hb, h0⟩
    have h0' : w ≠ 0 := h0
    refine ⟨Complex.log w, ?_, Complex.exp_log h0'⟩
    rw [Set.mem_setOf_eq, Complex.log_re]
    rw [Metric.mem_ball, dist_zero_right] at hb
    exact Real.log_neg (norm_pos_iff.mpr h0') hb
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hz
    · exact Complex.exp_ne_zero z
end GlobalTheory
