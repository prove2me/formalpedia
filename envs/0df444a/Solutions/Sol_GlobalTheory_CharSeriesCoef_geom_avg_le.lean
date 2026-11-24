-- Prove2me | solution 1 for GlobalTheory.CharSeriesCoef.geom_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:47.194934+00:00
-- url     : https://prove2.me/submissions/e1e101a6-b61a-41e6-9925-200039329f7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CharSeriesCoef
namespace GlobalTheory.CharSeriesCoef
theorem _root_.solution {ζ : ℂ} (hζ : ζ ≠ 1) (h1 : ‖ζ‖ = 1) (K : ℕ) (hK : 0 < K) :
    ‖(K:ℂ)⁻¹ * ∑ k : Fin K, ζ ^ (k:ℕ)‖ ≤ 2 / (K * ‖ζ - 1‖) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ζ ^ k) K, geom_sum_eq hζ K]
  have hz : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ)
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hnum : ‖ζ ^ K - 1‖ ≤ 2 := by
    calc ‖ζ ^ K - 1‖ ≤ ‖ζ ^ K‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, h1]; norm_num
  rw [norm_mul, norm_div, norm_inv, Complex.norm_natCast]
  calc (K:ℝ)⁻¹ * (‖ζ ^ K - 1‖ / ‖ζ - 1‖) ≤ (K:ℝ)⁻¹ * (2 / ‖ζ - 1‖) := by gcongr
    _ = 2 / (K * ‖ζ - 1‖) := by field_simp
end GlobalTheory.CharSeriesCoef
