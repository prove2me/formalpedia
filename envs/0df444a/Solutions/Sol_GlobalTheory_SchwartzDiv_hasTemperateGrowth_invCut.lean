-- Prove2me | solution 1 for GlobalTheory.SchwartzDiv.hasTemperateGrowth_invCut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:24:48.603932+00:00
-- url     : https://prove2.me/submissions/7eefd9b2-9bf9-458c-a3e4-957d5c54d715

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
import Theorems.Thm_GlobalTheory_SchwartzDiv_invCut_of_one_le
import Theorems.Thm_GlobalTheory_SchwartzDiv_invCut_of_le_half
import Theorems.Thm_GlobalTheory_SchwartzDiv_contDiff_invCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric
noncomputable section
open GlobalTheory GlobalTheory.SchwartzDiv
namespace GlobalTheory.SchwartzDiv
theorem _root_.solution : invCut.HasTemperateGrowth := by
  refine ⟨contDiff_invCut, fun n => ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (contDiff_invCut.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).continuousOn
  refine ⟨0, max C (Nat.factorial n : ℝ), fun x => ?_⟩
  rw [pow_zero, mul_one]
  rcases lt_or_ge x (1 / 2) with h1 | h1
  · have : invCut =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      exact invCut_of_le_half hs.le
    rw [(this.iteratedFDeriv ℝ n).eq_of_nhds]
    simp only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
    exact le_max_of_le_right (Nat.cast_nonneg _)
  rcases le_or_gt x 2 with h2 | h2
  · exact (hC x ⟨h1, h2⟩).trans (le_max_left _ _)
  · have : invCut =ᶠ[𝓝 x] Inv.inv := by
      filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < x by linarith)] with s hs
      exact invCut_of_one_le hs.le
    rw [(this.iteratedFDeriv ℝ n).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, iter_deriv_inv]
    refine le_trans ?_ (le_max_right _ _)
    have hx : ‖x ^ (-1 - n : ℤ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (zpow_pos (by linarith) _)]
      exact zpow_le_one_of_nonpos₀ (by linarith) (by omega)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
    calc (Nat.factorial n : ℝ) * ‖x ^ (-1 - n : ℤ)‖ ≤ Nat.factorial n * 1 := by gcongr
      _ = Nat.factorial n := mul_one _
end GlobalTheory.SchwartzDiv
