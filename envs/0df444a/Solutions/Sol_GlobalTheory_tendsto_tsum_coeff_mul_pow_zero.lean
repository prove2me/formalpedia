-- Prove2me | solution 1 for GlobalTheory.tendsto_tsum_coeff_mul_pow_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:55.056605+00:00
-- url     : https://prove2.me/submissions/8b90a9f1-d777-470e-9841-e614c2430881

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DetBoundedConvergentPowerSeriesMatrixETwoPi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open Filter Topology
namespace GlobalTheory
theorem _root_.solution (a : ℕ → ℂ) (q₀ : ℂ) (hq₀ : q₀ ≠ 0)
    (hs : Summable (fun m : ℕ => a m * q₀ ^ m)) :
    Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0) (𝓝 (a 0)) := by
  have hlim : Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0)
      (𝓝 (∑' m : ℕ, if m = 0 then a 0 else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖a m * q₀ ^ m‖) hs.norm ?_ ?_
    · intro m
      have hc : Continuous (fun q : ℂ => a m * q ^ m) := by fun_prop
      have h := hc.tendsto 0
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa using h
      · have h0 : a m * (0 : ℂ) ^ m = 0 := by simp [hm.ne']
        rw [h0] at h
        simpa [hm.ne'] using h
    · have hpos : 0 < ‖q₀‖ := norm_pos_iff.mpr hq₀
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hpos] with q hq m
      have hq' : ‖q‖ ≤ ‖q₀‖ := by
        have : ‖q‖ < ‖q₀‖ := by simpa using hq
        exact this.le
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      gcongr
  simpa using hlim
end GlobalTheory
