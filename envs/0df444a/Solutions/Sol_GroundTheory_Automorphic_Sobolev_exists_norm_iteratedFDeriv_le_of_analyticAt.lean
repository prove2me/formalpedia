-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.exists_norm_iteratedFDeriv_le_of_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:34.175796+00:00
-- url     : https://prove2.me/submissions/670c2d6f-e4fe-4108-886a-ab896465d17d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_AnalyticHypoSeries
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_nnnorm_changeOrigin_le_of_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open scoped ContDiff NNReal ENNReal Topology
open Set Filter
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {f : E → F} {x₀ : E}
    (hf : AnalyticAt ℝ f x₀) :
    ∃ r > 0, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k.factorial := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨ρ, hρ0', hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hρ0 : 0 < ρ := ENNReal.coe_pos.1 hρ0'
  obtain ⟨K, hK0, hK⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hρ0 (hρR.trans_le hp.r_le)
  set K' : ℝ≥0 := ⟨K, hK0.le⟩ with hK'def
  have hK' : ∀ n, ‖p n‖₊ ≤ K' / ρ ^ n := fun n ↦ by
    rw [← NNReal.coe_le_coe]; push_cast; exact hK n
  have hρ' : (0 : ℝ) < ρ := hρ0
  refine ⟨(ρ : ℝ) / 4, by positivity, 2 * K, 2 / ρ, by positivity, by positivity,
    fun y hy k ↦ ?_⟩
  set z := y - x₀ with hzdef
  have hz : ‖z‖ < (ρ : ℝ) / 4 := by rwa [Metric.mem_ball, dist_eq_norm] at hy
  have hzρ : ‖z‖₊ < ρ := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm]; linarith [norm_nonneg z]
  have hzR : (‖z‖₊ : ℝ≥0∞) < R := lt_trans (by exact_mod_cast hzρ) hρR
  have hq := hp.changeOrigin hzR
  have hxy : x₀ + z = y := by simp [hzdef]
  rw [hxy] at hq
  refine (norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall hq k).trans ?_
  have hb := nnnorm_changeOrigin_le_of_bound p hρ0 hK'
    (z := z) (by rw [← NNReal.coe_le_coe]; push_cast; linarith) (hzR.trans_le hp.r_le) k
  rw [← NNReal.coe_le_coe] at hb
  push_cast at hb
  have hb' : ‖p.changeOrigin z k‖ ≤ 2 * (K * (2 / ρ) ^ k) := hb
  calc (k.factorial : ℝ) * ‖p.changeOrigin z k‖ ≤ k.factorial * (2 * (K * (2 / ρ) ^ k)) := by
        gcongr
    _ = 2 * K * (2 / ρ) ^ k * k.factorial := by ring
end GroundTheory.Automorphic.Sobolev
