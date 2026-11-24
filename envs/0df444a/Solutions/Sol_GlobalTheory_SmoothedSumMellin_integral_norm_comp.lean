-- Prove2me | solution 1 for GlobalTheory.SmoothedSumMellin.integral_norm_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:53:37.276312+00:00
-- url     : https://prove2.me/submissions/c33912a2-1011-4577-a1a7-76182bc40217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open Set Filter Asymptotics Topology
open GlobalTheory GlobalTheory.SmoothedSumMellin
namespace GlobalTheory.SmoothedSumMellin
theorem _root_.solution (wt : ℝ → ℂ) (s : ℂ) {n : ℝ} (hn : 0 < n) :
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt (t * n)‖
      = n ^ (-s.re) * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt t‖ := by
  have h1 : ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt (t * n)‖ =
      ∫ t in Ioi (0 : ℝ), (fun u : ℝ => (u / n) ^ (s.re - 1) * ‖wt u‖) (t * n) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only
    rw [_root_.norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, mul_div_cancel_right₀ t hn.ne']
    simp
  have h2 : ∫ t in Ioi (0 : ℝ), (t / n) ^ (s.re - 1) * ‖wt t‖ =
      n ^ (1 - s.re) * ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • wt t‖ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [_root_.norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Real.div_rpow ht'.le hn.le]
    have h3 : n ^ (1 - s.re) = (n ^ (s.re - 1))⁻¹ := by rw [← Real.rpow_neg hn.le, neg_sub]
    rw [h3]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  rw [h1, integral_comp_mul_right_Ioi (fun u : ℝ => (u / n) ^ (s.re - 1) * ‖wt u‖) 0 hn, zero_mul]
  rw [h2, smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add hn]
  congr 1
  ring
end GlobalTheory.SmoothedSumMellin
