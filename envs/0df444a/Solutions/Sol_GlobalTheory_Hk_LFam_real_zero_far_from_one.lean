-- Prove2me | solution 1 for GlobalTheory.Hk.LFam.real_zero_far_from_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:06:11.353833+00:00
-- url     : https://prove2.me/submissions/3d8ea593-9802-4732-8009-cf44456d37f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormRayClassFamilyFOneGeOfRealCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsRayClassLFunctionRealZeroFarFromOne
import Theorems.Thm_GlobalTheory_Hk_LFam_norm_deriv_F_le_near_one
import Theorems.Thm_GlobalTheory_T_norm_rayClassFamily_F_one_ge_of_real_character
import Theorems.Thm_GlobalTheory_T_rayClassFamily_logDeriv_re_gt_one
import Theorems.Thm_GlobalTheory_T_rayClassLFunctionFamily_continuation_growth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
namespace LFam
theorem _root_.solution : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (β : ℝ), χ * χ = 1 → 3 / 4 ≤ β → 𝓕.F χ β = 0 → c / 𝓕.B ^ A ≤ 1 - β := by
  obtain ⟨A, c, hA, hc, h⟩ := GlobalTheory.T.norm_rayClassFamily_F_one_ge_of_real_character
  refine ⟨A + 1, c / 18000, by linarith, by positivity, ?_⟩
  intro 𝓕 χ β hχ hβ h0
  have hB : 0 < 𝓕.B := by linarith [𝓕.B_ge]
  have hβ1 : β ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ β (by simpa using hlt)).2.2.1 h0
  obtain ⟨han, -, -, -⟩ := GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ
  have hn : ‖(1 : ℂ) - β‖ = 1 - β := by
    rw [show (1 : ℂ) - β = ((1 - β : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hmv := (convex_closedBall (1 : ℂ) (1 / 4)).norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := 𝓕.F χ)
    (C := 18000 * 𝓕.B) (x := (β : ℂ)) (y := 1)
    (by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h3 := (abs_le.1 ((Complex.abs_re_le_norm (z - 1)).trans hz)).1
      simp only [sub_re, one_re] at h3
      exact (han z (by simp only [Set.mem_setOf_eq]; linarith)).differentiableAt)
    (fun z hz => 𝓕.norm_deriv_F_le_near_one χ z hz)
    (by rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, hn]; linarith)
    (Metric.mem_closedBall_self (by norm_num))
  rw [h0, sub_zero, hn] at hmv
  have h1 := (h 𝓕 χ hχ).trans hmv
  have hp : 0 < 𝓕.B ^ A := Real.rpow_pos_of_pos hB A
  rw [Real.rpow_add hB, Real.rpow_one, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hp] at h1
  nlinarith
end LFam
end GlobalTheory.Hk
