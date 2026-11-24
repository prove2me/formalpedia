-- Prove2me | solution 1 for GlobalTheory.GaussCutoff.mem_closure_gauss_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:32:54.130564+00:00
-- url     : https://prove2.me/submissions/a714872e-1cc6-446a-83de-8a5d9fb7061a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemClosureWideGaussianMulSchwartz
import Theorems.Thm_GlobalTheory_GaussCutoff_cutMap_apply
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open scoped ContDiff Nat SchwartzMap
noncomputable section
open GlobalTheory.GaussCutoff
namespace GlobalTheory.GaussCutoff
theorem _root_.solution (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (h : SchwartzMap E ℂ) :
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := ((schwartz_withSeminorms ℝ E ℂ).mem_nhds_iff h U).1 hU
  choose K hK0 hK using fun m : ℕ × ℕ => cut_bound h m.1 m.2
  set M := ∑ m ∈ s, K m with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun m _ => hK0 m
  set c := min 1 (r / (2 * (M + 1))) with hc_def
  have hcpos : 0 < c := lt_min one_pos (by positivity)
  have hc1 : |c| ≤ 1 := by rw [abs_of_pos hcpos]; exact min_le_left _ _
  have hcr : c * (M + 1) ≤ r / 2 := by
    have := min_le_right 1 (r / (2 * (M + 1)))
    rw [← hc_def] at this
    calc c * (M + 1) ≤ r / (2 * (M + 1)) * (M + 1) := by gcongr
      _ = r / 2 := by field_simp
  refine ⟨h + cutMap h c hc1, hsub ?_, Real.pi * c ^ 2, by positivity, fun y => ?_⟩
  · rw [Seminorm.mem_ball, add_sub_cancel_left]
    refine Seminorm.finset_sup_apply_lt hr fun m hm => ?_
    have h1 : SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) ≤ |c| * K m :=
      SchwartzMap.seminorm_le_bound ℝ m.1 m.2 _ (mul_nonneg (abs_nonneg c) (hK0 m)) (hK m c hc1)
    have h2 : K m ≤ M := Finset.single_le_sum (fun m _ => hK0 m) hm
    show SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) < r
    rw [abs_of_pos hcpos] at h1
    nlinarith
  · rw [add_apply, cutMap_apply, cutErr, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    have e : -Real.pi * ‖c • y‖ ^ 2 = -(Real.pi * c ^ 2 * ‖y‖ ^ 2) := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    rw [e]; push_cast; ring
end GlobalTheory.GaussCutoff
