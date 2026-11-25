-- Prove2me | solution 1 for GlobalTheory.exists_smooth_step_sharp_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:40:39.599151+00:00
-- url     : https://prove2.me/submissions/6852ad47-1c19-42a4-a243-1912c71b07b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSmoothStepSharpSlope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ρ ε : ℝ) (hε : 0 < ε) (h4 : 4 * ε < ρ) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ (∀ u, u ≤ ε → η u = 1) ∧ (∀ u, ρ - ε ≤ u → η u = 0) ∧
      (∀ u, 0 ≤ η u) ∧ (∀ u, η u ≤ 1) ∧ ∀ u, -(1 / (ρ - 4 * ε)) ≤ deriv η u := by
  let ψ : ContDiffBump (ρ / 2 : ℝ) := ⟨ρ / 2 - 2 * ε, ρ / 2 - ε, by linarith, by linarith⟩
  have hψc : Continuous ψ := ψ.continuous
  have hψ0 : ∀ t, t ≤ ε ∨ ρ - ε ≤ t → ψ t = 0 := by
    intro t ht
    apply ψ.zero_of_le_dist
    rw [Real.dist_eq]
    show ρ / 2 - ε ≤ |t - ρ / 2|
    rcases ht with ht | ht
    · rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
    · exact le_trans (by linarith) (le_abs_self _)
  have hψ1 : ∀ t, 2 * ε ≤ t → t ≤ ρ - 2 * ε → ψ t = 1 := by
    intro t h1 h2
    apply ψ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |t - ρ / 2| ≤ ρ / 2 - 2 * ε
    rw [abs_le]; constructor <;> linarith
  have hII : ∀ a b, IntervalIntegrable ψ volume a b := fun a b => hψc.intervalIntegrable a b
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun u => ∫ t in ε..u, ψ t := ⟨_, rfl⟩
  have hFd : ∀ u, HasDerivAt F (ψ u) u := by
    intro u; rw [hF]; exact (hψc.integral_hasStrictDerivAt ε u).hasDerivAt
  have hFs : ContDiff ℝ ∞ F := by
    refine contDiff_infty_iff_deriv.2 ⟨fun u => (hFd u).differentiableAt, ?_⟩
    have h : deriv F = ψ := funext fun u => (hFd u).deriv
    rw [h]; exact ψ.contDiff
  have hFlow : ∀ u, u ≤ ε → F u = 0 := by
    intro u hu
    rw [hF]
    show ∫ t in ε..u, ψ t = 0
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      exact hψ0 t (Or.inl (le_trans ht.2 (sup_le le_rfl hu)))
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ t in ε..(ρ - ε), ψ t := ⟨_, rfl⟩
  have hFhigh : ∀ u, ρ - ε ≤ u → F u = I := by
    intro u hu
    rw [hF, hI]
    show ∫ t in ε..u, ψ t = ∫ t in ε..(ρ - ε), ψ t
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII ε (ρ - ε)) (hII (ρ - ε) u),
      intervalIntegral.integral_congr (a := ρ - ε) (b := u) (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      exact hψ0 t (Or.inr (le_trans (le_inf le_rfl hu) ht.1))
  have hIge : ρ - 4 * ε ≤ I := by
    rw [hI]
    calc ρ - 4 * ε = ∫ _ in (2 * ε)..(ρ - 2 * ε), (1 : ℝ) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring
      _ = ∫ t in (2 * ε)..(ρ - 2 * ε), ψ t := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le (by linarith)] at ht
          exact (hψ1 t ht.1 ht.2).symm
      _ ≤ ∫ t in ε..(ρ - ε), ψ t :=
          intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
            (Filter.Eventually.of_forall fun t => ψ.nonneg) (hII _ _)
  have hIpos : 0 < I := by linarith
  have hFrange : ∀ u, 0 ≤ F u ∧ F u ≤ I := by
    intro u
    rcases le_total u ε with h | h
    · rw [hFlow u h]; exact ⟨le_rfl, hIpos.le⟩
    rcases le_total (ρ - ε) u with h' | h'
    · rw [hFhigh u h']; exact ⟨hIpos.le, le_rfl⟩
    have hsplit : F u + ∫ t in u..(ρ - ε), ψ t = I := by
      rw [hF, hI]; exact intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)
    have h1 : 0 ≤ F u := by
      rw [hF]; exact intervalIntegral.integral_nonneg h fun t _ => ψ.nonneg
    have h2 : 0 ≤ ∫ t in u..(ρ - ε), ψ t := intervalIntegral.integral_nonneg h' fun t _ => ψ.nonneg
    exact ⟨h1, by linarith⟩
  refine ⟨fun u => 1 - F u / I, contDiff_const.sub (hFs.div_const I), ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; simp [hFlow u hu]
  · intro u hu; simp [hFhigh u hu, hIpos.ne']
  · intro u
    rw [sub_nonneg, div_le_one hIpos]; exact (hFrange u).2
  · intro u
    have : 0 ≤ F u / I := div_nonneg (hFrange u).1 hIpos.le
    linarith
  · intro u
    have hd : HasDerivAt (fun u => 1 - F u / I) (-(ψ u / I)) u :=
      ((hFd u).div_const I).const_sub 1
    rw [hd.deriv, neg_le_neg_iff, div_le_div_iff₀ hIpos (by linarith)]
    nlinarith [ψ.le_one (x := u), ψ.nonneg (x := u)]
end GlobalTheory
