-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaBound.partial_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:25.456118+00:00
-- url     : https://prove2.me/submissions/ffb2f8bf-9831-47b6-afd0-e7ee2d52a113

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_sum_terms_le
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_harmonic_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaBound
open Finset
namespace GlobalTheory.CompanionTheory.DigammaBound
theorem _root_.solution (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (hzM : ‖z‖ ≤ M)
    (n : ℕ) (hn : M ≤ n) :
    ‖((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ))‖ ≤
      6 + 2 * Real.log M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hn1 : 1 ≤ n := hM.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set H : ℝ := ∑ i ∈ range n, ((i : ℝ) + 1)⁻¹ with hH
  have hlow : Real.log n ≤ H := by
    have h := log_add_one_le_harmonic n
    rw [harmonic_cast] at h
    have h2 : Real.log n ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log hn0 (by linarith)
    push_cast at h
    linarith
  have hup : H ≤ 1 + Real.log n := by
    have h := harmonic_le_one_add_log n
    rw [harmonic_cast] at h
    exact h
  have hHc : ((H : ℝ) : ℂ) = ∑ i ∈ range n, 1 / ((i : ℂ) + 1) := by
    rw [hH]
    push_cast
    simp
  have hdecomp : ((Real.log n : ℝ) : ℂ) - ∑ k ∈ range (n + 1), 1 / (z + (k : ℂ)) =
      ((Real.log n - H : ℝ) : ℂ) +
        ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))) - 1 / z := by
    rw [sum_range_succ', sum_sub_distrib, ← hHc]
    push_cast
    simp only [add_zero]
    ring
  have h1 : ‖((Real.log n - H : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h2 : ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ ≤
      2 * (1 + Real.log M) + 1 := by
    refine (norm_sum_le _ _).trans ((sum_terms_le z hz M hM n hn).trans ?_)
    have hHM := harmonic_le_one_add_log M
    rw [harmonic_cast] at hHM
    have h3 : ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) ≤ 1 := by
      have h4 : ‖z‖ * (1 / (M : ℝ)) ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_one hM0).2 hzM
      have h5 : 0 ≤ ‖z‖ * (1 / (n : ℝ)) := by positivity
      rw [mul_sub]
      linarith
    linarith
  have h3 : ‖1 / z‖ ≤ 2 := by
    have hzn : 1 / 2 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
    rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
    linarith
  rw [hdecomp]
  calc _ ≤ ‖((Real.log n - H : ℝ) : ℂ) +
        ∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ + ‖1 / z‖ := norm_sub_le _ _
    _ ≤ ‖((Real.log n - H : ℝ) : ℂ)‖ +
        ‖∑ i ∈ range n, (1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1)))‖ + ‖1 / z‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 6 + 2 * Real.log M := by linarith
end GlobalTheory.CompanionTheory.DigammaBound
