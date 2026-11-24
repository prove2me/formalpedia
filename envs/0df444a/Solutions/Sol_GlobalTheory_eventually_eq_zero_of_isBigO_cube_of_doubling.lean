-- Prove2me | solution 1 for GlobalTheory.eventually_eq_zero_of_isBigO_cube_of_doubling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:00.514395+00:00
-- url     : https://prove2.me/submissions/cbe439fc-e856-41fe-8b55-2316e7f9ea16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EventuallyEqZeroOfIsBigOCubeOfDoubling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
private lemma eq_zero_of_cube_bound_of_doubling {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (F : E → ℂ) (ε C : ℝ)
    (hP : ∀ w : E, ‖w‖ < ε → ‖F w‖ ≤ C * ‖w‖ ^ 3 ∧ F ((2 : ℂ) • w) = 3 * F w + F (-w))
    (z : E) (hz : ‖z‖ < ε) : F z = 0 := by

  set M : E → ℝ := fun w => ‖F w‖ + ‖F (-w)‖ with hM
  have step : ∀ w : E, ‖w‖ < ε → M ((2 : ℂ) • w) ≤ 4 * M w := by
    intro w hw
    have h1 := (hP w hw).2
    have h2 := (hP (-w) (by rwa [norm_neg])).2
    rw [neg_neg] at h2
    simp only [hM]
    rw [← smul_neg, h1, h2]
    have e1 : ‖3 * F w + F (-w)‖ ≤ 3 * ‖F w‖ + ‖F (-w)‖ :=
      (norm_add_le _ _).trans (by simp)
    have e2 : ‖3 * F (-w) + F w‖ ≤ 3 * ‖F (-w)‖ + ‖F w‖ :=
      (norm_add_le _ _).trans (by simp)
    linarith
  set w : ℕ → E := fun n => ((2 : ℂ)⁻¹) ^ n • z with hw
  have hnorm : ∀ n, ‖w n‖ = ((2 : ℝ) ^ n)⁻¹ * ‖z‖ := by
    intro n
    simp [hw, norm_smul]
  have hsmall : ∀ n, ‖w n‖ < ε := by
    intro n
    rw [hnorm]
    have h1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    calc ((2 : ℝ) ^ n)⁻¹ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < ε := by simpa using hz
  have hsucc : ∀ n, w n = (2 : ℂ) • w (n + 1) := by
    intro n
    simp only [hw, smul_smul]
    congr 1
    rw [pow_succ]
    field_simp
  have hiter : ∀ n : ℕ, M z ≤ 4 ^ n * M (w n) := by
    intro n
    induction n with
    | zero => simp [hw]
    | succ n ih =>
      calc M z ≤ 4 ^ n * M (w n) := ih
        _ = 4 ^ n * M ((2 : ℂ) • w (n + 1)) := by rw [← hsucc]
        _ ≤ 4 ^ n * (4 * M (w (n + 1))) := by
          gcongr
          exact step _ (hsmall _)
        _ = 4 ^ (n + 1) * M (w (n + 1)) := by ring
  have hbound : ∀ n : ℕ, M z ≤ (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n := by
    intro n
    have hb : M (w n) ≤ 2 * C * ‖w n‖ ^ 3 := by
      have a1 := (hP (w n) (hsmall n)).1
      have a2 := (hP (-w n) (by rw [norm_neg]; exact hsmall n)).1
      rw [norm_neg] at a2
      simp only [hM]
      linarith
    have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    calc M z ≤ 4 ^ n * M (w n) := hiter n
      _ ≤ 4 ^ n * (2 * C * ‖w n‖ ^ 3) := by gcongr
      _ = (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n := by
        have h2 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by
          rw [← mul_pow]
          norm_num
        rw [hnorm, h4]
        field_simp
        linear_combination (-(C * ‖z‖ ^ 3)) * h2
  have hlim : Filter.Tendsto (fun n : ℕ => (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n)
      Filter.atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (2 * C * ‖z‖ ^ 3)
    simpa using this
  have hM0 : M z ≤ 0 := ge_of_tendsto' hlim hbound
  have : ‖F z‖ ≤ 0 := by
    have := norm_nonneg (F (-z))
    simp only [hM] at hM0
    linarith
  exact norm_le_zero_iff.1 this
end GlobalTheory
end

set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → ℂ),
      F =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      (∀ᶠ z in 𝓝 0, F ((2 : ℂ) • z) = 3 * F z + F (-z)) → ∀ᶠ z in 𝓝 0, F z = 0) := by
  intro E _ _ F hO hrel
  obtain ⟨C, hC⟩ := hO.bound
  have hev : ∀ᶠ z in 𝓝 (0 : E), ‖F z‖ ≤ C * ‖z‖ ^ 3 ∧ F ((2 : ℂ) • z) = 3 * F z + F (-z) := by
    filter_upwards [hC, hrel] with z h1 h2
    exact ⟨by simpa using h1, h2⟩
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 hev
  filter_upwards [Metric.ball_mem_nhds (0 : E) hε] with z hz
  exact eq_zero_of_cube_bound_of_doubling F ε C (fun w hw => hP (by simpa using hw)) z
    (by simpa using hz)
end GlobalTheory
