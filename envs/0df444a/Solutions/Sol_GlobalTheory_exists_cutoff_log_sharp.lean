-- Prove2me | solution 1 for GlobalTheory.exists_cutoff_log_sharp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:38:19.340799+00:00
-- url     : https://prove2.me/submissions/1c69e38b-361c-4c45-91b6-caa725fa0992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSmoothStepSharpSlope
import Theorems.Thm_GlobalTheory_exists_smooth_step_sharp_slope

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
theorem _root_.solution : ∀ ρ0 θ : ℝ, 0 < ρ0 → 1 < θ → ∃ ε C : ℝ, 0 < ε ∧ ε < ρ0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ g : ℝ → ℝ,
    ContDiffOn ℝ ∞ g (Set.Ioi (-δ)) ∧ (∀ u, ρ0 - ε ≤ u → g u = 0) ∧
    (∀ u, 0 ≤ u → g u ≤ 0 ∧ 0 ≤ deriv g u ∧ -(θ / ρ0) ≤ deriv g u + u * deriv (deriv g) u) ∧
    (∀ u, 0 ≤ u → u ≤ ε → g u ≤ Real.log (u + δ) + C) ∧ ∀ u, ε / 2 ≤ u → -C ≤ g u := by
  intro ρ0 θ hρ hθ
  obtain ⟨ε, hε, hE⟩ : ∃ ε : ℝ, 0 < ε ∧ 8 * θ * ε = ρ0 * (θ - 1) :=
    ⟨ρ0 * (θ - 1) / (8 * θ), div_pos (mul_pos hρ (by linarith)) (by linarith), by field_simp⟩
  have h4 : 4 * ε < ρ0 := by nlinarith
  have hpos : 0 < ρ0 - 4 * ε := by linarith
  have hslope : 1 / (ρ0 - 4 * ε) ≤ θ / ρ0 := by
    rw [one_div_le hpos (by positivity), one_div_div, div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨η, hηs, hη1, hη0, hηnn, hηle, hηd⟩ := exists_smooth_step_sharp_slope ρ0 ε hε h4
  refine ⟨ε, 2 * ρ0 / ε + |Real.log ε|, hε, by linarith, ?_⟩
  intro δ hδ _
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun t => η t / (t + δ) := ⟨_, rfl⟩
  have hfv : ∀ t, f t = η t / (t + δ) := fun t => by rw [hf]
  have hfc : ContDiffOn ℝ ∞ f (Set.Ioi (-δ)) := by
    rw [hf]
    refine hηs.contDiffOn.div (contDiffOn_id.add contDiffOn_const) fun t ht => ?_
    have h : 0 < t + δ := by simp only [Set.mem_Ioi] at ht; linarith
    exact h.ne'
  have hfcont := hfc.continuousOn
  have hsub : ∀ a b, -δ < a → -δ < b → Set.uIcc a b ⊆ Set.Ioi (-δ) := fun a b ha hb t ht =>
    lt_of_lt_of_le (lt_inf_iff.2 ⟨ha, hb⟩) ht.1
  have hII : ∀ a b, -δ < a → -δ < b → IntervalIntegrable f volume a b :=
    fun a b ha hb => (hfcont.mono (hsub a b ha hb)).intervalIntegrable
  have hd : ∀ u, -δ < u → HasDerivAt (fun u => ∫ t in ρ0..u, f t) (f u) u := fun u hu =>
    intervalIntegral.integral_hasDerivAt_right (hII ρ0 u (by linarith) hu)
      (hfcont.stronglyMeasurableAtFilter isOpen_Ioi u hu)
      (hfcont.continuousAt (isOpen_Ioi.mem_nhds hu))
  have hnn : ∀ t, -δ < t → 0 ≤ f t := fun t ht => by
    rw [hfv]; exact div_nonneg (hηnn t) (by linarith)
  have hzero : ∀ u, ρ0 - ε ≤ u → ∫ t in ρ0..u, f t = 0 := by
    intro u hu
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      have h : ρ0 - ε ≤ t := le_trans (le_inf (by linarith) hu) ht.1
      simp only [hfv, hη0 t h, zero_div]
  have hle0 : ∀ u, 0 ≤ u → ∫ t in ρ0..u, f t ≤ 0 := by
    intro u hu
    rcases le_total u ρ0 with h | h
    · rw [intervalIntegral.integral_symm]
      have := intervalIntegral.integral_nonneg (μ := volume) h fun t ht =>
        hnn t (lt_of_lt_of_le (by linarith) ht.1)
      linarith
    · rw [hzero u (by linarith)]
  refine ⟨fun u => ∫ t in ρ0..u, f t, ?_, hzero, ?_, ?_, ?_⟩
  · exact (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2
      ⟨fun u hu => (hd u hu).differentiableAt.differentiableWithinAt,
       hfc.congr fun u hu => (hd u hu).deriv⟩
  · intro u hu
    have hu' : -δ < u := by linarith
    have hp : 0 < u + δ := by linarith
    have hdg : deriv (fun u => ∫ t in ρ0..u, f t) u = f u := (hd u hu').deriv
    have hηdiff : HasDerivAt η (deriv η u) u := ((hηs.differentiable (by simp)) u).hasDerivAt
    have hfd : HasDerivAt f ((deriv η u * (u + δ) - η u * 1) / (u + δ) ^ 2) u := by
      rw [hf]; exact hηdiff.fun_div ((hasDerivAt_id u).add_const δ) hp.ne'
    have hdd : deriv (deriv (fun u => ∫ t in ρ0..u, f t)) u = deriv f u := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioi.mem_nhds hu'] with t ht using (hd t ht).deriv
    refine ⟨hle0 u hu, ?_, ?_⟩
    · rw [hdg, hfv]; exact div_nonneg (hηnn u) hp.le
    · rw [hdg, hdd, hfd.deriv, hfv]
      have ha : 0 < 1 / (ρ0 - 4 * ε) := by positivity
      have key : η u / (u + δ) + u * ((deriv η u * (u + δ) - η u * 1) / (u + δ) ^ 2)
          = η u * δ / (u + δ) ^ 2 + u * deriv η u / (u + δ) := by
        field_simp; ring
      rw [key]
      have h1 : 0 ≤ η u * δ / (u + δ) ^ 2 := div_nonneg (mul_nonneg (hηnn u) hδ.le) (sq_nonneg _)
      have h2 : -(1 / (ρ0 - 4 * ε)) ≤ u * deriv η u / (u + δ) := by
        rw [le_div_iff₀ hp]
        nlinarith [mul_le_mul_of_nonneg_left (hηd u) hu, mul_pos ha hδ]
      linarith
  · intro u hu0 huε
    beta_reduce
    have hp : 0 < u + δ := by linarith
    have hεδ : 0 < ε + δ := by linarith
    have hsplit : ∫ t in ρ0..u, f t = (∫ t in ρ0..ε, f t) - ∫ t in u..ε, f t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hII ρ0 ε (by linarith) (by linarith)) (hII ε u (by linarith) (by linarith)),
        intervalIntegral.integral_symm u ε]
      ring
    have hlog : ∫ t in u..ε, f t = Real.log (ε + δ) - Real.log (u + δ) := by
      rw [intervalIntegral.integral_congr (g := fun t => (t + δ)⁻¹) ?_]
      · have h := intervalIntegral.integral_comp_add_right (a := u) (b := ε) (fun t : ℝ => t⁻¹) δ
        rw [h, integral_inv_of_pos hp hεδ, Real.log_div hεδ.ne' hp.ne']
      · intro t ht
        have h : t ≤ ε := le_trans ht.2 (sup_le huε le_rfl)
        simp only [hfv, hη1 t h, one_div]
    rw [hsplit, hlog]
    have h1 := hle0 ε hε.le
    have h2 : Real.log ε ≤ Real.log (ε + δ) := Real.log_le_log hε (by linarith)
    have h3 := neg_abs_le (Real.log ε)
    have h5 : 0 ≤ 2 * ρ0 / ε := by positivity
    linarith
  · intro u hu
    beta_reduce
    have hC : 0 ≤ 2 * ρ0 / ε + |Real.log ε| := by positivity
    rcases le_total u ρ0 with h | h
    · have hu' : -δ < u := by linarith
      rw [intervalIntegral.integral_symm]
      have hb : ∫ t in u..ρ0, f t ≤ ∫ _ in u..ρ0, (2 / ε) := by
        refine intervalIntegral.integral_mono_on h (hII u ρ0 hu' (by linarith))
          intervalIntegrable_const fun t ht => ?_
        have ht1 : ε / 2 ≤ t := le_trans hu ht.1
        have hk : 2 / ε * ε = 2 := div_mul_cancel₀ 2 hε.ne'
        rw [hfv, div_le_iff₀ (by linarith)]
        nlinarith [hηle t, mul_nonneg (div_pos two_pos hε).le (show 0 ≤ t + δ - ε / 2 by linarith)]
      rw [intervalIntegral.integral_const, smul_eq_mul] at hb
      have hm : (ρ0 - u) * (2 / ε) ≤ 2 * ρ0 / ε := by
        rw [show 2 * ρ0 / ε = ρ0 * (2 / ε) by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have := abs_nonneg (Real.log ε)
      linarith
    · rw [hzero u (by linarith)]; linarith
end GlobalTheory
