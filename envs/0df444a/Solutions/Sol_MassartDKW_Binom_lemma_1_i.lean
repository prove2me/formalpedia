-- Prove2me | solution 1 for MassartDKW.Binom.lemma_1_i
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:10:41.260468+00:00
-- url     : https://prove2.me/submissions/62ee38a0-bec1-4d47-b482-aa622becd34e

import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting



namespace MassartDKW.Binom

/-- derivative of `phi` -/
noncomputable def phiD (t : ℝ) : ℝ := t ^ 3 / ((3 + 2 * t) ^ 2 * (1 + t))

lemma phi_hasDerivAt {t : ℝ} (ht : 0 ≤ t) : HasDerivAt phi (phiD t) t := by
  have h1 : (0:ℝ) < 1 + t := by linarith
  have h2 : (2 * (1 + 2 * t / 3) : ℝ) ≠ 0 := by positivity
  have ha : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hb : HasDerivAt (fun t : ℝ => 2 * (1 + 2 * t / 3)) (2 * (2 / 3)) t := by
    have := ((((hasDerivAt_id t).const_mul (2:ℝ)).div_const 3).const_add 1).const_mul (2:ℝ)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hc : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + t)) t := by
    have := ((hasDerivAt_id t).const_add 1).log (ne_of_gt h1)
    simp only [id] at this
    exact this.congr_deriv (by ring)
  have hd := ((hasDerivAt_id t).sub (ha.div hb h2)).sub hc
  refine hd.congr_deriv ?_
  unfold phiD
  have h3 : (3 + 2 * t : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma phiD_pos {t : ℝ} (ht : 0 < t) : 0 < phiD t := by
  unfold phiD; positivity

lemma phi_continuousOn : ContinuousOn phi (Set.Ici 0) := by
  intro t ht
  exact (phi_hasDerivAt ht).continuousAt.continuousWithinAt

lemma phi_deriv {t : ℝ} (ht : 0 ≤ t) : deriv phi t = phiD t := (phi_hasDerivAt ht).deriv

lemma phi_zero : phi 0 = 0 := by simp [phi]

lemma phi_strictMonoOn : StrictMonoOn phi (Set.Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) phi_continuousOn ?_
  intro x hx
  rw [interior_Ici] at hx
  rw [phi_deriv (le_of_lt hx)]
  exact phiD_pos hx

lemma phi_pos {t : ℝ} (ht : 0 < t) : 0 < phi t := by
  have := phi_strictMonoOn ((Set.mem_Ici.2 le_rfl)) (le_of_lt ht : (0:ℝ) ≤ t) ht
  rwa [phi_zero] at this

lemma phiD_monotoneOn : MonotoneOn phiD (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  unfold phiD
  have hda : 0 < (3 + 2 * a) ^ 2 * (1 + a) := by positivity
  have hdb : 0 < (3 + 2 * b) ^ 2 * (1 + b) := by positivity
  rw [div_le_div_iff₀ hda hdb]
  have key : b ^ 3 * ((3 + 2 * a) ^ 2 * (1 + a)) - a ^ 3 * ((3 + 2 * b) ^ 2 * (1 + b))
      = (b - a) * (9 * (b ^ 2 + a * b + a ^ 2) + 21 * a * b * (a + b) + 16 * a ^ 2 * b ^ 2) := by
    ring
  have : 0 ≤ (b - a) * (9 * (b ^ 2 + a * b + a ^ 2) + 21 * a * b * (a + b) + 16 * a ^ 2 * b ^ 2) := by
    apply mul_nonneg (by linarith)
    positivity
  linarith

lemma phi_convexOn : ConvexOn ℝ (Set.Ici 0) phi := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ici 0) phi_continuousOn ?_ ?_
  · intro x hx
    rw [interior_Ici] at hx
    exact (phi_hasDerivAt (le_of_lt hx)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    rw [phi_deriv (le_of_lt ha), phi_deriv (le_of_lt hb)]
    exact phiD_monotoneOn ha hb hab

lemma log_div_tendsto : Filter.Tendsto (fun t : ℝ => Real.log (1 + t) / t) Filter.atTop (nhds 0) := by
  have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  have h2 : Filter.Tendsto (fun t : ℝ => t + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 Filter.tendsto_id
  have := h1.comp h2
  refine this.congr' ?_
  filter_upwards with t
  simp only [Function.comp]
  rw [add_comm]
  ring_nf

lemma rat_tendsto : Filter.Tendsto (fun t : ℝ => t / (2 * (1 + 2 * t / 3))) Filter.atTop
    (nhds (3 / 4)) := by
  have h1 : Filter.Tendsto (fun t : ℝ => 2 / t) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have h2 : Filter.Tendsto (fun t : ℝ => 2 / t + 4 / 3) Filter.atTop (nhds (0 + 4 / 3)) :=
    h1.add tendsto_const_nhds
  have h3 : Filter.Tendsto (fun t : ℝ => 1 / (2 / t + 4 / 3)) Filter.atTop (nhds (1 / (0 + 4 / 3))) :=
    tendsto_const_nhds.div h2 (by norm_num)
  have h4 : (1 : ℝ) / (0 + 4 / 3) = 3 / 4 := by norm_num
  rw [h4] at h3
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
  field_simp
  ring

lemma phi_div_tendsto :
    Filter.Tendsto (fun t => phi t / t) Filter.atTop (nhds (1 / 4)) := by
  have h := (tendsto_const_nhds (x := (1:ℝ)).sub rat_tendsto).sub log_div_tendsto
  have e : (1:ℝ) - 3 / 4 - 0 = 1 / 4 := by norm_num
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with t ht
  unfold phi
  field_simp

theorem lemma_1_i_core :
    (∀ t : ℝ, 0 < t → 0 < phi t) ∧
    StrictMonoOn phi (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) phi ∧
    Filter.Tendsto (fun t => phi t / t) Filter.atTop (nhds (1 / 4)) :=
  ⟨fun _ ht => phi_pos ht, phi_strictMonoOn, phi_convexOn, phi_div_tendsto⟩

end MassartDKW.Binom

open MassartDKW.Binom


theorem solution :
    (∀ t : ℝ, 0 < t → 0 < phi t) ∧
    StrictMonoOn phi (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) phi ∧
    Filter.Tendsto (fun t => phi t / t) Filter.atTop (nhds (1 / 4)) := by
  exact lemma_1_i_core
