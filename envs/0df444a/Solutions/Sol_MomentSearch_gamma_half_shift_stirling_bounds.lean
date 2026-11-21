-- Prove2me | solution 1 for MomentSearch.gamma_half_shift_stirling_bounds
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:34:16.357176+00:00
-- url     : https://prove2.me/submissions/59b3a2f8-99ce-4a69-97dc-d9f8441d977c

import Mathlib

open Real Filter Set
open scoped Topology

private noncomputable def F (x : ℝ) := x * log x - x
private noncomputable def defect (x : ℝ) := F (x+1) - F x - log (x+1/2)

private theorem derivF {x : ℝ} (hx : 0 < x) : HasDerivAt F (log x) x := by
  unfold F
  convert! (Real.hasDerivAt_mul_log hx.ne').sub (hasDerivAt_id x) using 1
  ring

private theorem defectMono : MonotoneOn defect (Ici 0) := by
  have cf : Continuous F := Real.continuous_mul_log.sub continuous_id
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · apply ContinuousOn.sub ((cf.comp (continuous_id.add continuous_const)).continuousOn.sub cf.continuousOn)
    exact (continuous_id.add continuous_const).continuousOn.log (fun x hx => by
      change x + 1/2 ≠ 0
      have := mem_Ici.mp hx
      positivity)
  · intro x hx
    rw [interior_Ici] at hx
    have hx' : 0 < x := hx
    exact (((derivF (show 0 < x+1 by positivity)).comp x ((hasDerivAt_id x).add_const 1)).sub
      (derivF hx')).differentiableAt.differentiableWithinAt |>.sub
      (((hasDerivAt_id x).add_const (1/2)).log (by change x+1/2 ≠ 0; positivity)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx' : 0 < x := hx
    have hd := (((derivF (show 0 < x+1 by positivity)).comp x ((hasDerivAt_id x).add_const 1)).sub
      (derivF hx')).sub (((hasDerivAt_id x).add_const (1/2)).log (by change x+1/2 ≠ 0; positivity))
    rw [show deriv defect x = _ from hd.deriv]
    let z := 1 / (2*x+1)
    have hz : 0 ≤ z := by dsimp [z]; positivity
    have hz' : z < 1 := by dsimp [z]; apply (div_lt_iff₀ (by positivity)).mpr; linarith
    have h := Real.sum_range_le_log_div hz hz' 1
    simp only [Finset.sum_range_one, Nat.mul_zero, zero_add, pow_one] at h
    have hr : (1+z)/(1-z) = (x+1)/x := by dsimp [z]; field_simp; ring
    rw [hr, Real.log_div (by positivity) hx'.ne'] at h
    have he : 1 / (x+1/2) = 2*z := by dsimp [z]; field_simp
    simp only [mul_one, id_eq] at *
    linarith

private theorem logShift (c : ℝ) :
    Tendsto (fun x : ℝ => log (1+c/x)) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop (tendsto_id (α := ℝ)) :
    Tendsto (fun x : ℝ => c/x) atTop (𝓝 0)) : Tendsto (fun x : ℝ => 1+c/x) atTop (𝓝 (1+0)))
  simpa using h.log (by norm_num)

private theorem remainderLimit (c : ℝ) :
    Tendsto (fun x : ℝ => F (x+c) - F x - c*log x) atTop (𝓝 0) := by
  have h := ((Real.tendsto_mul_log_one_add_div_atTop c).add ((logShift c).const_mul c)).sub_const c
  simp only [mul_zero, add_zero, sub_self] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (max 0 (-c))] with x hx
  have hx' : 0 < x := (le_max_left ..).trans_lt hx
  have hxc : 0 < x+c := by linarith [(le_max_right 0 (-c)).trans_lt hx]
  rw [show 1+c/x = (x+c)/x by field_simp, Real.log_div hxc.ne' hx'.ne']
  dsimp [F]
  ring

private theorem defectNonpos {x : ℝ} (hx : 0 ≤ x) : defect x ≤ 0 := by
  have h := (remainderLimit 1).sub (logShift (1/2))
  have hd : Tendsto defect atTop (𝓝 0) := by
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [show 1+(1/2)/y = (y+1/2)/y by field_simp, Real.log_div (by positivity) hy.ne']
    dsimp [defect]
    ring
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hd
  filter_upwards [eventually_ge_atTop x] with y hy
  exact defectMono hx (hx.trans hy) hy

private theorem sumDefect (t : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, defect (t+k) =
      F (t+n) - F t - ∑ k ∈ Finset.range n, log (t+1/2+k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Nat.cast_succ]
    simp only [defect, add_assoc, add_comm (1/2 : ℝ) (n : ℝ)]
    ring

private theorem sumLimit (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n+1), defect (t+k)) atTop
      (𝓝 (log (Gamma (t+1/2)) - log (sqrt Real.pi) - (1/2)*log 2 - F t)) := by
  have hG := Real.BohrMollerup.tendsto_log_gamma (show 0 < t+1/2 by positivity)
  have hS := Stirling.tendsto_stirlingSeq_sqrt_pi.log (show Real.sqrt Real.pi ≠ 0 by positivity)
  have hR := (remainderLimit (t+1)).comp tendsto_natCast_atTop_atTop
  have h := ((((hG.sub hS).sub_const ((1/2)*log 2)).sub_const (F t)).add hR)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change Real.BohrMollerup.logGammaSeq _ _ - log (Stirling.stirlingSeq n) - _ - _ +
    (F ((n : ℝ)+(t+1)) - F n - (t+1)*log n) = _
  rw [sumDefect, Stirling.log_stirlingSeq_formula, Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hn.ne'),
    Real.log_div (Nat.cast_ne_zero.mpr hn.ne') (Real.exp_pos _).ne', Real.log_exp]
  unfold Real.BohrMollerup.logGammaSeq
  rw [Nat.cast_add_one, show t + ((n : ℝ)+1) = (n : ℝ)+(t+1) by ring]
  unfold F
  ring

theorem solution (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt Real.pi * Real.exp (t * Real.log t - t) ≤ Real.Gamma (t + 1 / 2) ∧
    Real.Gamma (t + 1 / 2) ≤ Real.sqrt (2 * Real.pi) * Real.exp (t * Real.log t - t) := by
  have hlow := le_of_tendsto_of_tendsto' (sumLimit 0 le_rfl) (sumLimit t ht) (fun n =>
    Finset.sum_le_sum (fun k _ => defectMono (show 0 ≤ (0 : ℝ)+k by positivity)
      (show 0 ≤ t+k by positivity) (by linarith)))
  have hup := le_of_tendsto_of_tendsto' (sumLimit t ht) tendsto_const_nhds (fun n =>
    Finset.sum_nonpos (fun k _ => defectNonpos (show 0 ≤ t+k by positivity)))
  simp only [zero_add, Real.Gamma_one_half_eq, F, zero_mul, sub_zero] at hlow
  have hc : log (sqrt (2*Real.pi)) = log (sqrt Real.pi) + (1/2)*log 2 := by
    rw [Real.log_sqrt (by positivity), Real.log_sqrt Real.pi_pos.le,
      Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  have hg := Gamma_pos_of_pos (show 0 < t+1/2 by positivity)
  constructor
  · apply (Real.log_le_log_iff (by positivity) hg).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    linarith
  · apply (Real.log_le_log_iff hg (by positivity)).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, hc]
    dsimp [F] at hup
    linarith
