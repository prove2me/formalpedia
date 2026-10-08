-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.analytic_aggregate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:42:25.997031+00:00
-- url     : https://prove2.me/submissions/6804deab-1601-4556-9b2d-020a20800796
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_uniform_exp_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_tendsto_actualRowCount_normalized
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

private theorem log_div_of_normalized_pow {f : ℝ → ℝ} {n : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ n) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H : ℝ => Real.log (f H) / H) atTop (𝓝 0) := by
  have hlog : Tendsto (fun H : ℝ => Real.log (f H / H ^ n)) atTop (𝓝 (Real.log L)) :=
    (Real.continuousAt_log hL.ne').tendsto.comp hf
  have hslow : Tendsto (fun H : ℝ => Real.log H / H) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h := (hlog.div_atTop tendsto_id).add (hslow.const_mul (n : ℝ))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hf.eventually (eventually_ne_nhds hL.ne')] with H hH hn
  have hfne : f H ≠ 0 := by
    intro hz
    apply hn
    simp [hz]
  rw [Real.log_div hfne (pow_ne_zero _ hH.ne'), Real.log_pow]
  simp only [id_eq]
  ring

private theorem envelope_normalized (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => translationEnvelope m v H / H ^ (2 * m + 1))
      atTop (𝓝 (1 / v)) := by
  have hsmall : Tendsto (fun H : ℝ => 1 / H) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop 1
  have h1 : Tendsto (fun H : ℝ => (H + 1) / H) atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds (x := (1 : ℝ))).add hsmall
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with H hH
    field_simp
  have h2 : Tendsto (fun H : ℝ => (H / v + 1) / H) atTop (𝓝 (1 / v)) := by
    have ht := (tendsto_const_nhds (x := (1 / v : ℝ))).add hsmall
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with H hH
    field_simp
  have h := (h1.pow (2 * m)).mul h2
  simp only [one_pow, one_mul] at h
  convert h using 1
  funext H
  simp only [translationEnvelope, div_pow, div_mul_div_comm, pow_succ]

private theorem remainder_tendsto {nu : ℝ} (d : FixedData nu) :
    Tendsto (analyticRemainder d) atTop (𝓝 0) := by
  have hw : ∀ i : Fin d.m, 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    change 0 < (Nat.ceil (Real.log (d.q i.val)) : ℝ)
    rw [← d.x_log i.val]
    exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)
  have hlead : 0 < (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m + 1).factorial : ℝ) * (d.v0 : ℝ) *
        ∏ i, MatrixArithmetic.logWeights (finiteDenominators d) i) := by
    apply div_pos
    · exact mul_pos (by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one d.K_pos)
        (pow_pos d.base.theta_pos _)
    · exact mul_pos (mul_pos (by positivity) d.v0_pos)
        (Finset.prod_pos fun i _ => hw i)
  have hr := log_div_of_normalized_pow (tendsto_actualRowCount_normalized d) hlead
  have hc := tendsto_id.const_div_atTop
    (Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2)))
  have hq := log_div_of_normalized_pow (envelope_normalized d.m d.v0_pos)
    (div_pos zero_lt_one d.v0_pos)
  convert (hr.add hc).add hq using 1
  · funext H
    unfold analyticRemainder
    simp only [id_eq]
    ring
  · norm_num

private theorem rowCount_pos {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    0 < actualRowCount d H := by
  classical
  let r : Row d H := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one d.K_pos⟩,
    ⟨fun _ => 0, by simp [strictWeightedSimplex, realWeightedSimplex, hH, hH.le]⟩⟩
  have : Nonempty (Row d H) := ⟨r⟩
  exact Fintype.card_pos

theorem solution : AnalyticAggregateStatement := by
  intro nu hnu d
  refine ⟨analyticRemainder d, remainder_tendsto d, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  intro selection hdet
  have hb := actual_minor_uniform_exp_bound d (le_trans (by norm_num) hnu.le) hH selection
  have hlog := Real.log_le_log (norm_pos_iff.mpr hdet) hb
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ (mul_pos (by exact_mod_cast rowCount_pos d hH) hH)).mpr
  simpa only [mul_comm] using hlog
