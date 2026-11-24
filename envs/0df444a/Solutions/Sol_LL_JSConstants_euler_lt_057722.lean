-- Prove2me | solution 1 for LL_JSConstants.euler_lt_057722
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T23:32:27.133441+00:00
-- url     : https://prove2.me/submissions/c54ebcd6-6284-461f-acb3-5663cc84e0f1

import Mathlib

namespace LL_JSConstants_EulerWork

private noncomputable def cSeq (k : ℕ) : ℝ :=
  (harmonic (k + 8) : ℝ) - Real.log ((k + 8 : ℕ) : ℝ) -
    1 / (2 * ((k + 8 : ℕ) : ℝ)) + 1 / (12 * ((k + 8 : ℕ) : ℝ) ^ 2)

private lemma cSeq_succ_le (k : ℕ) : cSeq (k + 1) ≤ cSeq k := by
  unfold cSeq
  set m : ℕ := k + 8
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h2m1_pos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hcast : ((k + 1 + 8 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    have : k + 1 + 8 = m + 1 := by omega
    rw [this, Nat.cast_add, Nat.cast_one]
  have hharm : (harmonic (k + 1 + 8) : ℝ) = (harmonic m : ℝ) + 1 / ((m : ℝ) + 1) := by
    have : k + 1 + 8 = m + 1 := by omega
    rw [this, harmonic_succ]
    push_cast
    ring
  rw [hharm, hcast]
  set x : ℝ := 1 / (2 * (m : ℝ) + 1)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    rw [div_lt_one h2m1_pos]
    linarith
  have hlog_step := Real.sum_range_le_log_div hx0 hx1 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at hlog_step
  norm_num at hlog_step
  have hx_ratio : (1 + x) / (1 - x) = ((m : ℝ) + 1) / (m : ℝ) := by
    have hsub : 1 - x ≠ 0 := by linarith
    dsimp [x]
    field_simp
    ring
  rw [hx_ratio, Real.log_div hm1_pos.ne' hm_pos.ne'] at hlog_step
  have halg :
      (1 / ((m : ℝ) + 1) - 1 / (2 * ((m : ℝ) + 1)) + 1 / (12 * ((m : ℝ) + 1) ^ 2) +
          1 / (2 * (m : ℝ)) - 1 / (12 * (m : ℝ) ^ 2)) ≤
        2 * (x + x ^ 3 / 3) := by
    rw [← sub_nonneg]
    have hid :
        2 * (x + x ^ 3 / 3) -
            (1 / ((m : ℝ) + 1) - 1 / (2 * ((m : ℝ) + 1)) + 1 / (12 * ((m : ℝ) + 1) ^ 2) +
              1 / (2 * (m : ℝ)) - 1 / (12 * (m : ℝ) ^ 2)) =
          (2 * (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1) /
            (12 * (m : ℝ) ^ 2 * ((m : ℝ) + 1) ^ 2 * (2 * (m : ℝ) + 1) ^ 3) := by
      dsimp [x]
      field_simp
      ring
    rw [hid]
    positivity
  linarith

private lemma antitone_cSeq : Antitone cSeq :=
  antitone_nat_of_succ_le cSeq_succ_le

private lemma tendsto_cSeq :
    Filter.Tendsto cSeq Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  have h1 : Filter.Tendsto (fun k : ℕ => (harmonic (k + 8) : ℝ) - Real.log ((k + 8 : ℕ) : ℝ))
      Filter.atTop (nhds Real.eulerMascheroniConstant) :=
    Real.tendsto_harmonic_sub_log.comp (Filter.tendsto_add_atTop_nat 8)
  have h_nat : Filter.Tendsto (fun k : ℕ => ((k + 8 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
     tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 8)
  have h2 : Filter.Tendsto (fun k : ℕ => 1 / (2 * ((k + 8 : ℕ) : ℝ))) Filter.atTop (nhds 0) := by
    have h2' : Filter.Tendsto (fun x : ℝ => (2 * x)⁻¹) Filter.atTop (nhds 0) :=
      Filter.Tendsto.inv_tendsto_atTop
        (Filter.Tendsto.const_mul_atTop (show (0 : ℝ) < 2 by norm_num) Filter.tendsto_id)
    have h2'' : Filter.Tendsto (fun x : ℝ => 1 / (2 * x)) Filter.atTop (nhds 0) := by
      simpa only [one_div] using h2'
    exact h2''.comp h_nat
  have h3 : Filter.Tendsto (fun k : ℕ => 1 / (12 * ((k + 8 : ℕ) : ℝ) ^ 2)) Filter.atTop (nhds 0) := by
    have h3' : Filter.Tendsto (fun x : ℝ => (12 * x ^ 2)⁻¹) Filter.atTop (nhds 0) :=
      Filter.Tendsto.inv_tendsto_atTop
        (Filter.Tendsto.const_mul_atTop (show (0 : ℝ) < 12 by norm_num)
          (Filter.tendsto_pow_atTop (by norm_num)))
    have h3'' : Filter.Tendsto (fun x : ℝ => 1 / (12 * x ^ 2)) Filter.atTop (nhds 0) := by
      simpa only [one_div] using h3'
    exact h3''.comp h_nat
  have h123 : Filter.Tendsto cSeq Filter.atTop
      (nhds ((Real.eulerMascheroniConstant - 0) + 0)) :=
    (h1.sub h2).add h3
  simpa only [sub_zero, add_zero] using h123

private lemma cSeq_zero_lt : cSeq 0 < (0.57722 : ℝ) := by
  unfold cSeq
  have h8 : (harmonic 8 : ℝ) = 761 / 280 := by
    norm_num [harmonic_succ, harmonic_zero]
  have hlog8 : Real.log ((0 + 8 : ℕ) : ℝ) = 3 * Real.log 2 := by
    have : ((0 + 8 : ℕ) : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [this, Real.log_pow]
    norm_num
  rw [show (0 + 8 : ℕ) = 8 from rfl] at hlog8 ⊢
  rw [h8, hlog8]
  have hlog2 := Real.log_two_gt_d9
  linarith

end LL_JSConstants_EulerWork

theorem solution : Real.eulerMascheroniConstant < (0.57722 : ℝ) :=
  lt_of_le_of_lt
    (LL_JSConstants_EulerWork.antitone_cSeq.le_of_tendsto LL_JSConstants_EulerWork.tendsto_cSeq 0)
    LL_JSConstants_EulerWork.cSeq_zero_lt
