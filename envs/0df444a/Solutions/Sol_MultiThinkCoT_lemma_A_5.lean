-- Prove2me | solution 1 for MultiThinkCoT.lemma_A_5
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T05:06:04.762892+00:00
-- url     : https://prove2.me/submissions/1b3ae985-9abb-4548-bcd6-f239065769ad

import Mathlib

set_option maxHeartbeats 4000000

theorem solution : ∀ k : ℝ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧
      ∀ a b x : ℝ, Real.exp 1 ≤ a → 0 ≤ b → 0 < x →
        c * (a * Real.log a ^ k + b) ≤ x → a * Real.log x ^ k + b ≤ x := by
  intro k hk
  refine ⟨Real.exp ((2 * k + 2) ^ 3), Real.exp_pos _, ?_⟩
  intro a b x ha hb hx hmain
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hL1 : 1 ≤ Real.log a := (Real.le_log_iff_exp_le ha0).mpr ha
  have hLp : 0 < Real.log a := by linarith
  have hk0 : (0:ℝ) ≤ k := by linarith
  have hcpos : 0 < Real.exp ((2 * k + 2) ^ 3) := Real.exp_pos _
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hc2 : (2:ℝ) ≤ Real.exp ((2 * k + 2) ^ 3) := by
    have h := Real.add_one_le_exp ((2 * k + 2) ^ 3)
    have hcube : (1:ℝ) ≤ (2 * k + 2) ^ 3 := by
      have h1 : (1:ℝ) ≤ 2 * k + 2 := by linarith
      calc (1:ℝ) = 1 ^ 3 := by norm_num
        _ ≤ (2 * k + 2) ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
    linarith
  have hc1 : (1:ℝ) ≤ Real.exp ((2 * k + 2) ^ 3) := Real.one_le_exp (by positivity)
  have hcpow : (2:ℝ) ^ k + 1 ≤ Real.exp ((2 * k + 2) ^ 3) := by
    have h2k1 : (2:ℝ) ^ (k + 1) ≤ Real.exp ((2 * k + 2) ^ 3) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      apply Real.exp_le_exp.mpr
      have h1 : (k + 1) * Real.log 2 ≤ (k + 1) * 1 :=
        mul_le_mul_of_nonneg_left hlog2 (by linarith)
      have h2 : k + 1 ≤ (2 * k + 2) ^ 3 := by nlinarith [sq_nonneg (2 * k + 2), sq_nonneg k, hk]
      linarith
    have h3 : (2:ℝ) ^ k + 1 ≤ (2:ℝ) ^ (k + 1) := by
      have h4 : (2:ℝ) ^ (k + 1) = (2:ℝ) ^ k * (2:ℝ) ^ (1:ℝ) := Real.rpow_add (by norm_num) k 1
      rw [h4, Real.rpow_one]
      have h5 : (1:ℝ) ≤ (2:ℝ) ^ k := Real.one_le_rpow (by norm_num) hk0
      nlinarith
    linarith
  -- base numeric inequality at `(2k+2)^3 + 1`
  have hMpos : (0:ℝ) < (2 * k + 2) ^ 3 + 1 := by positivity
  have hbase : 2 * k * Real.log ((2 * k + 2) ^ 3 + 1) + 2 * Real.log 2 ≤ (2 * k + 2) ^ 3 + 1 := by
    have ht : (2 * k + 2) ^ 3 + 1 ≤ (2 * k + 2) ^ 4 := by
      nlinarith [sq_nonneg (2 * k + 2), sq_nonneg k, hk]
    have hlogM : Real.log ((2 * k + 2) ^ 3 + 1) ≤ 4 * Real.log (2 * k + 2) := by
      have h1 := Real.log_le_log hMpos ht
      rwa [Real.log_pow] at h1
    have hlogt : Real.log (2 * k + 2) ≤ 2 * k + 1 := by
      have h := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 2 * k + 2)
      linarith
    have h2k0 : (0:ℝ) ≤ 2 * k := by linarith
    have h1 : 2 * k * Real.log ((2 * k + 2) ^ 3 + 1) ≤ 2 * k * (4 * Real.log (2 * k + 2)) :=
      mul_le_mul_of_nonneg_left hlogM h2k0
    have h2 : 2 * k * (4 * Real.log (2 * k + 2)) ≤ 2 * k * (4 * (2 * k + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) h2k0
    nlinarith [h1, h2, hlog2, hk, sq_nonneg k]
  -- monotonicity of `μ - 2k log μ` from the base point
  have hmono : ∀ μ : ℝ, (2 * k + 2) ^ 3 + 1 ≤ μ → 2 * k * Real.log μ + 2 * Real.log 2 ≤ μ := by
    intro μ hμ
    have hμpos : 0 < μ := by linarith [hMpos]
    have hstep : Real.log μ ≤ Real.log ((2 * k + 2) ^ 3 + 1) + (μ - ((2 * k + 2) ^ 3 + 1)) / ((2 * k + 2) ^ 3 + 1) := by
      have h1 : Real.log (μ / ((2 * k + 2) ^ 3 + 1)) = Real.log μ - Real.log ((2 * k + 2) ^ 3 + 1) :=
        Real.log_div hμpos.ne' hMpos.ne'
      have h2 : Real.log (μ / ((2 * k + 2) ^ 3 + 1)) ≤ μ / ((2 * k + 2) ^ 3 + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h3 : μ / ((2 * k + 2) ^ 3 + 1) - 1 = (μ - ((2 * k + 2) ^ 3 + 1)) / ((2 * k + 2) ^ 3 + 1) := by
        field_simp
      rw [h1, h3] at h2
      linarith
    have hstep2 : 2 * k * ((μ - ((2 * k + 2) ^ 3 + 1)) / ((2 * k + 2) ^ 3 + 1)) ≤ μ - ((2 * k + 2) ^ 3 + 1) := by
      rw [← mul_div_assoc, div_le_iff₀ hMpos]
      have h2kM : 2 * k ≤ (2 * k + 2) ^ 3 + 1 := by nlinarith [sq_nonneg (2 * k + 2), hk, sq_nonneg k]
      have hnonneg : 0 ≤ μ - ((2 * k + 2) ^ 3 + 1) := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h2kM hnonneg]
    nlinarith [hstep, hstep2, hbase]
  -- lower bound on `log x`
  have hxge : Real.exp ((2 * k + 2) ^ 3) * Real.exp 1 ≤ x := by
    have hLk : (1:ℝ) ≤ Real.log a ^ k := Real.one_le_rpow hL1 hk0
    have h1 : Real.exp 1 ≤ a * Real.log a ^ k := by
      have h2 : Real.exp 1 * 1 ≤ a * Real.log a ^ k :=
        mul_le_mul ha hLk (by norm_num : (0:ℝ) ≤ 1) (le_trans (Real.exp_pos 1).le ha)
      linarith
    have h2 : Real.exp 1 ≤ a * Real.log a ^ k + b := by linarith
    have h3 : Real.exp ((2 * k + 2) ^ 3) * Real.exp 1 ≤ Real.exp ((2 * k + 2) ^ 3) * (a * Real.log a ^ k + b) :=
      mul_le_mul_of_nonneg_left h2 hcpos.le
    linarith
  have hx1 : (1:ℝ) ≤ x := by nlinarith [hxge, hc1, Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)]
  have hmulog : (2 * k + 2) ^ 3 + 1 ≤ Real.log x := by
    have h1 : Real.log (Real.exp ((2 * k + 2) ^ 3) * Real.exp 1) ≤ Real.log x :=
      Real.log_le_log (by positivity) hxge
    rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at h1
    linarith
  have hmu0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  -- bounds from the hypothesis
  have hLk0 : 0 ≤ a * Real.log a ^ k := by
    have : 0 ≤ Real.log a ^ k := Real.rpow_nonneg hLp.le k
    positivity
  have hca : Real.exp ((2 * k + 2) ^ 3) * (a * Real.log a ^ k) ≤ x := by
    nlinarith [hmain, hb, hcpos]
  have hcb : Real.exp ((2 * k + 2) ^ 3) * b ≤ x := by
    nlinarith [hmain, hLk0, hcpos]
  rcases le_or_gt x (a ^ 2) with hcase | hcase
  · -- ## Case A: x ≤ a²
    have hmule : Real.log x ≤ 2 * Real.log a := by
      have h1 : Real.log x ≤ Real.log (a ^ 2) := Real.log_le_log hx hcase
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith
    have hk1 : Real.log x ^ k ≤ (2 * Real.log a) ^ k := Real.rpow_le_rpow hmu0 hmule hk0
    have hsplit : (2 * Real.log a) ^ k = (2:ℝ) ^ k * Real.log a ^ k :=
      Real.mul_rpow (by norm_num) hLp.le
    rw [hsplit] at hk1
    have h2k0 : (0:ℝ) ≤ (2:ℝ) ^ k := Real.rpow_nonneg (by norm_num) k
    have hkey : Real.exp ((2 * k + 2) ^ 3) * (a * Real.log x ^ k + b) ≤ ((2:ℝ) ^ k + 1) * x := by
      have h1 : a * Real.log x ^ k ≤ (2:ℝ) ^ k * (a * Real.log a ^ k) := by
        nlinarith [hk1, ha0.le]
      nlinarith [h1, hca, hcb]
    have hfinal : ((2:ℝ) ^ k + 1) * x ≤ Real.exp ((2 * k + 2) ^ 3) * x := by
      nlinarith [hcpow, hx.le]
    have hcx := le_trans hkey hfinal
    by_contra hcon
    push_neg at hcon
    nlinarith [hcx, hcon, hcpos]
  · -- ## Case B: a² < x
    have hax : a ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq ha0.le]
      exact Real.sqrt_le_sqrt hcase.le
    have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have hsqrteq : Real.sqrt x = Real.exp (Real.log x / 2) := by
      rw [Real.exp_half, Real.exp_log hx]
    have hbound : Real.log x ^ k ≤ Real.sqrt x / 2 := by
      have hlog : 2 * k * Real.log (Real.log x) + 2 * Real.log 2 ≤ Real.log x := hmono _ hmulog
      have hμpos : 0 < Real.log x := by linarith [hmulog, hMpos]
      have h1 : Real.log x ^ k = Real.exp (k * Real.log (Real.log x)) := by
        rw [Real.rpow_def_of_pos hμpos k]
        congr 1
        ring
      rw [h1, hsqrteq]
      have h2 : Real.exp (Real.log x / 2) / 2 = Real.exp (Real.log x / 2 - Real.log 2) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      rw [h2]
      apply Real.exp_le_exp.mpr
      nlinarith [hlog]
    have hkey : Real.exp ((2 * k + 2) ^ 3) * (a * Real.log x ^ k + b) ≤ Real.exp ((2 * k + 2) ^ 3) * x := by
      have h1 : a * Real.log x ^ k ≤ Real.sqrt x * (Real.sqrt x / 2) := by
        have h2 : a * Real.log x ^ k ≤ Real.sqrt x * Real.log x ^ k :=
          mul_le_mul_of_nonneg_right hax (Real.rpow_nonneg hmu0 k)
        nlinarith [h2, hbound, hsqrtpos]
      have h3 : Real.sqrt x * (Real.sqrt x / 2) = x / 2 := by
        have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
        nlinarith [hsq]
      rw [h3] at h1
      nlinarith [h1, hca, hcb, hc2, hx.le, hcpos]
    by_contra hcon
    push_neg at hcon
    nlinarith [hkey, hcon, hcpos]
