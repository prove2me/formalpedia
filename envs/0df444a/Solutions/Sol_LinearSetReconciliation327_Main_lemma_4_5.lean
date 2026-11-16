-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-15T12:22:51.786977+00:00
-- url     : https://prove2.me/submissions/b1a3469a-976f-4243-978a-f26feab96327

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-! ## Auxiliary lemmas for Lemma 4.5 (entropy from the mean) -/

/-- `lg x = log x / log 2`. -/
lemma lg_eq_log_div (x : ℝ) : lg x = Real.log x / Real.log 2 := rfl

/-- For `x ≥ 0`, `x * log (1/x) = negMulLog x`. -/
lemma mul_log_inv_eq_negMulLog {x : ℝ} (hx : 0 ≤ x) : x * Real.log (1 / x) = Real.negMulLog x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h; simp
  · rw [Real.negMulLog, one_div, Real.log_inv]; ring

/-- For `x ≥ 0`, `x * lg (1/x) = negMulLog x / log 2`. -/
lemma mul_lg_inv_eq {x : ℝ} (hx : 0 ≤ x) :
    x * lg (1 / x) = Real.negMulLog x / Real.log 2 := by
  rw [lg_eq_log_div, ← mul_div_assoc, mul_log_inv_eq_negMulLog hx]

/-- Logarithm of the geometric weights: `-log ((1-q) q^k) = log (1+μ) + k log (1/q)` when
`q = μ/(1+μ)`. -/
lemma log_geom {q μ : ℝ} (hμ : 0 < μ) (hq : q = μ / (1 + μ)) (k : ℕ) :
    -(Real.log ((1 - q) * q ^ k)) = Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q) := by
  have h1μ : (0:ℝ) < 1 + μ := by linarith
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one h1μ]; linarith
  have h1q : 0 < 1 - q := by linarith
  have hsub : (1:ℝ) - q = 1 / (1 + μ) := by rw [hq]; field_simp; ring
  have hlog1q : Real.log (1 - q) = -Real.log (1 + μ) := by
    rw [hsub, one_div, Real.log_inv]
  rw [Real.log_mul (ne_of_gt h1q) (pow_ne_zero k (ne_of_gt hq0)), Real.log_pow, hlog1q,
    one_div, Real.log_inv]
  ring

/-- **Core real inequality.** For a probability vector `p` on `ℕ` with finite mean `μ`,
the Shannon entropy in nats is at most `1 + log (1 + μ)`. -/
lemma entropy_nats_bound (p : ℕ → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hsum : ∑' k : ℕ, p k = 1) (hmeanS : Summable fun k : ℕ => (k : ℝ) * p k) {μ : ℝ}
    (hμ : ∑' k : ℕ, (k : ℝ) * p k = μ) :
    Summable (fun k => Real.negMulLog (p k)) ∧
      ∑' k : ℕ, Real.negMulLog (p k) ≤ 1 + Real.log (1 + μ) := by
  have hμ0 : 0 ≤ μ := by
    rw [← hμ]
    exact tsum_nonneg fun k => mul_nonneg (Nat.cast_nonneg k) (hp0 k)
  rcases eq_or_lt_of_le hμ0 with h0 | hpos
  · -- mean zero: `p` is the Dirac mass at `0`
    have hμz : μ = 0 := h0.symm
    have hzero : ∀ k : ℕ, (k : ℝ) * p k = 0 := by
      intro k
      have hle : (k : ℝ) * p k ≤ ∑' j : ℕ, (j : ℝ) * p j := by
        have h := Summable.sum_le_tsum ({k} : Finset ℕ)
          (fun j _ => mul_nonneg (Nat.cast_nonneg j) (hp0 j)) hmeanS
        simpa using h
      rw [hμ, hμz] at hle
      exact le_antisymm hle (mul_nonneg (Nat.cast_nonneg k) (hp0 k))
    have hp_single : ∀ k : ℕ, k ≠ 0 → p k = 0 := by
      intro k hk
      have hk' : (k : ℝ) ≠ 0 := by
        simp [hk]
      exact (mul_eq_zero.mp (hzero k)).resolve_left hk'
    have hp_zero : p 0 = 1 := by
      have h := hsum
      rw [tsum_eq_single 0 hp_single] at h
      exact h
    have hpall : ∀ k : ℕ, Real.negMulLog (p k) = 0 := by
      intro k
      rcases eq_or_ne k 0 with hk | hk
      · subst hk; simp [hp_zero]
      · rw [hp_single k hk]; simp
    refine ⟨?_, ?_⟩
    · simpa [hpall] using (summable_zero : Summable (fun _ : ℕ => (0:ℝ)))
    · simp [hpall, hμz]
  · -- positive mean: compare with the geometric law of parameter `q = μ/(1+μ)`
    set q : ℝ := μ / (1 + μ) with hq
    have h1μ : (0:ℝ) < 1 + μ := by linarith
    have hq0 : 0 < q := by rw [hq]; positivity
    have hq1 : q < 1 := by rw [hq, div_lt_one h1μ]; linarith
    have h1q : 0 < 1 - q := by linarith
    set Q : ℕ → ℝ := fun k => (1 - q) * q ^ k with hQ
    have hQpos : ∀ k, 0 < Q k := fun k => by
      rw [hQ]; exact mul_pos h1q (pow_pos hq0 k)
    have hQsum : Summable Q := by
      rw [hQ]
      exact (summable_geometric_of_lt_one hq0.le hq1).mul_left _
    have hQtsum : ∑' k : ℕ, Q k = 1 := by
      rw [hQ, tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
      field_simp
    have hQmean : ∑' k : ℕ, (k : ℝ) * Q k = μ := by
      have hterm : ∀ k : ℕ, (k : ℝ) * Q k = (1 - q) * ((k : ℝ) * q ^ k) := by
        intro k; rw [hQ]; ring
      rw [show (∑' k : ℕ, (k : ℝ) * Q k)
          = ∑' k : ℕ, (1 - q) * ((k : ℝ) * q ^ k) from tsum_congr hterm]
      rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one]
      · rw [hq]; field_simp; try ring
      · rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
    -- pointwise comparison with the geometric law
    have hpoint : ∀ k : ℕ, Real.negMulLog (p k) ≤
        p k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)) - p k + Q k := by
      intro k
      have hQk := hQpos k
      have hpk := hp0 k
      have h1 : Q k * Real.negMulLog (p k / Q k) ≤ Q k - p k := by
        have h2 : Real.negMulLog (p k / Q k) ≤ 1 - p k / Q k :=
          Real.negMulLog_le_one_sub_self (div_nonneg hpk hQk.le)
        calc Q k * Real.negMulLog (p k / Q k) ≤ Q k * (1 - p k / Q k) :=
              mul_le_mul_of_nonneg_left h2 hQk.le
          _ = Q k - p k := by field_simp; try ring
      have h3 : Real.negMulLog (p k) =
          Q k * Real.negMulLog (p k / Q k) + (p k / Q k) * Real.negMulLog (Q k) := by
        have hm := Real.negMulLog_mul (p k / Q k) (Q k)
        rw [div_mul_cancel₀ (p k) (ne_of_gt hQk)] at hm
        rw [hm]; try ring
      have h4 : (p k / Q k) * Real.negMulLog (Q k) =
          p k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)) := by
        have hlogQ : Real.log (Q k) = -(Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)) := by
          have h := log_geom hpos hq.symm k
          rw [← hq] at h
          rw [hQ]
          linarith
        have hQk0 : Q k ≠ 0 := ne_of_gt hQk
        calc (p k / Q k) * Real.negMulLog (Q k)
            = (p k / Q k) * (Q k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q))) := by
                rw [Real.negMulLog, hlogQ]; ring
          _ = p k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)) := by
                field_simp
      rw [h3, h4]
      linarith
    -- summability of the comparison series
    have hpS : Summable p := by
      by_contra hc
      rw [tsum_eq_zero_of_not_summable hc] at hsum
      norm_num at hsum
    have hA : Summable fun k : ℕ => p k * Real.log (1 + μ) := hpS.mul_right _
    have hB : Summable fun k : ℕ => (k : ℝ) * p k * Real.log (1 / q) := hmeanS.mul_right _
    have hC : Summable fun k : ℕ =>
        p k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)) := by
      have heq : (fun k : ℕ => p k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)))
          = fun k : ℕ => p k * Real.log (1 + μ) + (k : ℝ) * p k * Real.log (1 / q) := by
        funext k; ring
      rw [heq]
      exact hA.add hB
    have hcS : Summable fun k : ℕ =>
        p k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)) - p k + Q k :=
      (hC.sub hpS).add hQsum
    have hc_nonneg : ∀ k : ℕ, 0 ≤
        p k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)) - p k + Q k := by
      intro k
      have h1 := hpoint k
      have h2 : 0 ≤ Real.negMulLog (p k) := Real.negMulLog_nonneg (hp0 k) (hp1 k)
      linarith
    have hsumm : Summable fun k => Real.negMulLog (p k) :=
      Summable.of_nonneg_of_le (fun k => Real.negMulLog_nonneg (hp0 k) (hp1 k))
        (fun k => hpoint k) hcS
    refine ⟨hsumm, ?_⟩
    have hle : ∑' k : ℕ, Real.negMulLog (p k) ≤
        ∑' k : ℕ, (p k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)) - p k + Q k) :=
      hsumm.tsum_le_tsum (fun k => hpoint k) hcS
    have hAtsum : ∑' b : ℕ, p b * Real.log (1 + μ) = Real.log (1 + μ) := by
      rw [tsum_mul_right, hsum, one_mul]
    have hBtsum : ∑' b : ℕ, (b : ℝ) * p b * Real.log (1 / q) = μ * Real.log (1 / q) := by
      rw [tsum_mul_right, hμ]
    have htsum_c : ∑' k : ℕ,
        (p k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)) - p k + Q k)
        = Real.log (1 + μ) + μ * Real.log (1 / q) - 1 + 1 := by
      have hsplit : (fun k : ℕ =>
            p k * (Real.log (1 + μ) + (k : ℝ) * Real.log (1 / q)) - p k + Q k)
          = fun k : ℕ => ((p k * Real.log (1 + μ) + (k : ℝ) * p k * Real.log (1 / q)) - p k
              + Q k) := by
        funext k; ring
      rw [hsplit]
      rw [Summable.tsum_add ((hA.add hB).sub hpS) hQsum]
      rw [Summable.tsum_sub (hA.add hB) hpS, Summable.tsum_add hA hB]
      rw [hAtsum, hBtsum, hsum, hQtsum]
      try ring
    rw [htsum_c] at hle
    have hstep : μ * Real.log (1 / q) ≤ 1 := by
      have h1q' : 1 / q = (1 + μ) / μ := by rw [hq]; field_simp
      have hpos' : (0:ℝ) < (1 + μ) / μ := by positivity
      have hlog_le : Real.log ((1 + μ) / μ) ≤ 1 / μ := by
        have h := Real.log_le_sub_one_of_pos hpos'
        have hsub : (1 + μ) / μ - 1 = 1 / μ := by field_simp; ring
        linarith
      calc μ * Real.log (1 / q) = μ * Real.log ((1 + μ) / μ) := by rw [h1q']
        _ ≤ μ * (1 / μ) := mul_le_mul_of_nonneg_left hlog_le hpos.le
        _ = 1 := by field_simp
    linarith

/-- **Lemma 4.5 (entropy from the mean).** -/
theorem lemma_4_5 (T : PMF ℕ) (hmean : ∑' k : ℕ, (k : ℝ≥0∞) * T k ≠ ⊤) :
    entropy (fun k => (T k).toReal) ≤
      ENNReal.ofReal (lg (Real.exp 1 * (1 + (∑' k : ℕ, (k : ℝ≥0∞) * T k).toReal))) := by
  classical
  set p : ℕ → ℝ := fun k => (T k).toReal with hp
  set mu : ℝ := (∑' k : ℕ, (k : ℝ≥0∞) * T k).toReal with hmu
  have hp0 : ∀ k, 0 ≤ p k := fun k => ENNReal.toReal_nonneg
  have hp1 : ∀ k, p k ≤ 1 := fun k => by
    have h := ENNReal.toReal_mono (b := 1) ENNReal.one_ne_top (T.coe_le_one k)
    simpa [p] using h
  have hsum : ∑' k : ℕ, p k = 1 := by
    have h := ENNReal.tsum_toReal_eq (f := fun k => T k) (fun k => T.apply_ne_top k)
    simp only [p]
    rw [← h, T.tsum_coe, ENNReal.toReal_one]
  have hmeanS : Summable fun k : ℕ => (k : ℝ) * p k := by
    have h := ENNReal.summable_toReal (f := fun k : ℕ => (k : ℝ≥0∞) * T k) hmean
    refine h.congr fun k => ?_
    simp [p, ENNReal.toReal_mul]
  have hmueq : ∑' k : ℕ, (k : ℝ) * p k = mu := by
    have h := ENNReal.tsum_toReal_eq (f := fun k : ℕ => (k : ℝ≥0∞) * T k)
      (fun k => ENNReal.mul_ne_top (by simp) (T.apply_ne_top k))
    rw [hmu, h]
    exact tsum_congr fun k => by simp [p, ENNReal.toReal_mul]
  obtain ⟨hsumm, hbound⟩ := entropy_nats_bound p hp0 hp1 hsum hmeanS hmueq
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmu0 : 0 ≤ mu := by
    rw [← hmueq]
    exact tsum_nonneg fun k => mul_nonneg (Nat.cast_nonneg k) (hp0 k)
  have hnonneg : ∀ k, 0 ≤ p k * lg (1 / p k) := fun k => by
    rw [mul_lg_inv_eq (hp0 k)]
    exact div_nonneg (Real.negMulLog_nonneg (hp0 k) (hp1 k)) hlog2.le
  have hsumm_lg : Summable fun k => p k * lg (1 / p k) :=
    (hsumm.div_const (Real.log 2)).congr fun k => (mul_lg_inv_eq (hp0 k)).symm
  have htsum_lg : ∑' k : ℕ, p k * lg (1 / p k)
      = (∑' k : ℕ, Real.negMulLog (p k)) / Real.log 2 := by
    have hterm : ∀ k : ℕ, p k * lg (1 / p k) = Real.negMulLog (p k) * (Real.log 2)⁻¹ :=
      fun k => by rw [mul_lg_inv_eq (hp0 k), div_eq_mul_inv]
    rw [show (∑' k : ℕ, p k * lg (1 / p k))
        = ∑' k : ℕ, Real.negMulLog (p k) * (Real.log 2)⁻¹ from tsum_congr hterm]
    rw [tsum_mul_right, div_eq_mul_inv]
  rw [entropy]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsumm_lg]
  rw [htsum_lg]
  apply ENNReal.ofReal_le_ofReal
  rw [lg_eq_log_div]
  have hloge : Real.log (Real.exp 1 * (1 + mu)) = 1 + Real.log (1 + mu) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (by linarith : (1:ℝ) + mu ≠ 0), Real.log_exp]
  rw [hloge]
  exact (div_le_div_iff_of_pos_right hlog2).mpr hbound

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Lemma 4.5 (Entropy from the mean) — submission wrapper matching the target statement. -/
theorem solution (T : PMF ℕ) (hmean : ∑' k : ℕ, (k : ℝ≥0∞) * T k ≠ ⊤) :
    entropy (fun k => (T k).toReal) ≤
      ENNReal.ofReal (lg (Real.exp 1 * (1 + (∑' k : ℕ, (k : ℝ≥0∞) * T k).toReal))) :=
  LinearSetReconciliation327.Main.lemma_4_5 T hmean
