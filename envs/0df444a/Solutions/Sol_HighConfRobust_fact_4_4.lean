-- Prove2me | solution 1 for HighConfRobust.fact_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:56:27.236027+00:00
-- url     : https://prove2.me/submissions/3029c7ba-ac93-4538-bb44-b17115cad3b6

import Mathlib
import Definitions.Def_HighConfRobust_renyiDivergence

open MeasureTheory HighConfRobust

/-- Absolute continuity of finitely supported discrete measures. -/
private lemma ac_discrete {M : ℕ} (p w : Fin M → ENNReal) (hpw : ∀ i, p i ≠ 0 → w i ≠ 0) :
    (∑ i, p i • Measure.dirac i) ≪ (∑ i, w i • Measure.dirac i) := by
  intro s hs
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at hs ⊢
  rw [Finset.sum_eq_zero_iff] at hs ⊢
  intro i hi
  rcases mul_eq_zero.mp (hs i hi) with h | h
  · by_cases hp : p i = 0
    · simp [hp]
    · exact absurd h (hpw i hp)
  · simp [h]

private lemma lintegral_discrete {M : ℕ} (w : Fin M → ENNReal) (f : Fin M → ENNReal) :
    ∫⁻ x, f x ∂(∑ i, w i • Measure.dirac i) = ∑ i, w i * f i := by
  rw [lintegral_finsetSum_measure]
  congr 1; ext i
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

private lemma discrete_singleton {M : ℕ} (w : Fin M → ENNReal) (j : Fin M) :
    (∑ i, w i • Measure.dirac i) {j} = w j := by
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Measure.dirac_apply' _ (measurableSet_singleton j),
      Set.indicator_of_notMem (Set.mem_singleton_iff.not.mpr hb), mul_zero]
  · simp

private lemma rnDeriv_discrete {M : ℕ} (p w : Fin M → ENNReal) (hpw : ∀ i, p i ≠ 0 → w i ≠ 0)
    [IsFiniteMeasure (∑ i, p i • Measure.dirac i)] [IsFiniteMeasure (∑ i, w i • Measure.dirac i)]
    (j : Fin M) :
    w j * (∑ i, p i • Measure.dirac i).rnDeriv (∑ i, w i • Measure.dirac i) j = p j := by
  have h := Measure.setLIntegral_rnDeriv (ac_discrete p w hpw) {j}
  rw [lintegral_singleton, discrete_singleton, discrete_singleton] at h
  rw [mul_comm]; exact h

theorem solution (ε a : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (ha : 0 < a) (ha1 : a < 1) :
    let lam : ℝ := min 1 (a / ε)
    let κ : ℝ := 1 / max 1 (Real.log (ε / a))
    let w : Fin 3 → ENNReal :=
      ![ENNReal.ofReal (1 - ε), ENNReal.ofReal (ε * (1 - lam)), ENNReal.ofReal (lam * ε)]
    let w' : Fin 3 → ENNReal := ![ENNReal.ofReal (1 - ε), 0, ENNReal.ofReal ε]
    renyiDivergence (1 + κ) (∑ i, w' i • Measure.dirac i) (∑ i, w i • Measure.dirac i) ≤
      ((2 * ε / κ : ℝ) : EReal) := by
  intro lam κ w w'
  have hm1 : 1 ≤ max 1 (Real.log (ε / a)) := le_max_left _ _
  have hκ0 : 0 < κ := by positivity
  have hκinv : 1 / κ = max 1 (Real.log (ε / a)) := by simp [κ]
  have hlam0 : 0 < lam := lt_min one_pos (div_pos ha hε)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hq1 : (1 + κ) ≠ 1 := by linarith
  -- absolute continuity
  have hpw : ∀ i, w' i ≠ 0 → w i ≠ 0 := by
    intro i hi
    fin_cases i
    · simpa [w, w'] using hi
    · simp [w'] at hi
    · simp only [w, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
  set μ := ∑ i, w' i • Measure.dirac i with hμ
  set ν := ∑ i, w i • Measure.dirac i with hν
  have : IsFiniteMeasure μ := by
    constructor; simp only [hμ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    simp [w', Fin.sum_univ_three]
  have : IsFiniteMeasure ν := by
    constructor; simp only [hν, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    simp [w, Fin.sum_univ_three]
  have hac : μ ≪ ν := ac_discrete w' w hpw
  have hrn := rnDeriv_discrete w' w hpw
  -- the key real bound on (1/λ)^κ
  have hloglam : Real.log (1 / lam) ≤ 1 / κ := by
    rw [hκinv]
    by_cases h : 1 ≤ a / ε
    · have : lam = 1 := min_eq_left h
      rw [this]; simp only [div_one, Real.log_one]; linarith
    · push Not at h
      have : lam = a / ε := min_eq_right h.le
      rw [this, one_div_div]
      exact le_max_right _ _
  have hpow : (1 / lam) ^ κ ≤ 3 := by
    rw [Real.rpow_def_of_pos (by positivity)]
    have : Real.log (1 / lam) * κ ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hloglam hκ0.le
      rwa [one_div_mul_cancel hκ0.ne'] at this
    calc Real.exp (Real.log (1 / lam) * κ) ≤ Real.exp 1 := Real.exp_le_exp.mpr this
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  -- bound the integral
  have hI : ∫⁻ x, (μ.rnDeriv ν x) ^ (1 + κ) ∂ν ≤ ENNReal.ofReal (1 + 2 * ε) := by
    rw [hν, lintegral_discrete, Fin.sum_univ_three]
    have t0 : w 0 * (μ.rnDeriv ν 0) ^ (1 + κ) ≤ ENNReal.ofReal (1 - ε) := by
      by_cases h0 : w 0 = 0
      · rw [h0, zero_mul]; exact zero_le
      · have hw0 : w 0 ≠ ⊤ := by simp [w]
        have hr : μ.rnDeriv ν 0 = 1 := by
          have := hrn 0
          have e : w' 0 = w 0 := rfl
          rw [e] at this
          exact (ENNReal.mul_right_inj h0 hw0).mp (this.trans (mul_one _).symm)
        rw [hr, ENNReal.one_rpow, mul_one]
        exact le_rfl
    have t1 : w 1 * (μ.rnDeriv ν 1) ^ (1 + κ) = 0 := by
      by_cases h1 : w 1 = 0
      · rw [h1, zero_mul]
      · have hr : μ.rnDeriv ν 1 = 0 := by
          have := hrn 1
          have e : w' 1 = 0 := rfl
          rw [e, mul_eq_zero] at this
          exact this.resolve_left h1
        rw [hr, ENNReal.zero_rpow_of_pos (by linarith), mul_zero]
    have t2 : w 2 * (μ.rnDeriv ν 2) ^ (1 + κ) ≤ ENNReal.ofReal (3 * ε) := by
      have h2 : w 2 ≠ 0 := hpw 2 (by simp [w']; exact hε)
      have hw2 : w 2 = ENNReal.ofReal (lam * ε) := rfl
      have hr : μ.rnDeriv ν 2 = ENNReal.ofReal (1 / lam) := by
        have := hrn 2
        have e : w' 2 = ENNReal.ofReal ε := rfl
        rw [e, hw2] at this
        rw [hw2] at h2
        have hne : ENNReal.ofReal (lam * ε) ≠ ⊤ := ENNReal.ofReal_ne_top
        rw [← ENNReal.eq_div_iff h2 hne] at this
        rw [this, ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1; field_simp
      rw [hr, hw2, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_add (by positivity), Real.rpow_one]
      have : lam * ε * (1 / lam * (1 / lam) ^ κ) = ε * (1 / lam) ^ κ := by
        field_simp
      rw [this]
      nlinarith
    calc w 0 * (μ.rnDeriv ν 0) ^ (1 + κ) + w 1 * (μ.rnDeriv ν 1) ^ (1 + κ) +
          w 2 * (μ.rnDeriv ν 2) ^ (1 + κ)
        ≤ ENNReal.ofReal (1 - ε) + 0 + ENNReal.ofReal (3 * ε) := by
          rw [t1]; gcongr
      _ = ENNReal.ofReal (1 + 2 * ε) := by
          rw [add_zero, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1; ring
  -- conclude
  unfold renyiDivergence
  rw [if_neg hq1]
  unfold PADMPriv.renyiDiv
  rw [if_pos hac]
  have hlog : ENNReal.log (∫⁻ x, (μ.rnDeriv ν x) ^ (1 + κ) ∂ν) ≤ ((2 * ε : ℝ) : EReal) := by
    calc ENNReal.log (∫⁻ x, (μ.rnDeriv ν x) ^ (1 + κ) ∂ν)
        ≤ ENNReal.log (ENNReal.ofReal (1 + 2 * ε)) := ENNReal.log_monotone hI
      _ = ((Real.log (1 + 2 * ε) : ℝ) : EReal) := ENNReal.log_ofReal_of_pos (by linarith)
      _ ≤ ((2 * ε : ℝ) : EReal) := by
          apply EReal.coe_le_coe_iff.mpr
          have := Real.add_one_le_exp (2 * ε)
          calc Real.log (1 + 2 * ε) ≤ Real.log (Real.exp (2 * ε)) :=
                Real.log_le_log (by linarith) (by linarith)
            _ = 2 * ε := Real.log_exp _
  have hk : ((1 + κ - 1)⁻¹ : ℝ) = κ⁻¹ := by ring_nf
  rw [hk]
  calc ((κ⁻¹ : ℝ) : EReal) * ENNReal.log (∫⁻ x, (μ.rnDeriv ν x) ^ (1 + κ) ∂ν)
      ≤ ((κ⁻¹ : ℝ) : EReal) * ((2 * ε : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left hlog (by exact_mod_cast (inv_pos.mpr hκ0).le)
    _ = ((2 * ε / κ : ℝ) : EReal) := by
        rw [← EReal.coe_mul]; congr 1; field_simp
