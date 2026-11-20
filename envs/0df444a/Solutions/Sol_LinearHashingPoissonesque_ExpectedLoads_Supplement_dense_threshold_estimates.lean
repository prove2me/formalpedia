-- Prove2me | solution 1 for LinearHashingPoissonesque.ExpectedLoads.Supplement.dense_threshold_estimates
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:26:37.727201+00:00
-- url     : https://prove2.me/submissions/63055dc4-1449-4743-9cd9-cba8f8a09a03

import Mathlib
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonThresholds

open Set LinearHashingPoissonesque.ExpectedLoads

lemma log_one_add_ge (x : ℝ) (hx : 0 ≤ x) : 2 * x / (2 + x) ≤ Real.log (1 + x) := by
  let g : ℝ → ℝ := fun y => Real.log (1 + y) - 2 * y / (2 + y)
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro y hy
      have hy : (0:ℝ) ≤ y := hy
      apply ContinuousAt.continuousWithinAt
      have h1 : (1 + y) ≠ 0 := by linarith
      have h2 : (2 + y) ≠ 0 := by linarith
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ici] at hy
      have hy : (0:ℝ) < y := hy
      apply DifferentiableAt.differentiableWithinAt
      have h1 : (1 + y) ≠ 0 := by linarith
      have h2 : (2 + y) ≠ 0 := by linarith
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ici] at hy
      have hy : (0:ℝ) < y := hy
      have hd : HasDerivAt g (1 / (1 + y) - (2 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2) y := by
        have a1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + y)) y := by
          have := ((hasDerivAt_id y).const_add 1).log (by simp; linarith)
          simpa [one_div] using this
        have a2 : HasDerivAt (fun y : ℝ => 2 * y / (2 + y))
            ((2 * 1 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2) y := by
          have := ((hasDerivAt_id' y).const_mul 2).div ((hasDerivAt_id' y).const_add 2)
            (by linarith)
          exact this
        exact (a1.sub a2).congr_deriv (by ring)
      rw [hd.deriv]
      have : (1:ℝ) / (1 + y) - (2 * (2 + y) - 2 * y * 1) / (2 + y) ^ 2 =
          y ^ 2 / ((1 + y) * (2 + y) ^ 2) := by
        field_simp; ring
      rw [this]; positivity
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simp only [g, add_zero, Real.log_one, mul_zero, zero_div, sub_zero] at this
  linarith

/-- (1-δ) log(1-δ) ≥ -δ + δ²/2 for δ ∈ [0,1) -/
lemma one_sub_log_ge (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) :
    -δ + δ ^ 2 / 2 ≤ (1 - δ) * Real.log (1 - δ) := by
  let h : ℝ → ℝ := fun y => (1 - y) * Real.log (1 - y) + y - y ^ 2 / 2
  have hmono : MonotoneOn h (Ico 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
    · intro y hy
      apply ContinuousAt.continuousWithinAt
      have : (1 - y) ≠ 0 := by linarith [hy.2]
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ico] at hy
      apply DifferentiableAt.differentiableWithinAt
      have : (1 - y) ≠ 0 := by linarith [hy.2]
      fun_prop (disch := assumption)
    · intro y hy
      rw [interior_Ico] at hy
      have hne : (1 - y) ≠ 0 := by linarith [hy.2]
      have hd : HasDerivAt h (-Real.log (1 - y) - y) y := by
        have a1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
          simpa using (hasDerivAt_id y).const_sub 1
        have a2 := (a1.mul (a1.log hne))
        have a3 := (a2.add (hasDerivAt_id y)).sub ((hasDerivAt_pow 2 y).div_const 2)
        exact a3.congr_deriv (by field_simp; ring)
      rw [hd.deriv]
      have := Real.log_le_sub_one_of_pos (by linarith [hy.2] : (0:ℝ) < 1 - y)
      linarith
  have := hmono (mem_Ico.mpr ⟨le_rfl, by norm_num⟩) (mem_Ico.mpr ⟨h0, h1⟩) h0
  simp only [h, sub_zero, Real.log_one, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div] at this
  linarith



theorem solution (m : ℝ) (n r : ℕ) (hm : 0 < m)
    (hr : 1 ≤ r) (hrn : r ≤ n) (hdense : Real.log ((n : ℝ) / r) ≤ m / n) :
    upperThreshold m n r ≤ m / n + 2 * Real.sqrt (m / n * Real.log ((n : ℝ) / r)) ∧
    m / n - Real.sqrt (2 * (m / n) * Real.log ((n : ℝ) / r)) ≤
      lowerThreshold m n r := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) (hr.trans hrn))
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set μ := m / (n : ℝ) with hμ
  set L := Real.log ((n : ℝ) / r) with hL
  have hμ0 : 0 < μ := div_pos hm hn
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_div hr0).mpr (by exact_mod_cast hrn))
  set D : ℝ → ℝ := fun t => poissonDivergence t μ with hD
  have hDμ : D μ = 0 := by simp [hD, poissonDivergence, div_self hμ0.ne']
  have hD0 : D 0 = μ := by simp [hD, poissonDivergence]
  have hDcont : ContinuousOn D (Icc 0 (2 * μ + 2 * Real.sqrt (μ * L) + 1)) := by
    have hc : Continuous (fun t : ℝ => t * Real.log t - t * Real.log μ - t + μ) := by
      have := Real.continuous_mul_log; fun_prop
    refine hc.continuousOn.congr (fun t ht => ?_)
    simp only [hD, poissonDivergence]
    rcases ht.1.eq_or_lt with h0 | hpos
    · subst h0; simp
    · rw [Real.log_div hpos.ne' hμ0.ne']; ring
  refine ⟨?_, ?_⟩
  · -- upper threshold
    set δ := 2 * Real.sqrt (μ * L) with hδ
    have hδ0 : 0 ≤ δ := by positivity
    have hsq : Real.sqrt (μ * L) ^ 2 = μ * L := Real.sq_sqrt (by positivity)
    have hδμ : δ ≤ 2 * μ := by
      have : Real.sqrt (μ * L) ≤ μ := by
        rw [Real.sqrt_le_left hμ0.le]; nlinarith
      linarith
    have hDδ : L ≤ D (μ + δ) := by
      set u := δ / μ with hu
      have hu0 : 0 ≤ u := div_nonneg hδ0 hμ0.le
      have hlog := log_one_add_ge u hu0
      have e1 : (μ + δ) / μ = 1 + u := by rw [hu]; field_simp
      have hval : D (μ + δ) = (μ + δ) * Real.log (1 + u) - δ := by
        simp only [hD, poissonDivergence]; rw [e1]; ring
      rw [hval]
      have hμu : μ * u = δ := by rw [hu]; field_simp
      have h2u : 0 < 2 + u := by linarith
      have hu2 : u ≤ 2 := by rw [hu, div_le_iff₀ hμ0]; linarith
      have key : (μ + δ) * (2 * u / (2 + u)) - δ = μ * u ^ 2 / (2 + u) := by
        rw [← hμu]; field_simp; ring
      have hμu2 : μ * u ^ 2 = 4 * L := by
        have e : (μ * u) ^ 2 = δ ^ 2 := by rw [hμu]
        have h2 : δ ^ 2 = 4 * (μ * L) := by rw [hδ, mul_pow, hsq]; norm_num
        have h3 : (μ * u ^ 2) * μ = (4 * L) * μ := by linear_combination e + h2
        exact mul_right_cancel₀ hμ0.ne' h3
      calc L ≤ 4 * L / (2 + u) := by rw [le_div_iff₀ h2u]; nlinarith
        _ = μ * u ^ 2 / (2 + u) := by rw [hμu2]
        _ = (μ + δ) * (2 * u / (2 + u)) - δ := key.symm
        _ ≤ (μ + δ) * Real.log (1 + u) - δ := by gcongr
    have hsub : Icc μ (μ + δ) ⊆ Icc 0 (2 * μ + 2 * Real.sqrt (μ * L) + 1) := by
      intro t ht; exact ⟨hμ0.le.trans ht.1, by linarith [ht.2]⟩
    obtain ⟨t, ht, hDt⟩ := intermediate_value_Icc (by linarith : μ ≤ μ + δ) (hDcont.mono hsub)
      (show L ∈ Icc (D μ) (D (μ + δ)) from ⟨by rw [hDμ]; exact hL0, hDδ⟩)
    have hmem : t ∈ {t : ℝ | μ ≤ t ∧ poissonDivergence t μ = L} := ⟨ht.1, hDt⟩
    unfold upperThreshold
    calc sInf {t : ℝ | m / (n : ℝ) ≤ t ∧ poissonDivergence t (m / (n : ℝ)) = Real.log ((n : ℝ) / (r : ℝ))}
        ≤ t := csInf_le ⟨μ, fun x hx => hx.1⟩ hmem
      _ ≤ μ + δ := ht.2
  · -- lower threshold
    unfold lowerThreshold
    split_ifs with hμL
    · have : μ ≤ Real.sqrt (2 * μ * L) := by
        rw [Real.le_sqrt hμ0.le (by positivity)]; nlinarith
      linarith
    · push Not at hμL
      have hsub : Icc 0 μ ⊆ Icc 0 (2 * μ + 2 * Real.sqrt (μ * L) + 1) := by
        intro t ht; exact ⟨ht.1, by have := Real.sqrt_nonneg (μ * L); linarith [ht.2]⟩
      obtain ⟨t0, ht0, hDt0⟩ := intermediate_value_Icc' hμ0.le (hDcont.mono hsub)
        (show L ∈ Icc (D μ) (D 0) from ⟨by rw [hDμ]; exact hL0, by rw [hD0]; exact hμL.le⟩)
      have ht0pos : 0 < t0 := by
        rcases ht0.1.eq_or_lt with h | h
        · subst h; rw [hD0] at hDt0; linarith
        · exact h
      refine le_csInf ⟨t0, ht0pos, ht0.2, hDt0⟩ (fun t ht => ?_)
      obtain ⟨htpos, htμ, hDt⟩ := ht
      set w := 1 - t / μ with hw
      have hw0 : 0 ≤ w := by rw [hw, sub_nonneg, div_le_one hμ0]; exact htμ
      have hw1 : w < 1 := by rw [hw]; have := div_pos htpos hμ0; linarith
      have hlow := one_sub_log_ge w hw0 hw1
      have ht_eq : t = μ * (1 - w) := by rw [hw]; field_simp; ring
      have hDw : poissonDivergence t μ = μ * ((1 - w) * Real.log (1 - w) + w) := by
        unfold poissonDivergence
        rw [show t / μ = 1 - w by rw [hw]; ring, ht_eq]; ring
      rw [hDw] at hDt
      have hLw : μ * w ^ 2 / 2 ≤ L := by
        have h' : μ * ((1 - w) * Real.log (1 - w) + w) = L := hDt
        nlinarith [h', mul_le_mul_of_nonneg_left hlow hμ0.le]
      have hμt : μ - t = μ * w := by rw [ht_eq]; ring
      have : μ - t ≤ Real.sqrt (2 * μ * L) := by
        rw [Real.le_sqrt (by rw [hμt]; positivity) (by positivity)]
        rw [hμt]
        have : μ * w ^ 2 ≤ 2 * L := by linarith
        nlinarith [mul_le_mul_of_nonneg_left this hμ0.le]
      linarith
