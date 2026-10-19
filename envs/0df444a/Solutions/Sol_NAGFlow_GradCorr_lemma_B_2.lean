-- Prove2me | solution 1 for NAGFlow.GradCorr.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:40:09.125927+00:00
-- url     : https://prove2.me/submissions/2c0466c4-c537-4e9f-9d1e-f4609bf3fad4

import Mathlib
set_option autoImplicit false

theorem solution (μ : ℝ) (α γ Ls : ℕ → ℝ) (hγ0 : 0 < γ 0) (hμ : 0 ≤ μ)
    (hLpos : ∀ k, 0 < Ls k) (hLmu : ∀ k, μ ≤ Ls k)
    (hγ : ∀ k, γ (k + 1) = γ k + α k * (μ - γ (k + 1)))
    (hα : ∀ k, Ls k * α k ^ 2 = γ k * (1 + α k)) (hαpos : ∀ k, 0 < α k) :
    (∀ k, 0 < γ k) ∧
      (∀ L : ℝ, (∀ i, Ls i ≤ L) → ∀ k, Real.sqrt (min (γ 0) μ / L) ≤ α k) ∧
      (∀ k : ℕ, 1 ≤ k →
        ∏ i ∈ Finset.range k, 1 / (1 + α i) ≤
          4 * (2 + ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) ^ (-2 : ℤ)) ∧
      (∀ L : ℝ, (∀ i, Ls i ≤ L) → ∀ k : ℕ, 1 ≤ k →
        ∏ i ∈ Finset.range k, 1 / (1 + α i) ≤
          (1 + Real.sqrt (min (γ 0) μ / L)) ^ (-(k : ℤ))) ∧
      (μ = 0 → ∀ k : ℕ, 1 ≤ k →
        (1 + ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) ^ (-2 : ℤ) ≤
          ∏ i ∈ Finset.range k, 1 / (1 + α i)) := by
  -- one-step identity
  have hstep : ∀ k, γ (k + 1) * (1 + α k) = γ k + α k * μ := fun k => by
    linear_combination hγ k
  have hpos : ∀ k, 0 < γ k := by
    intro k
    induction k with
    | zero => exact hγ0
    | succ k ih =>
      have h1 := hstep k
      have h2 := hαpos k
      have h3 : 0 < γ (k + 1) * (1 + α k) := by rw [h1]; positivity
      exact (pos_iff_pos_of_mul_pos h3).mpr (by linarith)
  have hlow : ∀ k, min (γ 0) μ ≤ γ k := by
    intro k
    induction k with
    | zero => exact min_le_left _ _
    | succ k ih =>
      have h1 := hstep k
      have h2 := hαpos k
      have hm : min (γ 0) μ ≤ μ := min_le_right _ _
      by_contra hneg
      push_neg at hneg
      nlinarith
  have hsq : ∀ L : ℝ, (∀ i, Ls i ≤ L) → ∀ k, Real.sqrt (min (γ 0) μ / L) ≤ α k := by
    intro L hL k
    have hLp : 0 < L := lt_of_lt_of_le (hLpos 0) (hL 0)
    apply Real.sqrt_le_iff.mpr
    refine ⟨(hαpos k).le, ?_⟩
    rw [div_le_iff₀ hLp]
    have h1 := hα k
    have h2 := hlow k
    have h3 := hpos k
    have h4 := hαpos k
    have h5 : Ls k * α k ^ 2 ≤ L * α k ^ 2 :=
      mul_le_mul_of_nonneg_right (hL k) (by positivity)
    nlinarith [mul_pos h3 h4]
  -- products
  set R : ℕ → ℝ := fun k => ∏ i ∈ Finset.range k, Real.sqrt (1 + α i) with hRdef
  have hRsucc : ∀ k, R (k + 1) = R k * Real.sqrt (1 + α k) := fun k => by
    simp only [hRdef, Finset.prod_range_succ]
  have hR0 : R 0 = 1 := by simp [hRdef]
  have hs1 : ∀ k, 0 < 1 + α k := fun k => by have := hαpos k; linarith
  have hsqs : ∀ k, Real.sqrt (1 + α k) ^ 2 = 1 + α k := fun k => Real.sq_sqrt (hs1 k).le
  have hs_ge : ∀ k, 1 ≤ Real.sqrt (1 + α k) := fun k => by
    rw [Real.one_le_sqrt]; have := hαpos k; linarith
  have hRpos : ∀ k, 0 < R k := by
    intro k
    induction k with
    | zero => rw [hR0]; norm_num
    | succ k ih => rw [hRsucc]; exact mul_pos ih (by have := hs_ge k; linarith)
  have hPR : ∀ k, ∏ i ∈ Finset.range k, 1 / (1 + α i) = (R k ^ 2)⁻¹ := by
    intro k
    induction k with
    | zero => simp [hR0]
    | succ k ih =>
      rw [Finset.prod_range_succ, ih, hRsucc, mul_pow, hsqs]
      have := hs1 k
      have := hRpos k
      field_simp
  have hgR : ∀ k, γ 0 / R k ^ 2 ≤ γ k := by
    intro k
    induction k with
    | zero => rw [hR0]; simp
    | succ k ih =>
      have h1 := hstep k
      have h2 := hαpos k
      have hr := hRpos k
      have hs := hsqs k
      rw [hRsucc, mul_pow, hs]
      have hμ' : 0 ≤ α k * μ := by positivity
      rw [show γ 0 / (R k ^ 2 * (1 + α k)) = (γ 0 / R k ^ 2) / (1 + α k) by
        field_simp]
      rw [div_le_iff₀ (hs1 k)]
      nlinarith
  have hkey : ∀ k, (Real.sqrt (γ 0 / Ls k)) ^ 2 = γ 0 / Ls k := fun k =>
    Real.sq_sqrt (div_nonneg hγ0.le (hLpos k).le)
  -- the core relation  R_k^2 (s^2-1)^2 >= c^2 s^2
  have hcore : ∀ k, Real.sqrt (γ 0 / Ls k) * Real.sqrt (1 + α k) ≤
      R k * α k := by
    intro k
    have hr := hRpos k
    have hL := hLpos k
    have hc0 : 0 ≤ Real.sqrt (γ 0 / Ls k) := Real.sqrt_nonneg _
    have hs0 : 0 ≤ Real.sqrt (1 + α k) := Real.sqrt_nonneg _
    have h1 := hα k
    have h2 := hgR k
    have h3 : γ 0 / Ls k * (1 + α k) ≤ (R k * α k) ^ 2 := by
      have : γ 0 / R k ^ 2 * (1 + α k) ≤ γ k * (1 + α k) :=
        mul_le_mul_of_nonneg_right h2 (hs1 k).le
      rw [← h1] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ hL]
      nlinarith
    have h4 : (Real.sqrt (γ 0 / Ls k) * Real.sqrt (1 + α k)) ^ 2 ≤ (R k * α k) ^ 2 := by
      rw [mul_pow, hkey, hsqs]; exact h3
    exact le_of_sq_le_sq h4 (by have := hαpos k; positivity)
  -- lower bound on R
  have hlowR : ∀ k, 1 + (∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) / 2 ≤ R k := by
    intro k
    induction k with
    | zero => simp [hR0]
    | succ k ih =>
      rw [Finset.sum_range_succ, hRsucc]
      have h1 := hcore k
      have hs := hsqs k
      have hs1' := hs_ge k
      have hr := hRpos k
      have hc0 : 0 ≤ Real.sqrt (γ 0 / Ls k) := Real.sqrt_nonneg _
      set s := Real.sqrt (1 + α k)
      set c := Real.sqrt (γ 0 / Ls k)
      have hα' : α k = (s - 1) * (s + 1) := by nlinarith
      rw [hα'] at h1
      -- c s ≤ R (s-1)(s+1) ≤ R (s-1) 2 s
      have h2 : c * s ≤ (R k * (s - 1)) * (2 * s) := by
        have : R k * (s - 1) * (s + 1) ≤ R k * (s - 1) * (2 * s) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hr.le (by linarith))
        nlinarith
      have h3 : c ≤ R k * (s - 1) * 2 := by
        have : 0 < s := by linarith
        nlinarith
      nlinarith
  have hupR : (μ = 0) → ∀ k, R k ≤ 1 + ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i) := by
    intro hμ0 k
    have hgeq : ∀ k, γ k ≤ γ 0 / R k ^ 2 := by
      intro k
      induction k with
      | zero => rw [hR0]; simp
      | succ k ih =>
        have h1 := hstep k
        have hr := hRpos k
        have hs := hsqs k
        rw [hRsucc, mul_pow, hs, hμ0, mul_zero, add_zero] at *
        rw [show γ 0 / (R k ^ 2 * (1 + α k)) = (γ 0 / R k ^ 2) / (1 + α k) by
          field_simp]
        rw [le_div_iff₀ (hs1 k)]
        nlinarith
    induction k with
    | zero => simp [hR0]
    | succ k ih =>
      rw [Finset.sum_range_succ, hRsucc]
      have hr := hRpos k
      have hL := hLpos k
      have hs := hsqs k
      have hs1' := hs_ge k
      have hc0 : 0 ≤ Real.sqrt (γ 0 / Ls k) := Real.sqrt_nonneg _
      have h1 := hα k
      have h2 := hgeq k
      have h3 : (R k * α k) ^ 2 ≤ γ 0 / Ls k * (1 + α k) := by
        have : γ k * (1 + α k) ≤ γ 0 / R k ^ 2 * (1 + α k) :=
          mul_le_mul_of_nonneg_right h2 (hs1 k).le
        rw [← h1] at this
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
        rw [div_mul_eq_mul_div, le_div_iff₀ hL]
        nlinarith
      have h4 : R k * α k ≤ Real.sqrt (γ 0 / Ls k) * Real.sqrt (1 + α k) := by
        refine le_of_sq_le_sq ?_ (by positivity)
        calc (R k * α k) ^ 2 ≤ γ 0 / Ls k * (1 + α k) := h3
          _ = _ := by rw [mul_pow (Real.sqrt _), hkey, hsqs]
      set s := Real.sqrt (1 + α k)
      set c := Real.sqrt (γ 0 / Ls k)
      have hα' : α k = (s - 1) * (s + 1) := by nlinarith
      rw [hα'] at h4
      have h5 : R k * (s - 1) ≤ c := by
        have : 0 < s + 1 := by linarith
        nlinarith
      nlinarith
  refine ⟨hpos, hsq, ?_, ?_, ?_⟩
  · intro k _
    rw [hPR]
    set S := ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
    have h := hlowR k
    have hr := hRpos k
    have h2 : (2 + S) ^ 2 / 4 ≤ R k ^ 2 := by nlinarith
    rw [zpow_neg, show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · intro L hL k _
    have hLp : 0 < L := lt_of_lt_of_le (hLpos 0) (hL 0)
    rw [zpow_neg, zpow_natCast, ← one_div, ← one_div_pow]
    calc ∏ i ∈ Finset.range k, 1 / (1 + α i)
        ≤ ∏ i ∈ Finset.range k, 1 / (1 + Real.sqrt (min (γ 0) μ / L)) := by
          apply Finset.prod_le_prod
          · intro i _; exact (one_div_pos.mpr (hs1 i)).le
          · intro i _
            have := hsq L hL i
            have hp : 0 < 1 + Real.sqrt (min (γ 0) μ / L) := by
              have := Real.sqrt_nonneg (min (γ 0) μ / L); linarith
            exact one_div_le_one_div_of_le hp (by linarith)
      _ = _ := by rw [Finset.prod_const, Finset.card_range]
  · intro hμ0 k _
    rw [hPR]
    set S := ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
    have h := hupR hμ0 k
    have hr := hRpos k
    rw [zpow_neg, show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]
    apply inv_anti₀ (by positivity)
    nlinarith
