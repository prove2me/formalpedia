-- Prove2me | solution 1 for NAGFlow.Nesterov.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:00:55.406932+00:00
-- url     : https://prove2.me/submissions/92074743-0853-489a-be30-5df1cf9c6c0e

import Mathlib
set_option autoImplicit false

theorem solution (μ : ℝ) (α γ Ls : ℕ → ℝ) (hγ0 : 0 < γ 0) (hμ : 0 ≤ μ)
    (hLpos : ∀ k, 0 < Ls k) (hLmu : ∀ k, μ ≤ Ls k)
    (hα : ∀ k, Ls k * α k ^ 2 = γ (k + 1)) (hαpos : ∀ k, 0 < α k)
    (hγ : ∀ k, γ (k + 1) = (1 - α k) * γ k + μ * α k) :
    (∀ k, 0 < γ k) ∧
      (∀ k, 0 < α k ∧ α k ≤ 1) ∧
      (∀ L : ℝ, (∀ i, Ls i ≤ L) → ∀ k, Real.sqrt (min (γ 1) μ / L) ≤ α k) ∧
      (∀ k : ℕ, 1 ≤ k →
        ∏ i ∈ Finset.range k, (1 - α i) ≤
          4 * (2 + ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) ^ (-2 : ℤ)) ∧
      (∀ L : ℝ, (∀ i, Ls i ≤ L) → ∀ k : ℕ, 1 ≤ k →
        ∏ i ∈ Finset.range k, (1 - α i) ≤ (1 - Real.sqrt (min (γ 1) μ / L)) ^ k) ∧
      (μ = 0 → ∀ k : ℕ, 1 ≤ k →
        (1 + ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) ^ (-2 : ℤ) ≤
          ∏ i ∈ Finset.range k, (1 - α i)) := by
  have hpos : ∀ k, 0 < γ k := by
    intro k
    cases k with
    | zero => exact hγ0
    | succ k => rw [← hα k]; have := hLpos k; have := hαpos k; positivity
  have hα1 : ∀ k, α k ≤ 1 := by
    intro k
    by_contra h
    push_neg at h
    have h1 := hα k
    have h2 := hγ k
    have h3 := hpos k
    have h4 := hαpos k
    have h5 := hLmu k
    have h6 := hLpos k
    nlinarith [mul_pos h4 (sub_pos.mpr h), mul_pos h3 (sub_pos.mpr h),
      mul_nonneg h4.le (sub_nonneg.mpr h5), mul_pos (mul_pos h6 h4) (sub_pos.mpr h)]
  have hm : ∀ k, min (γ 1) μ ≤ γ (k + 1) := by
    intro k
    induction k with
    | zero => exact min_le_left _ _
    | succ k ih =>
      have h2 := hγ (k + 1)
      have h4 := hαpos (k + 1)
      have h5 := hα1 (k + 1)
      have hm' : min (γ 1) μ ≤ μ := min_le_right _ _
      nlinarith [mul_nonneg (sub_nonneg.mpr h5) (sub_nonneg.mpr ih),
        mul_nonneg h4.le (sub_nonneg.mpr hm')]
  have hsq : ∀ L : ℝ, (∀ i, Ls i ≤ L) → ∀ k, Real.sqrt (min (γ 1) μ / L) ≤ α k := by
    intro L hL k
    have hLp : 0 < L := lt_of_lt_of_le (hLpos 0) (hL 0)
    apply Real.sqrt_le_iff.mpr
    refine ⟨(hαpos k).le, ?_⟩
    rw [div_le_iff₀ hLp]
    have h1 := hα k
    have h2 := hm k
    have h5 : Ls k * α k ^ 2 ≤ L * α k ^ 2 :=
      mul_le_mul_of_nonneg_right (hL k) (by positivity)
    nlinarith
  have hnn : ∀ i, 0 ≤ 1 - α i := fun i => by linarith [hα1 i]
  -- products
  set u : ℕ → ℝ := fun k => ∏ i ∈ Finset.range k, Real.sqrt (1 - α i) with hudef
  have hu0 : u 0 = 1 := by simp [hudef]
  have husucc : ∀ k, u (k + 1) = u k * Real.sqrt (1 - α k) := fun k => by
    simp only [hudef, Finset.prod_range_succ]
  have hunn : ∀ k, 0 ≤ u k := fun k =>
    Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have hu2 : ∀ k, u k ^ 2 = ∏ i ∈ Finset.range k, (1 - α i) := by
    intro k
    simp only [hudef]
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hnn i)
  have hsqs : ∀ k, Real.sqrt (1 - α k) ^ 2 = 1 - α k := fun k => Real.sq_sqrt (hnn k)
  have hs1 : ∀ k, Real.sqrt (1 - α k) ≤ 1 := fun k => by
    rw [Real.sqrt_le_one]; linarith [hαpos k]
  have hkey : ∀ k, (Real.sqrt (γ 0 / Ls k)) ^ 2 = γ 0 / Ls k := fun k =>
    Real.sq_sqrt (div_nonneg hγ0.le (hLpos k).le)
  -- γ_k ≥ γ_0 u_k²
  have hgu : ∀ k, γ 0 * u k ^ 2 ≤ γ k := by
    intro k
    induction k with
    | zero => rw [hu0]; simp
    | succ k ih =>
      have h2 := hγ k
      have h4 := hαpos k
      rw [husucc, mul_pow, hsqs]
      nlinarith [mul_nonneg (hnn k) (sub_nonneg.mpr ih), mul_nonneg hμ h4.le]
  have hgu0 : μ = 0 → ∀ k, γ k = γ 0 * u k ^ 2 := by
    intro hμ0 k
    induction k with
    | zero => rw [hu0]; simp
    | succ k ih =>
      rw [hγ k, husucc, mul_pow, hsqs, hμ0, ih]; ring
  -- core inequality: c * u_{k+1} ≤ α_k
  have hc : ∀ k, Real.sqrt (γ 0 / Ls k) * u (k + 1) ≤ α k := by
    intro k
    have hL := hLpos k
    have h1 := hα k
    have h2 := hgu (k + 1)
    have h4 : (Real.sqrt (γ 0 / Ls k) * u (k + 1)) ^ 2 ≤ α k ^ 2 := by
      rw [mul_pow, hkey]
      rw [div_mul_eq_mul_div, div_le_iff₀ hL]
      nlinarith
    exact le_of_sq_le_sq h4 (hαpos k).le
  have hc' : μ = 0 → ∀ k, α k ≤ Real.sqrt (γ 0 / Ls k) * u (k + 1) := by
    intro hμ0 k
    have hL := hLpos k
    have h1 := hα k
    have h2 := hgu0 hμ0 (k + 1)
    have h4 : α k ^ 2 ≤ (Real.sqrt (γ 0 / Ls k) * u (k + 1)) ^ 2 := by
      rw [mul_pow, hkey]
      rw [div_mul_eq_mul_div, le_div_iff₀ hL]
      nlinarith
    exact le_of_sq_le_sq h4 (mul_nonneg (Real.sqrt_nonneg _) (hunn _))
  -- upper bound
  have hup : ∀ k, u k * (1 + (∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) / 2) ≤ 1 := by
    intro k
    induction k with
    | zero => simp [hu0]
    | succ k ih =>
      rw [Finset.sum_range_succ, husucc]
      have h1 := hc k
      rw [husucc] at h1
      have hs := hsqs k
      have hs0 := Real.sqrt_nonneg (1 - α k)
      have hs1' := hs1 k
      have hu := hunn k
      set s := Real.sqrt (1 - α k)
      set c := Real.sqrt (γ 0 / Ls k)
      set T := (∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i))
      have hα' : α k = 1 - s ^ 2 := by linarith
      rw [hα'] at h1
      have e1 : u k * s * (1 + T / 2) ≤ s := by nlinarith
      have e2 : u k * s * c ≤ 1 - s ^ 2 := by nlinarith
      nlinarith [sq_nonneg (1 - s)]
  have hlo : μ = 0 → ∀ k, 1 ≤ u k * (1 + ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)) := by
    intro hμ0 k
    induction k with
    | zero => simp [hu0]
    | succ k ih =>
      rw [Finset.sum_range_succ, husucc]
      have h1 := hc' hμ0 k
      rw [husucc] at h1
      have hs := hsqs k
      have hs0 := Real.sqrt_nonneg (1 - α k)
      have hs1' := hs1 k
      have hu := hunn k
      set s := Real.sqrt (1 - α k)
      set c := Real.sqrt (γ 0 / Ls k)
      set T := (∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i))
      have hα' : α k = 1 - s ^ 2 := by linarith
      rw [hα'] at h1
      have e1 : s ≤ u k * s * (1 + T) := by nlinarith
      have e2 : 1 - s ^ 2 ≤ u k * s * c := by nlinarith
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1')]
  refine ⟨hpos, fun k => ⟨hαpos k, hα1 k⟩, hsq, ?_, ?_, ?_⟩
  · intro k _
    rw [← hu2]
    set S := ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
    have h := hup k
    have hu := hunn k
    have h2 : u k * (2 + S) ≤ 2 := by nlinarith
    have h3 : (u k * (2 + S)) ^ 2 ≤ 2 ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    rw [zpow_neg, show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    nlinarith
  · intro L hL k _
    calc ∏ i ∈ Finset.range k, (1 - α i)
        ≤ ∏ i ∈ Finset.range k, (1 - Real.sqrt (min (γ 1) μ / L)) := by
          apply Finset.prod_le_prod
          · intro i _; exact hnn i
          · intro i _
            have := hsq L hL i
            linarith
      _ = _ := by rw [Finset.prod_const, Finset.card_range]
  · intro hμ0 k _
    rw [← hu2]
    set S := ∑ i ∈ Finset.range k, Real.sqrt (γ 0 / Ls i)
    have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
    have h := hlo hμ0 k
    have hu := hunn k
    rw [zpow_neg, show (2:ℤ) = ((2:ℕ):ℤ) by norm_num, zpow_natCast]
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    nlinarith
