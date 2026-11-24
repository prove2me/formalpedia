-- Prove2me | solution 1 for LindbladQueryOptimal.Simulation.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T20:36:57.6478+00:00
-- url     : https://prove2.me/submissions/d945e31f-7bd4-48ea-a661-9e1b7e42001c

import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation

attribute [local instance] Classical.propDecidable Classical.decEq

end LindbladQueryOptimal.Simulation

theorem solution_aux (B : ℝ) (hB : 1 ≤ B) (τ ε : ℝ) (q : ℕ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε2 : ε ≤ 1/2)
    (h : 100 * B^2 * (1 + τ + Real.log (1/ε) / Real.log (Real.exp 1 + Real.log (1/ε)/τ)) ≤ q) :
    B * Real.sqrt τ * (B * Real.sqrt (τ/q))^q ≤ ε := by
  set L := Real.log (1/ε) with hL
  have hLpos : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  have hL0 : 0 ≤ L := hLpos.le
  set u := L/τ with hu
  have hu0 : 0 ≤ u := div_nonneg hL0 hτ.le
  set ℓ := Real.log (Real.exp 1 + u) with hℓ
  have he1 : (1:ℝ) ≤ Real.exp 1 := by simpa using Real.add_one_le_exp (1:ℝ)
  have hℓ1 : 1 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ Real.exp 1 + u by linarith)
    rw [Real.log_exp] at this
    exact this
  have hℓ0 : 0 < ℓ := by linarith
  set s := Real.sqrt (Real.exp 1 + u) with hs
  have hs2 : s^2 = Real.exp 1 + u := Real.sq_sqrt (by positivity)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hℓs : ℓ = 2 * Real.log s := by
    rw [hℓ, ← hs2, Real.log_pow]; norm_num
  have hlogs : Real.log s ≤ s / Real.exp 1 := by
    have := Real.add_one_le_exp (Real.log (s / Real.exp 1))
    rw [Real.exp_log (by positivity), Real.log_div hs0.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
    linarith
  have hexp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp0 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hℓs' : ℓ ≤ s := by
    rw [hℓs]
    have : Real.log s * Real.exp 1 ≤ s := by rwa [le_div_iff₀ (Real.exp_pos 1)] at hlogs
    nlinarith
  have hq : (0:ℝ) < q := by
    have : 0 < L / ℓ := by positivity
    have : 0 < 100 * B^2 * (1 + τ + L/ℓ) := by positivity
    linarith
  set q' : ℝ := (q:ℝ) with hq'
  have hLℓ : L / ℓ * ℓ = L := div_mul_cancel₀ _ hℓ0.ne'
  have hqℓ : 100 * B^2 * L ≤ q' * ℓ := by
    have : 100 * B^2 * (L/ℓ) ≤ q' := by nlinarith [sq_nonneg B, hτ]
    have := mul_le_mul_of_nonneg_right this hℓ0.le
    nlinarith
  have hqτ : 100 * B^2 * (τ + L/ℓ) ≤ q' := by nlinarith [sq_nonneg B]
  have hB2 : 1 ≤ B^2 := by nlinarith
  -- ratio r = q/(B^2 τ)
  set r := q' / (B^2 * τ) with hr
  have hBτ : 0 < B^2 * τ := by positivity
  have hr0 : 0 < r := by positivity
  have hr1 : 100 ≤ r := by
    rw [hr, le_div_iff₀ hBτ]; nlinarith [sq_nonneg B]
  have hrs : s ≤ r := by
    have h1 : 100 * (1 + u/ℓ) ≤ r := by
      rw [hr, le_div_iff₀ hBτ]
      have : u / ℓ * τ = L / ℓ := by rw [hu]; field_simp
      nlinarith [sq_nonneg B]
    have h2 : u / s ≤ u / ℓ := div_le_div_of_nonneg_left hu0 hℓ0 hℓs'
    have h3 : s ≤ 100 * (1 + u/s) := by
      have hs1 : 1 ≤ s := by nlinarith only [hs2, he1, hu0, hs0]
      have : 1 + u/s = (s + u)/s := by field_simp
      rw [this, mul_div_assoc', le_div_iff₀ hs0]
      nlinarith only [hs2, hexp, hu0, hs1]
    linarith only [h1, h2, h3]
  have hM4 : 4 ≤ Real.log r := by
    have : Real.exp 4 ≤ r := by
      have : Real.exp 4 = (Real.exp 1)^4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]; nlinarith [Real.exp_pos 1, pow_pos (Real.exp_pos 1) 2, pow_pos (Real.exp_pos 1) 3]
    calc (4:ℝ) = Real.log (Real.exp 4) := (Real.log_exp 4).symm
      _ ≤ Real.log r := Real.log_le_log (Real.exp_pos 4) this
  have hMℓ : ℓ / 2 ≤ Real.log r := by
    have := Real.log_le_log hs0 hrs
    linarith only [this, hℓs]
  set M := Real.log r with hM
  -- log y
  set y := B * Real.sqrt (τ/q') with hy
  have hy0 : 0 < y := by positivity
  have hy2 : y^2 = 1 / r := by
    rw [hy, mul_pow, Real.sq_sqrt (by positivity), hr]; field_simp
  have hlogy : Real.log y = -M/2 := by
    have : Real.log (y^2) = -M := by rw [hy2, one_div, Real.log_inv]
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hlogB : Real.log B ≤ B - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hlogτ : Real.log τ ≤ τ - 1 := Real.log_le_sub_one_of_pos hτ
  have hpos : 0 < B * Real.sqrt τ * y^(q) := by positivity
  have hlogLHS : Real.log (B * Real.sqrt τ * y^q) = Real.log B + Real.log τ / 2 + q' * (-M/2) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_sqrt hτ.le, Real.log_pow, hlogy]
  have hlogε : Real.log ε = -L := by
    rw [hL, one_div, Real.log_inv]; ring
  have key : Real.log B + Real.log τ / 2 + q' * (-M/2) ≤ -L := by
    have hBB : B ≤ B^2 := by nlinarith only [hB]
    have hBτ' : τ ≤ B^2 * τ := by nlinarith only [hB2, hτ]
    have hq1 : 100 * B^2 * (1 + τ) ≤ q' := by
      have : 0 ≤ L / ℓ := by positivity
      have h2 : 0 ≤ 100 * B^2 * (L / ℓ) := by positivity
      nlinarith only [h, h2]
    have e1 : B + τ/2 ≤ q' := by linarith only [hq1, hBB, hBτ', hB, hτ]
    have e2 : q' * 4 ≤ q' * M := mul_le_mul_of_nonneg_left hM4 hq.le
    have e3 : q' * (ℓ/2) ≤ q' * M := mul_le_mul_of_nonneg_left hMℓ hq.le
    have hBL : L ≤ B^2 * L := by nlinarith only [hB2, hL0]
    have e4 : q' * (-M/2) = -(q' * M)/2 := by ring
    have e5 : q' * (ℓ/2) = (q' * ℓ)/2 := by ring
    rw [e4]
    linarith [hlogB, hlogτ, e1, e2, e3, e5, hqℓ, hBL]
  rw [← Real.log_le_log_iff hpos hε, hlogLHS, hlogε]
  exact key

theorem solution (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ ε : ℝ) (q : ℕ),
      0 ≤ τ → 0 < ε → ε ≤ 1/2 → C * LindbladQueryOptimal.Simulation.queryScale τ ε ≤ q →
      B * Real.sqrt τ * (B * Real.sqrt (τ/q))^q ≤ ε := by
  refine ⟨100 * B^2, by positivity, ?_⟩
  intro τ ε q hτ hε hε2 h
  rcases hτ.eq_or_lt with h0 | h0
  · subst h0
    simp only [LindbladQueryOptimal.Simulation.queryScale, if_true] at h
    have : (1:ℝ) ≤ q := by nlinarith [sq_nonneg B]
    have hq : q ≠ 0 := by rintro rfl; simp at this; linarith
    simp [hq]; exact hε.le
  · simp only [LindbladQueryOptimal.Simulation.queryScale, h0.ne', if_false] at h
    exact solution_aux B hB τ ε q h0 hε hε2 h
