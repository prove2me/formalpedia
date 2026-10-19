-- Prove2me | solution 1 for LeiBR.Async.eq_30
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:40:00.07411+00:00
-- url     : https://prove2.me/submissions/c8b4c38e-e90d-4ecb-a408-bcd578ce8ce5

import Mathlib
set_option autoImplicit false

theorem solution (β : ℝ) (hβ : 1 < β) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, β ^ k ≤ ∫ x in (1 : ℝ)..((K : ℝ) + 1), β ^ x ∧
    ∫ x in (1 : ℝ)..((K : ℝ) + 1), β ^ x ≤ β ^ ((K : ℝ) + 1) / Real.log β := by
  have hb0 : 0 < β := by linarith
  have hL : 0 < Real.log β := Real.log_pos hβ
  have hLle : Real.log β ≤ β - 1 := by
    have := Real.add_one_le_exp (Real.log β)
    rw [Real.exp_log hb0] at this; linarith
  have hint : ∫ x in (1 : ℝ)..((K : ℝ) + 1), β ^ x
      = (β ^ ((K : ℝ) + 1) - β) / Real.log β := by
    have h : ∀ x ∈ Set.uIcc (1 : ℝ) ((K : ℝ) + 1),
        HasDerivAt (fun x : ℝ => β ^ x / Real.log β) (β ^ x) x := by
      intro x _
      have h1 : HasDerivAt (fun x : ℝ => β ^ x) (β ^ x * Real.log β) x := by
        have e : (fun x : ℝ => β ^ x) = fun x => Real.exp (Real.log β * x) :=
          funext fun x => Real.rpow_def_of_pos hb0 x
        rw [e, Real.rpow_def_of_pos hb0 x]
        have := ((hasDerivAt_id x).const_mul (Real.log β)).exp
        refine this.congr_deriv ?_
        simp
      refine (h1.div_const (Real.log β)).congr_deriv ?_
      field_simp
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt h
      (by
        apply Continuous.intervalIntegrable
        exact Real.continuous_const_rpow (ne_of_gt hb0) |>.congr (fun _ => rfl) |> fun h => h)
    rw [this, Real.rpow_one]
    ring
  have hgeo : ∀ n : ℕ, (∑ k ∈ Finset.Icc 1 n, β ^ k) * (β - 1) = β ^ (n + 1) - β := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), add_mul, ih]
      ring
  have hpow : β ^ ((K : ℝ) + 1) = β ^ (K + 1) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  rw [hint, hpow]
  have hnum : 0 ≤ β ^ (K + 1) - β := by
    have : β ^ 1 ≤ β ^ (K + 1) := pow_le_pow_right₀ hβ.le (by omega)
    simpa using this
  have hs : ∑ k ∈ Finset.Icc 1 K, β ^ k = (β ^ (K + 1) - β) / (β - 1) := by
    rw [eq_div_iff (by linarith)]; exact hgeo K
  constructor
  · rw [hs]
    exact div_le_div_of_nonneg_left hnum hL hLle
  · apply div_le_div_of_nonneg_right _ hL.le
    linarith
