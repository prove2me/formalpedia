-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_full_cell_rounding_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:48:40.542877+00:00
-- url     : https://prove2.me/submissions/ac56c84d-2221-460f-b07a-f39c86a35db7

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_ceiling_cell
open MeasureTheory Set
set_option autoImplicit false

/-- Full cell integrals equal the integral evaluated at the right rounded time. -/
theorem solution (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n) (F : ℝ → ℝ → ℝ)
    (hI : IntegrableOn (fun s => F s (T * (Nat.ceil (s * (n : ℝ) / T) : ℝ) / (n : ℝ)))
      (Icc 0 T)) :
    let u : ℕ → ℝ := fun k => T * (k : ℝ) / (n : ℝ)
    (∑ k ∈ Finset.range n, (∫ s in Icc (u k) (u (k+1)), F s (u (k+1)))) =
      ∫ s in Icc 0 T, F s (T * (Nat.ceil (s * (n : ℝ) / T) : ℝ) / (n : ℝ)) := by
  intro u
  let R : ℝ → ℝ := fun s => F s (T * (Nat.ceil (s * (n : ℝ) / T) : ℝ) / (n : ℝ))
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h0 : u 0 = 0 := by simp [u]
  have hN : u n = T := by simp [u, mul_div_cancel_right₀ _ hn']
  have hu : Monotone u := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hT.le) (by positivity)
  have hsub (k : ℕ) (hk : k < n) : Icc (u k) (u (k+1)) ⊆ Icc 0 T := by
    apply Icc_subset_Icc
    · rw [← h0]; exact hu (Nat.zero_le k)
    · rw [← hN]; exact hu (Nat.succ_le_of_lt hk)
  have hcell (k : ℕ) :
      (∫ s in Icc (u k) (u (k+1)), F s (u (k+1))) =
      ∫ s in u k..u (k+1), R s := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (hu (Nat.le_succ k))]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have h := Kyprianou.Ch04.ito43_ceiling_cell T s hT n k hn hs
    simp only [R,h,u]
  have hRi (k : ℕ) (hk : k < n) : IntervalIntegrable R volume (u k) (u (k+1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hu (Nat.le_succ k))).mpr
      (hI.mono_set (hsub k hk))
  calc
    _ = ∑ k ∈ Finset.range n, (∫ s in u k..u (k+1), R s) :=
      Finset.sum_congr rfl fun k _ => hcell k
    _ = _ := by
      rw [intervalIntegral.sum_integral_adjacent_intervals hRi, h0,hN,
        intervalIntegral.integral_of_le hT.le, integral_Icc_eq_integral_Ioc]
