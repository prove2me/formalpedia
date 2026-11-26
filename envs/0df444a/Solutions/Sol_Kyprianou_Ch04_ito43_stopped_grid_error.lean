-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_stopped_grid_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:38:52.839997+00:00
-- url     : https://prove2.me/submissions/fbe7018e-1843-483e-8652-ab9eb420aff9

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_stopped_cell_error
import Theorems.Thm_Kyprianou_Ch04_ito43_cut_sum_bound
open MeasureTheory Set
set_option autoImplicit false

/-- Uniform stopped-grid error is bounded by full-cell L1 errors and a single mesh charge. -/
theorem solution (H : ℝ → ℝ) (g : ℝ → ℝ → ℝ) (u : ℕ → ℝ)
    (hu : Monotone u) (n : ℕ) (T t M δ : ℝ)
    (h0 : u 0 = 0) (hn : u n = T) (ht : t ∈ Icc 0 T)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hmesh : ∀ k < n, u (k+1) - u k ≤ δ)
    (hHi : IntegrableOn H (Icc 0 T))
    (hgi : ∀ r ∈ Icc 0 T, IntegrableOn (fun s => g s r) (Icc 0 T))
    (hH : ∀ s ∈ Icc 0 T, |H s| ≤ M)
    (hg : ∀ s ∈ Icc 0 T, ∀ r ∈ Icc 0 T, |g s r| ≤ M) :
    let v := fun k => min t (u k)
    |(∫ s in Icc 0 t, H s) -
      (∑ k ∈ Finset.range n, (∫ s in Icc (v k) (v (k+1)), g s (v (k+1))))| ≤
      (∑ k ∈ Finset.range n, (∫ s in Icc (u k) (u (k+1)), |H s - g s (u (k+1))|)) +
        2*M*δ := by
  intro v
  have hv : Monotone v := fun i j hij => min_le_min_left _ (hu hij)
  have hv0 : v 0 = 0 := by simp [v,h0,min_eq_right ht.1]
  have hvn : v n = t := by simp [v,hn,min_eq_left ht.2]
  have hsub (k : ℕ) (hk : k < n) : Icc (u k) (u (k+1)) ⊆ Icc 0 T := by
    apply Icc_subset_Icc
    · rw [← h0]; exact hu (Nat.zero_le _)
    · rw [← hn]; exact hu (Nat.succ_le_of_lt hk)
  have hvsub (k : ℕ) (hk : k < n) : Icc (v k) (v (k+1)) ⊆ Icc 0 T := by
    apply Icc_subset_Icc
    · rw [← hv0]; exact hv (Nat.zero_le _)
    · exact (hv (Nat.succ_le_of_lt hk)).trans (hvn.le.trans ht.2)
  have hI (k : ℕ) (hk : k < n) : IntervalIntegrable H volume (v k) (v (k+1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hv (Nat.le_succ k))).mpr
      (hHi.mono_set (hvsub k hk))
  have hsum : (∑ k ∈ Finset.range n, (∫ s in Icc (v k) (v (k+1)), H s)) =
      ∫ s in Icc 0 t, H s := by
    simp only [integral_Icc_eq_integral_Ioc]
    calc
      _ = ∑ k ∈ Finset.range n, (∫ s in v k..v (k+1), H s) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (intervalIntegral.integral_of_le (hv (Nat.le_succ k))).symm
      _ = _ := by
        rw [intervalIntegral.sum_integral_adjacent_intervals hI,hv0,hvn,
          intervalIntegral.integral_of_le ht.1]
  rw [← hsum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Kyprianou.Ch04.ito43_cut_sum_bound u hu t (2*M*δ) (by positivity)
  intro k hk
  have hr : u (k+1) ∈ Icc 0 T := hsub k hk ⟨hu (Nat.le_succ k),le_rfl⟩
  exact Kyprianou.Ch04.ito43_stopped_cell_error H g (u k) (u (k+1)) t M δ
    (hu (Nat.le_succ k)) (hmesh k hk) hM hδ
    (hHi.mono_set (hsub k hk)) ((hgi _ hr).mono_set (hsub k hk))
    (fun s hs => hH s (hsub k hk hs))
    (fun s hs r hrr => hg s (hsub k hk hs) r (hsub k hk hrr))
