-- Prove2me | solution 1 for N25.etaResidueSeries25_coeff
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:05.826188+00:00
-- url     : https://prove2.me/submissions/883fa626-cc1c-4006-849d-cb98b497cc45

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

open Polynomial

namespace N25

private theorem residue_block (r N : ℕ) (hr : 0 < r) (hr25 : r < 25) :
    (∏ k ∈ Finset.range 25,
      if (25 * N + k + 1) % 25 = r then
        (1 - X ^ (25 * N + k + 1) : ℤ[X]) else 1) =
      1 - X ^ (25 * N + r) := by
  rw [Finset.prod_eq_single (r - 1)]
  · rw [if_pos (by omega)]
    congr 2
    omega
  · intro k hk hkr
    rw [Finset.mem_range] at hk
    exact if_neg (by omega)
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

private theorem residue_blocks (g N : ℕ) (hg : 0 < g) (hg25 : g < 25) :
    (∏ k ∈ Finset.range (25 * N),
      ((if (k + 1) % 25 = g then (1 - X ^ (k + 1) : ℤ[X]) else 1) *
        (if (k + 1) % 25 = 25 - g then (1 - X ^ (k + 1) : ℤ[X]) else 1))) =
    ∏ m ∈ Finset.range N,
      ((1 - X ^ (25 * m + g)) * (1 - X ^ (25 * (m + 1) - g)) : ℤ[X]) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.prod_range_add, ih]
    rw [Finset.prod_range_succ (n := N)]
    congr 1
    rw [Finset.prod_mul_distrib, residue_block g N hg hg25,
      residue_block (25 - g) N (by omega) (by omega)]
    have he : 25 * N + (25 - g) = 25 * (N + 1) - g := by omega
    rw [he]

private theorem coeff_mul_high_factor {n e : ℕ} (h : n < e) (p : ℤ[X]) :
    (p * (1 - X ^ e)).coeff n = p.coeff n := by
  rw [mul_sub, mul_one, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow',
    if_neg (by omega), sub_zero]

private theorem residue_coeff_stable (g n N : ℕ) (hN : n ≤ N) :
    (∏ k ∈ Finset.range N,
      ((if (k + 1) % 25 = g then (1 - X ^ (k + 1) : ℤ[X]) else 1) *
        (if (k + 1) % 25 = 25 - g then (1 - X ^ (k + 1) : ℤ[X]) else 1))).coeff n =
    (∏ k ∈ Finset.range n,
      ((if (k + 1) % 25 = g then (1 - X ^ (k + 1) : ℤ[X]) else 1) *
        (if (k + 1) % 25 = 25 - g then (1 - X ^ (k + 1) : ℤ[X]) else 1))).coeff n := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hnN ih =>
    rw [Finset.prod_range_succ]
    split_ifs <;>
      simp only [← mul_assoc, mul_one, coeff_mul_high_factor (by omega : n < N + 1)]
    all_goals exact ih

/-- Each frozen residue-series coefficient is the stabilized coefficient of
the polynomial product indexed by the two nonzero residue classes. -/
theorem _root_.solution (g : ℕ) (hg : 0 < g) (hg25 : g < 25) (n : ℕ) :
    PowerSeries.coeff n (etaResidueSeries25 g) =
      (∏ k ∈ Finset.range n,
        ((if (k + 1) % 25 = g then (1 - X ^ (k + 1) : ℤ[X]) else 1) *
          (if (k + 1) % 25 = 25 - g then (1 - X ^ (k + 1) : ℤ[X]) else 1))).coeff n := by
  have hcast :
      (∏ m ∈ Finset.range (n + 1),
        ((1 - PowerSeries.X ^ (25 * m + g)) *
          (1 - PowerSeries.X ^ (25 * (m + 1) - g)) : PowerSeries ℤ)) =
      (((∏ m ∈ Finset.range (n + 1),
        ((1 - X ^ (25 * m + g)) * (1 - X ^ (25 * (m + 1) - g)) : ℤ[X])) : ℤ[X]) : PowerSeries ℤ) := by
    let ι : ℤ[X] →+* PowerSeries ℤ := Polynomial.coeToPowerSeries.ringHom
    have hX : ι X = PowerSeries.X := Polynomial.coe_X
    calc
      _ = ∏ m ∈ Finset.range (n + 1),
          ι ((1 - X ^ (25 * m + g)) * (1 - X ^ (25 * (m + 1) - g))) := by
        apply Finset.prod_congr rfl
        intro m hm
        simp only [map_mul, map_sub, map_pow, map_one, hX]
      _ = ι (∏ m ∈ Finset.range (n + 1),
          ((1 - X ^ (25 * m + g)) * (1 - X ^ (25 * (m + 1) - g)) : ℤ[X])) :=
        (map_prod ι _ _).symm
      _ = _ := rfl
  simp only [etaResidueSeries25, PowerSeries.coeff_mk]
  rw [hcast, Polynomial.coeff_coe, ← residue_blocks g (n + 1) hg hg25]
  exact residue_coeff_stable g n (25 * (n + 1)) (by omega)

end N25
