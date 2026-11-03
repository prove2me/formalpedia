-- Prove2me | solution 1 for Grunbaum2003.repaired_ray_query_budget_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T07:16:00.350205+00:00
-- url     : https://prove2.me/submissions/cdfaf08d-8f46-4cb9-b0aa-a2985d856961

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003


/-- Summing the corrected two-charge detector costs over a decreasing unknown
facet pool retains the original leading quadratic coefficient. -/
theorem sum_twice_remaining_add_three (m : ℕ) :
    (∑ k ∈ Finset.range m, (2 * (m - k) + 3)) = m * m + 4 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hterm : ∀ k ∈ Finset.range m,
        2 * (m + 1 - k) + 3 = (2 * (m - k) + 3) + 2 := by
      intro k hk
      have hk' : k ≤ m := (Finset.mem_range.mp hk).le
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ih]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, Nat.add_sub_cancel_left]
    ring

/-- Exact original query budget, including the d+1 paid inner-simplex queries.
The geometric/controller premise to establish separately is at most2u+3 detector
calls when u facets remain unknown. -/
theorem corrected_discovery_budget_fits {d m f₀ : ℕ} (hd : 2 ≤ d) (hm : d + 1 ≤ m) :
    f₀ + (d + 1) + ∑ k ∈ Finset.range m, (1 + (d - 1) * (2 * (m - k) + 3)) ≤
      f₀ + (d - 1) * m ^ 2 + (5 * d - 4) * m := by
  have hsum : (∑ k ∈ Finset.range m, (1 + (d - 1) * (2 * (m - k) + 3))) =
      m + (d - 1) * (m * m + 4 * m) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_twice_remaining_add_three]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, mul_one]
  rw [hsum]
  have hcoefficient : 5 * d - 4 = 5 * (d - 1) + 1 := by omega
  have hspare : d + 1 ≤ (d - 1) * m := by
    have hdm : 1 ≤ d - 1 := by omega
    have hmul := Nat.mul_le_mul_right m hdm
    have hmm : m ≤ (d - 1) * m := by simpa only [one_mul] using hmul
    exact hm.trans hmm
  rw [hcoefficient]
  nlinarith only [hspare]


theorem repaired_ray_query_budget_bound (d m f₀ : ℕ) (hd : 2 ≤ d) (hm : d + 1 ≤ m) :
    (∑ k ∈ Finset.range m, (2 * (m - k) + 3)) = m * m + 4 * m ∧
    f₀ + (d + 1) + ∑ k ∈ Finset.range m, (1 + (d - 1) * (2 * (m - k) + 3)) ≤
      f₀ + (d - 1) * m ^ 2 + (5 * d - 4) * m :=
  ⟨sum_twice_remaining_add_three m, corrected_discovery_budget_fits hd hm⟩

end Grunbaum2003

theorem solution (d m f₀ : ℕ) (hd : 2 ≤ d) (hm : d + 1 ≤ m) :
    (∑ k ∈ Finset.range m, (2 * (m - k) + 3)) = m * m + 4 * m ∧
    f₀ + (d + 1) + ∑ k ∈ Finset.range m, (1 + (d - 1) * (2 * (m - k) + 3)) ≤
      f₀ + (d - 1) * m ^ 2 + (5 * d - 4) * m :=
  Grunbaum2003.repaired_ray_query_budget_bound d m f₀ hd hm
