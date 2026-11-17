-- Prove2me | solution 1 for N25.etaResidueSeries25_trunc_prefix
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:06.448628+00:00
-- url     : https://prove2.me/submissions/cfc4512b-19c4-4caa-a9ae-893f9e9e2b99

import Definitions.Def_N25_UnitSeries

set_option autoImplicit false

open scoped BigOperators

namespace N25

private theorem coeff_mul_high_binomial (p : PowerSeries ℤ) (n e : ℕ)
    (h : n < e) :
    PowerSeries.coeff n (p * (1 - PowerSeries.X ^ e)) = PowerSeries.coeff n p := by
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow',
    if_neg (by omega), sub_zero]

private theorem prefix_coefficient_stable (g n t k : ℕ)
    (hg : 0 < g) (hg25 : g < 25) (hn : n < 25 * t) :
    PowerSeries.coeff n
      (∏ m ∈ Finset.range (t + k),
        ((1 - PowerSeries.X ^ (25 * m + g)) *
          (1 - PowerSeries.X ^ (25 * (m + 1) - g)) : PowerSeries ℤ)) =
    PowerSeries.coeff n
      (∏ m ∈ Finset.range t,
        ((1 - PowerSeries.X ^ (25 * m + g)) *
          (1 - PowerSeries.X ^ (25 * (m + 1) - g)) : PowerSeries ℤ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, Finset.prod_range_succ, ← mul_assoc,
      coeff_mul_high_binomial _ n _ (by omega),
      coeff_mul_high_binomial _ n _ (by omega)]
    exact ih

/-- A residue Euler product needs only the factors below the truncation order. -/
theorem _root_.solution (g N t : ℕ)
    (hg : 0 < g) (hg25 : g < 25) (hNt : N ≤ 25 * t) :
    PowerSeries.trunc N (etaResidueSeries25 g) =
      PowerSeries.trunc N
        (∏ m ∈ Finset.range t,
          ((1 - PowerSeries.X ^ (25 * m + g)) *
            (1 - PowerSeries.X ^ (25 * (m + 1) - g)) : PowerSeries ℤ)) := by
  apply Polynomial.ext
  intro n
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  split_ifs with hn
  · simp only [etaResidueSeries25, PowerSeries.coeff_mk]
    have hleft := prefix_coefficient_stable g n (n + 1) t hg hg25 (by omega)
    have hright := prefix_coefficient_stable g n t (n + 1) hg hg25 (by omega)
    rw [Nat.add_comm (n + 1) t] at hleft
    exact hleft.symm.trans hright
  · rfl

end N25
