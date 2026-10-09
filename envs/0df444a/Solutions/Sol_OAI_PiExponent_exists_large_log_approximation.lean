-- Prove2me | solution 1 for OAI.PiExponent.exists_large_log_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:58:45.036996+00:00
-- url     : https://prove2.me/submissions/ef2a6b35-3f47-4e3b-a868-c3c9c4d49248

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic



theorem solution
    (nu X : ℝ) (hnu : 0 < nu)
    (hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu)) :
    ∃ p : ℤ, ∃ q : ℕ,
      2 ≤ q ∧ X < Real.log q ∧ p ≠ 0 ∧
        |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp X)
  obtain ⟨p, q, hq, happrox⟩ := hbad (max 2 N)
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hNq : N ≤ q := le_trans (le_max_right _ _) hq
  have hexp : Real.exp X < (q : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hNq)
  have hlog : X < Real.log q := by
    simpa using Real.log_lt_log (Real.exp_pos X) hexp
  have hp : p ≠ 0 := by
    intro hp0
    have hpow : (q : ℝ) ^ (-nu) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ q))
        (by linarith)
    have hpi : Real.pi ≤ (q : ℝ) ^ (-nu) := by
      simpa [hp0, abs_of_pos Real.pi_pos] using happrox
    have hpi2 := Real.pi_gt_three
    linarith
  exact ⟨p, q, hq2, hlog, hp, happrox⟩

#print axioms solution
