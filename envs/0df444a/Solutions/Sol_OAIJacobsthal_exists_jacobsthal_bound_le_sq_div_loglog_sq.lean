-- Prove2me | solution 1 for OAIJacobsthal.exists_jacobsthal_bound_le_sq_div_loglog_sq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:34:46.542868+00:00
-- url     : https://prove2.me/submissions/e04c4a2b-4d14-4726-b50b-d5ab757ce2af

import Mathlib
import Definitions.Def_JacobsthalImproved
import Theorems.Thm_OAI_Erdos970_Erdos970Final_erdos_970_iterated_log

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k →
      ∃ m : ℕ,
        (∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
          ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime n) ∧
        (m : ℝ) ≤ C * (k : ℝ) ^ 2 / (Real.log (Real.log (3 * (k : ℝ)))) ^ 2 :=
  OAI.Erdos970.Erdos970Final.erdos_970_iterated_log
