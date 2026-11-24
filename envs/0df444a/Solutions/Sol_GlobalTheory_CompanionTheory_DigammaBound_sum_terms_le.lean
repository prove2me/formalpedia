-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaBound.sum_terms_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:52.966175+00:00
-- url     : https://prove2.me/submissions/bad58067-b7a1-4b75-a75f-a584df952814

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_term_le_two
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_term_le_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaBound
open Finset
namespace GlobalTheory.CompanionTheory.DigammaBound
theorem _root_.solution (z : ℂ) (hz : 1 / 2 ≤ z.re) (M : ℕ) (hM : 1 ≤ M) (n : ℕ) (hn : M ≤ n) :
    ∑ i ∈ range n, ‖1 / ((i : ℂ) + 1) - 1 / (z + ((i : ℂ) + 1))‖ ≤
      2 * ∑ i ∈ range M, ((i : ℝ) + 1)⁻¹ + ‖z‖ * (1 / (M : ℝ) - 1 / (n : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [sub_self, mul_zero, add_zero, mul_sum]
    exact sum_le_sum fun i _ => term_le_two z hz i
  | succ n hn ih =>
    rw [sum_range_succ]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hM hn)
    have ht := term_le_sq z hz n
    have htel : ‖z‖ / ((n : ℝ) + 1) ^ 2 ≤ ‖z‖ * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
      have : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = ((n : ℝ) * ((n : ℝ) + 1))⁻¹ := by
        field_simp
        ring
      rw [this]
      apply inv_anti₀ (by positivity)
      nlinarith
    push_cast
    nlinarith [ih, ht, htel]
end GlobalTheory.CompanionTheory.DigammaBound
