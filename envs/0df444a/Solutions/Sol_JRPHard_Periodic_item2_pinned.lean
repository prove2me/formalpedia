-- Prove2me | solution 1 for JRPHard.Periodic.item2_pinned
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T07:35:51.78077+00:00
-- url     : https://prove2.me/submissions/0e29588b-1185-40c9-a540-40fcf0f741f6

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting
open JRPHard.Periodic
set_option autoImplicit false

namespace JRPResearch

theorem item2_gap (M q : ℕ) (hM : 0 < M) (hq : 0 < q) (hne : q ≠ M) :
    2 * (M : ℝ)^2 * (M + 1) + M ≤ JRPHard.Periodic.eoq2 M q := by
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hg : (q : ℝ) ≤ (M + 1) * ((q : ℝ) - M)^2 := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : (q : ℝ) + 1 ≤ M := by exact_mod_cast h
      have hs : (1 : ℝ) ≤ ((q : ℝ) - M)^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (M : ℝ) + 1 by positivity)
      nlinarith
    · have hh : (M : ℝ) + 1 ≤ q := by exact_mod_cast h
      have hd : 0 ≤ (q : ℝ) - M := by linarith
      have hm := mul_nonneg (show 0 ≤ (q : ℝ) - M - 1 by linarith)
        (show 0 ≤ ((M : ℝ) + 1) * ((q : ℝ) - M) + M by positivity)
      nlinarith
  unfold JRPHard.Periodic.eoq2 JRPHard.Aperiodic.eoq JRPHard.Periodic.coefK2 JRPHard.Periodic.coefH2
  push_cast
  apply (mul_le_mul_iff_left₀ hqR).mp
  simp only [add_mul, div_mul_cancel₀ _ (ne_of_gt hqR)]
  have hm := mul_le_mul_of_nonneg_left hg hMR.le
  nlinarith

end JRPResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Schulz and Telha, arXiv:2007.09045v1, proof of Lemma 2.
-- Includes the full integer EOQ gap proof; platform imports do not export helpers.
theorem solution (M : ℕ) (hM : 2 ≤ M) :
    (∀ q₁ q₂ : ℕ, 0 < q₁ → 0 < q₂ → q₂ ≠ M →
      (M : ℝ) + eoq2 M M + 1 < lemma2Cost M q₁ q₂) ∧
    lemma2Cost M M M = (M : ℝ) + eoq2 M M + 1 := by
  have hMp : 0 < M := by omega
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hMp
  have he0 : eoq2 M M = 2 * (M : ℝ)^2 * (M + 1) := by
    unfold eoq2 JRPHard.Aperiodic.eoq coefK2 coefH2
    push_cast
    field_simp
    ring
  constructor
  · intro q₁ q₂ hq₁ hq₂ hne
    have he := JRPResearch.item2_gap M q₂ hMp hq₂ hne
    rw [← he0] at he
    have hg : 0 < (Nat.gcd q₁ q₂ : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left q₂ hq₁
    have hq : (1 : ℝ) ≤ q₁ := by exact_mod_cast hq₁
    have hf : 0 < (M : ℝ) / (Nat.gcd q₁ q₂ : ℝ) := div_pos hMR hg
    simp only [lemma2Cost, periodicCost, coefK0, coefK1, coefH1, Nat.cast_zero, Nat.cast_one]
    change (M : ℝ) + eoq2 M M + 1 <
      JRPHard.Aperiodic.eoq 0 1 q₁ + eoq2 M q₂ + (M : ℝ) / (Nat.gcd q₁ q₂ : ℝ)
    simp only [JRPHard.Aperiodic.eoq, zero_div, one_mul, zero_add]
    linarith
  · simp only [lemma2Cost, periodicCost, coefK0, coefK1, coefH1, Nat.cast_zero, Nat.cast_one]
    change JRPHard.Aperiodic.eoq 0 1 M + eoq2 M M + (M : ℝ) / (Nat.gcd M M : ℝ) = _
    simp only [JRPHard.Aperiodic.eoq, zero_div, one_mul, zero_add, Nat.gcd_self,
      div_self (ne_of_gt hMR)]
