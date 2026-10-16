-- Prove2me | solution 1 for JRPHard.RangeDiv.item2_pinned
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:49:26.740633+00:00
-- url     : https://prove2.me/submissions/b14862cc-c2fc-48f3-95b3-d6a12f514861

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting
open JRPHard.RangeDiv
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
-- Mathematical source: Schulz and Telha, arXiv:2007.09045v1, proof of Lemma 3.
theorem solution (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) (q₁ q₂ : ℕ)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hne : q₂ ≠ M) :
    (threshold M L U : ℝ) < rangeCost M L U q₁ q₂ := by
  have hM : 0 < M := lt_of_lt_of_le hI.1 (hI.2.1.trans hI.2.2.1)
  have hg : 0 < (Nat.gcd q₁ q₂ : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left q₂ hq₁
  have hL : 0 < (L : ℝ) := by exact_mod_cast hI.1
  have hU : 0 < (U : ℝ) := by exact_mod_cast lt_of_lt_of_le hI.1 hI.2.1
  have hq : 0 < (q₁ : ℝ) := by exact_mod_cast hq₁
  have hLU : (L : ℝ) ≤ U := by exact_mod_cast hI.2.1
  have hUM : (U : ℝ) ≤ M := by exact_mod_cast hI.2.2.1
  have hf : (L : ℝ) < q₁ + (L : ℝ) * U / (Nat.gcd q₁ q₂ : ℝ) := by
    by_cases hLq : (L : ℝ) ≤ q₁
    · have hp : 0 < (L : ℝ) * U / (Nat.gcd q₁ q₂ : ℝ) := by positivity
      linarith
    · have hgq : (Nat.gcd q₁ q₂ : ℝ) ≤ q₁ := by exact_mod_cast Nat.gcd_le_left q₂ hq₁
      have hgl : (Nat.gcd q₁ q₂ : ℝ) ≤ U := by linarith
      have hh : (L : ℝ) ≤ (L : ℝ) * U / (Nat.gcd q₁ q₂ : ℝ) :=
        (le_div_iff₀ hg).2 (mul_le_mul_of_nonneg_left hgl hL.le)
      linarith
  have he := JRPResearch.item2_gap M q₂ hM hq₂ hne
  unfold rangeCost JRPHard.Periodic.periodicCost coefK0 threshold
  change ((L + U + 2 * M ^ 2 * (M + 1) : ℕ) : ℝ) <
    JRPHard.Aperiodic.eoq 0 1 q₁ + JRPHard.Periodic.eoq2 M q₂ + ((L * U : ℕ) : ℝ) / (Nat.gcd q₁ q₂ : ℝ)
  simp only [JRPHard.Aperiodic.eoq, zero_div, one_mul, zero_add]
  push_cast
  linarith
