-- Prove2me | solution 1 for NymanBeurling.cofinal_subcubic_rational_gram_rows
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T17:45:31.134954+00:00
-- url     : https://prove2.me/submissions/43981bd5-8b77-46e9-b5da-16a6aa3ce0a2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_arbitrarily_small_remainder_certificates
import Theorems.Thm_NymanBeurling_polynomial_cutoff_rational_gram_criterion

open NymanBeurling.RationalGram

theorem solution (J B : ℕ) :
    ∃ n : ℕ, max 2 B ≤ n ∧
      gap (n^(J+2)) (512*n^(3*(J+1))) ≤ 1/(J+1:ℚ) := by
  obtain ⟨c, K, hc⟩ := NymanBeurling.arbitrarily_small_remainder_certificates J
  change cost c K < 1 / (J + 1 : ℚ) at hc
  let n := max (max 2 B) (c.support.sup id + 1)
  have hB : max 2 B ≤ n := le_max_left _ _
  have hn : 1 ≤ n := by omega
  have hd : n ≤ n ^ (J + 2) := le_self_pow₀ hn (by omega)
  have hs : ∀ k ∈ c.support, k < n ^ (J + 2) := by
    intro k hk
    have hk' : k ≤ c.support.sup id := Finset.le_sup (f := id) hk
    have hn' : c.support.sup id + 1 ≤ n := le_max_right _ _
    omega
  have hrows : n ^ (J + 2) + 1 ≤ 512 * n ^ (3 * (J + 1)) := by
    have hpow : n ^ (J + 2) ≤ n ^ (3 * (J + 1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpos : 0 < n ^ (3 * (J + 1)) := pow_pos (by omega) _
    omega
  have hcomparison :=
    (NymanBeurling.polynomial_cutoff_rational_gram_criterion.2.1
      (n ^ (J + 2)) (512 * n ^ (3 * (J + 1))) hrows).2.2.1
  exact ⟨n, hB, (hcomparison c hs K).trans hc.le⟩
