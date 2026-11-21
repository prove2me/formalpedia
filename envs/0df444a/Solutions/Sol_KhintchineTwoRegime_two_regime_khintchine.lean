-- Prove2me | solution 1 for KhintchineTwoRegime.two_regime_khintchine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T02:45:03.821214+00:00
-- url     : https://prove2.me/submissions/9620585a-4ea3-4cee-aab2-6ca184d0d6ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_fourProfile
import Definitions.Def_KhintchineTwoRegime_sixProfile
import Definitions.Def_KhintchineTwoRegime_Abound
import Theorems.Thm_KhintchineTwoRegime_theorem_1
import Theorems.Thm_KhintchineTwoRegime_theorem_2

namespace KhintchineTwoRegime

theorem _root_.solution :
    (∀ n : ℕ, 2 ≤ n → ∀ τ : ℝ, ∀ ω ∈ Cn n τ,
      1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) ≤ K n ω) ∧
    (∀ n : ℕ, 4 ≤ n → ∀ τ : ℝ, 0 ≤ τ → τ ≤ Real.sqrt (2 - Real.sqrt 2) →
      fourProfile n τ ∈ Cn n τ ∧
      K n (fourProfile n τ) =
        1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) ∧
      ∀ ω ∈ Cn n τ,
        K n ω = 1 / Real.sqrt 2 + (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2)) →
          ω = fourProfile n τ) ∧
    (∀ n : ℕ, 6 ≤ n →
      ∀ τ ∈ Set.Icc (Real.sqrt (2 - Real.sqrt 2)) (Real.sqrt (2 - Real.sqrt 966 / 22)),
        sixProfile n τ ∈ Cn n τ ∧
        (∀ ω ∈ Cn n τ, K n (sixProfile n τ) ≤ K n ω) ∧
        (∀ ω ∈ Cn n τ, K n ω = K n (sixProfile n τ) → ω = sixProfile n τ) ∧
        K n (sixProfile n τ) = Abound ((2 - τ ^ 2) / Real.sqrt 2)) ∧
    ((7663211842 : ℝ) / 10 ^ 10 < Real.sqrt (2 - Real.sqrt 966 / 22) ∧
      Real.sqrt (2 - Real.sqrt 966 / 22) < (7663211843 : ℝ) / 10 ^ 10) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact theorem_1.1
  · exact theorem_1.2
  · exact theorem_2.1
  · exact theorem_2.2

end KhintchineTwoRegime
