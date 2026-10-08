-- Prove2me | solution 1 for MultiSecretary.BR.uniformly_bounded_regret
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T03:49:21.344829+00:00
-- url     : https://prove2.me/submissions/294e084f-dd91-408b-8b1f-f4e20097daba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MultiSecretary_BR_Model
import Definitions.Def_MultiSecretary_BR_Policy
import Theorems.Thm_MultiSecretary_BR_br_satisfies_sufficient_condition
import Theorems.Thm_MultiSecretary_BR_sufficient_condition

set_option autoImplicit false

open Finset MultiSecretary.BR in
theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ (m : ℕ) (I : Instance m), I.eps = ε → ∀ n k : ℕ, k ≤ n →
      I.brPolicy n k ∈ policies n m k ∧
      I.Voff n k - I.Von n k ≤ I.Voff n k - I.value (I.brPolicy n k) ∧
      I.Voff n k - I.value (I.brPolicy n k) ≤ I.a I.top * M := by
  obtain ⟨M, hM⟩ := br_satisfies_sufficient_condition ε (ε / 2) hε (by linarith) (by linarith)
  refine ⟨3 * M + 1 / (4 * ε), fun m I hI n k hk => ?_⟩
  obtain ⟨hmem, hτn, hτ, h1, h2, h3, h4⟩ := hM m I hI n k hk
  refine ⟨hmem, ?_, ?_⟩
  · have : I.value (I.brPolicy n k) ≤ I.Von n k := by
      unfold Instance.Von; exact Finset.le_sup' I.value hmem
    linarith
  · have := sufficient_condition I n k hk _ hmem _ hτn hτ M h1 h2 h3 h4
    rw [hI] at this
    have he : I.a I.top / (4 * ε) = I.a I.top * (1 / (4 * ε)) := by ring
    nlinarith [he]
