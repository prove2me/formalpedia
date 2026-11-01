-- Prove2me | solution 1 for OAI.Ostmann.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T22:43:00.915461+00:00
-- url     : https://prove2.me/submissions/9cd099b4-6092-4e6a-b275-44344042f853

import Mathlib
import Theorems.Thm_OAI_Ostmann_inverseGoldbach

open scoped Pointwise symmDiff

theorem solution : ∀ A B : Set ℕ, A.Nontrivial → B.Nontrivial →
    Set.Infinite ((A + B) ∆ {n : ℕ | Nat.Prime n}) :=
  fun A B hA hB => OAI.Ostmann.inverseGoldbach A B hA hB
