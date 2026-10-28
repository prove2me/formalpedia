-- Prove2me | solution 1 for NQueensComp.NPC.observation_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:34:43.758812+00:00
-- url     : https://prove2.me/submissions/652af927-8995-4597-b16d-83cc3089a29d

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

open NQueensComp.NPC

theorem solution :
    IsNQueensSol 19 Q19 ∧
    (∀ q ∈ Q19, diffDiag q ≠ 1 ∧ diffDiag q ≠ 0 ∧ diffDiag q ≠ -1) ∧
    ((0, 8) ∈ Q19 ∧ (17, 0) ∈ Q19) ∧
    (1 < |((sumDiag (19, 8) : ℕ) : ℤ) - ((sumDiag (17, 19) : ℕ) : ℤ)| ∧
      1 < |diffDiag (19, 8) - diffDiag (17, 19)|) ∧
    ∀ m ∈ ({(19, 8), (17, 19)} : Finset Queen), ∀ p ∈ insert ((0, 0) : Queen) Q19,
      1 < |((sumDiag m : ℕ) : ℤ) - ((sumDiag p : ℕ) : ℤ)| ∧
        1 < |diffDiag m - diffDiag p| := by
  unfold IsNQueensSol NonAttacking Attacks FitsOn size col row sumDiag diffDiag Q19
  decide +kernel
