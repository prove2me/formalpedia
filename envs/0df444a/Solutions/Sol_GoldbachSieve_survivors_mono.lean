-- Prove2me | solution 1 for GoldbachSieve.survivors_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T17:39:50.148318+00:00
-- url     : https://prove2.me/submissions/d01eb292-4159-48af-8f24-3261e171f1cd

import Definitions.Def_GoldbachSieve
import Theorems.Thm_GoldbachSieve_mem_survivors

open GoldbachSieve

theorem solution {lo lo' hi hi' c : ℕ} (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
    GoldbachSieve.survivors lo hi c ⊆ GoldbachSieve.survivors lo' hi' c := by
  intro q hq
  rw [GoldbachSieve.mem_survivors] at hq ⊢
  exact ⟨by omega, by omega, hq.2.2⟩
