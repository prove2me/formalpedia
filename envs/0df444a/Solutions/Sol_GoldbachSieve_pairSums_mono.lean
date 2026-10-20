-- Prove2me | solution 1 for GoldbachSieve.pairSums_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T17:39:51.431853+00:00
-- url     : https://prove2.me/submissions/b15a4973-bd3c-4e78-af46-0e3cd72446df

import Definitions.Def_GoldbachSieve
import Theorems.Thm_GoldbachSieve_mem_survivors
import Theorems.Thm_GoldbachSieve_mem_pairSums

open GoldbachSieve

theorem solution {P P' lo lo' hi hi' c : ℕ} (hP : P ≤ P') (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    GoldbachSieve.pairSums P lo hi c ⊆ GoldbachSieve.pairSums P' lo' hi' c := by
  intro n hn
  rw [GoldbachSieve.mem_pairSums] at hn ⊢
  obtain ⟨p, hp, q, hq, he⟩ := hn
  refine ⟨p, ?_, q, ?_, he⟩
  · obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp2, hpP⟩ := Finset.mem_Icc.mp hpI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp2, le_trans hpP hP⟩, hpp⟩
  · rw [GoldbachSieve.mem_survivors] at hq ⊢
    exact ⟨by omega, by omega, hq.2.2⟩
