-- Prove2me | solution 1 for GoldbachSieve.mem_pairSums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T10:29:51.516262+00:00
-- url     : https://prove2.me/submissions/327d947b-a9a8-4089-97fb-50f145c94242

import Definitions.Def_GoldbachSieve

open GoldbachSieve

theorem solution {P lo hi c n : ℕ} :
    n ∈ pairSums P lo hi c ↔
      ∃ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
        ∃ q ∈ survivors lo hi c, n = p + q := by
  simp only [pairSums, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩
