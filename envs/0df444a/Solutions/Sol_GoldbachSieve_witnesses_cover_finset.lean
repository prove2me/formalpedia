-- Prove2me | solution 1 for GoldbachSieve.witnesses_cover_finset
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T13:48:25.072215+00:00
-- url     : https://prove2.me/submissions/024dcbf6-62e4-42d7-94ea-3402470b3cdd

import Definitions.Def_GoldbachSieve

theorem solution (A : Finset ℕ) (smallBound lo hi cutoff : ℕ)
    (hw : ∀ n ∈ A,
      ∃ p ∈ ((Finset.Icc 2 smallBound).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors lo hi cutoff, n = p + q) :
    A ⊆ GoldbachSieve.pairSums smallBound lo hi cutoff := by
  intro n hn
  obtain ⟨p, hp, q, hq, hsum⟩ := hw n hn
  unfold GoldbachSieve.pairSums
  rw [Finset.mem_biUnion]
  refine ⟨p, hp, ?_⟩
  rw [Finset.mem_image]
  exact ⟨q, hq, hsum.symm⟩
