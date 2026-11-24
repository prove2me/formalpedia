-- Prove2me | solution 1 for GlobalTheory.LatticeIndicator.forall_mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:15:22.667838+00:00
-- url     : https://prove2.me/submissions/10c09a31-0ece-441c-9324-733ee4da86ae

import Mathlib


theorem solution {O K m n : Type*} [CommRing O] [CommRing K] [Algebra O K]
    (x : Matrix m n K) :
    (∀ i j, x i j ∈ (algebraMap O K).range) ↔
      ∃ y : Matrix m n O, y.map (algebraMap O K) = x := by
  constructor
  · intro h; choose y hy using h; exact ⟨Matrix.of y, Matrix.ext fun i j => hy i j⟩
  · rintro ⟨y,rfl⟩ i j; exact ⟨y i j,rfl⟩
