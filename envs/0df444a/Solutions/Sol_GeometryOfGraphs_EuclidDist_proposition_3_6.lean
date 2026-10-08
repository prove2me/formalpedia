-- Prove2me | solution 1 for GeometryOfGraphs.EuclidDist.proposition_3_6
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:54:06.174884+00:00
-- url     : https://prove2.me/submissions/5844d47b-cf5f-46eb-a365-1a95b95ed556

import Mathlib

open Matrix

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (hP : P.IsSymm) :
    P.PosSemidef ↔
      ∀ Y : Matrix X X ℝ, Y.PosSemidef → 0 ≤ ∑ i, ∑ j, P i j * Y i j := by
  constructor
  · intro hp Y hy
    have h := (hp.hadamard hy).dotProduct_mulVec_nonneg (fun _ => 1)
    simpa [dotProduct, mulVec, hadamard] using h
  · intro h
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, ?_⟩
    · exact Matrix.isHermitian_iff_isSymm.mpr hP
    · intro x
      have hx := h (Matrix.vecMulVec x x) (by simpa using Matrix.posSemidef_vecMulVec_self_star x)
      simpa [dotProduct, mulVec, vecMulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hx

#print axioms solution
