-- Prove2me | solution 1 for GlobalTheory.DiagonalTimesLowerTriangular.diag_mul_of_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:22:12.176491+00:00
-- url     : https://prove2.me/submissions/b1ca3b36-eb4b-41cf-a37d-4f5a1e366953

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiagMulOfLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiagonalTimesLowerTriangular
namespace GlobalTheory.DiagonalTimesLowerTriangular
theorem _root_.solution {K : Type} [CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}
    (ha : ∀ (i j : Fin s), i < j → a i j = (0 : K))
    (hb : ∀ (i j : Fin s), i < j → b i j = (0 : K)) :
    ∀ (i : Fin s), (a * b) i i = a i i * b i i := by
  intro i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hb k i h, mul_zero]
    · rw [ha i k h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h
end GlobalTheory.DiagonalTimesLowerTriangular
