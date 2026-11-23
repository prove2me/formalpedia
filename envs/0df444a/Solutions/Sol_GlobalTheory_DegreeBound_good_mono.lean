-- Prove2me | solution 1 for GlobalTheory.DegreeBound.good_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:27.270177+00:00
-- url     : https://prove2.me/submissions/8164df60-86d7-4d6d-9dea-9ec4cf746374

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeLeOfIntegralAtInfinity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.DegreeBound
variable {K : Type} [Field K] {D : ℕ}
namespace GlobalTheory.DegreeBound
theorem _root_.solution {y : Fin D → K} {j : Fin D} {N : ℕ} {b : K} (h : Good y j N b) (M : ℕ) :
    Good y j (N + M) b := by
  obtain ⟨C, hC, he⟩ := h
  refine ⟨C * X j ^ M, (totalDegree_mul _ _).trans (by rw [totalDegree_X_pow]; omega), ?_⟩
  rw [pow_add, ← mul_assoc, he, map_mul, map_pow, aeval_X]
end GlobalTheory.DegreeBound
