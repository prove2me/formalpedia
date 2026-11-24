-- Prove2me | solution 1 for GlobalTheory.DegreeBound.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:52.647802+00:00
-- url     : https://prove2.me/submissions/e294db87-00f8-431f-be8e-531a93d0a879

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
theorem _root_.solution {y : Fin D → K} {j : Fin D} {N N' : ℕ} {b b' : K} (h : Good y j N b)
    (h' : Good y j N' b') : Good y j (N + N') (b * b') := by
  obtain ⟨C, hC, he⟩ := h
  obtain ⟨C', hC', he'⟩ := h'
  refine ⟨C * C', (totalDegree_mul _ _).trans (add_le_add hC hC'), ?_⟩
  rw [map_mul, ← he, ← he', pow_add]; ring
end GlobalTheory.DegreeBound
