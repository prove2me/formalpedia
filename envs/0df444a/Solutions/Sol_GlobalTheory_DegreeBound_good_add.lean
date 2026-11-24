-- Prove2me | solution 1 for GlobalTheory.DegreeBound.good_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:49.461823+00:00
-- url     : https://prove2.me/submissions/16a625eb-87b6-40a7-95be-77b77e187565

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
theorem _root_.solution {y : Fin D → K} {j : Fin D} {N : ℕ} {b b' : K} (h : Good y j N b)
    (h' : Good y j N b') : Good y j N (b + b') := by
  obtain ⟨C, hC, he⟩ := h
  obtain ⟨C', hC', he'⟩ := h'
  exact ⟨C + C', (totalDegree_add _ _).trans (max_le hC hC'), by rw [add_mul, he, he', map_add]⟩
end GlobalTheory.DegreeBound
