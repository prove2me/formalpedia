-- Prove2me | solution 1 for GroundTheory.PAdicHodge.det_mul_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:50:55.115556+00:00
-- url     : https://prove2.me/submissions/d737b09d-2768-478a-8556-fb41d1c23ba2

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
import Theorems.Thm_GroundTheory_PAdicHodge_det_mul_eq_sum_minors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Matrix Finset Equiv
variable {R : Type*} [CommRing R]
variable {k n : ℕ}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R)
    (h : n < k) : (A * B).det = 0 := by
  rw [det_mul_eq_sum_minors]
  refine Finset.sum_eq_zero fun s _ => ?_
  exfalso
  have := s.1.card_le_univ
  rw [Fintype.card_fin, s.2] at this
  omega
end GroundTheory.PAdicHodge
