-- Prove2me | solution 1 for GroundTheory.PAdicHodge.maxMinor_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:37.085115+00:00
-- url     : https://prove2.me/submissions/204ac8ba-f31a-45ea-b1a0-cef4d3a2aef0

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
variable {m n k : ℕ}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (P : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset m k) :
    maxMinor (P * B) s = ∑ t : KSubset n k, compound k P s t * maxMinor B t := by
  unfold maxMinor
  have : (P * B).submatrix s.emb id = P.submatrix s.emb id * B := by
    ext i j; simp [mul_apply]
  rw [this, det_mul_eq_sum_minors]
  rfl
end GroundTheory.PAdicHodge
