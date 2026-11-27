-- Prove2me | solution 1 for GroundTheory.PAdicHodge.compound_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:51:50.933803+00:00
-- url     : https://prove2.me/submissions/166b239b-4ac0-40f4-997b-f156eedf7c37

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
import Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
import Theorems.Thm_GroundTheory_PAdicHodge_det_mul_eq_sum_minors
import Theorems.Thm_GroundTheory_PAdicHodge_compound_apply

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
theorem _root_.solution {l : ℕ} (P : Matrix (Fin m) (Fin n) R) (Q : Matrix (Fin n) (Fin l) R) :
    compound k (P * Q) = compound k P * compound k Q := by
  ext s u
  rw [compound_apply, mul_apply]
  have : (P * Q).submatrix s.emb u.emb = P.submatrix s.emb id * Q.submatrix id u.emb := by
    ext i j; simp [mul_apply]
  rw [this, det_mul_eq_sum_minors]
  rfl
end GroundTheory.PAdicHodge
