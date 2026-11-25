-- Prove2me | solution 1 for GroundTheory.PAdicHodge.ACris.natDegree_one_add_X_pow_sub_one_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:36.109839+00:00
-- url     : https://prove2.me/submissions/948be42e-7aba-49d1-abc5-92ff69fb1c60

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable (q : ℕ)
namespace GroundTheory.PAdicHodge.ACris
theorem _root_.solution (N : ℕ) :
    ((((1 : ℤ[X]) + X) ^ q - 1) ^ N).natDegree ≤ q * N := by
  refine (natDegree_pow_le).trans ?_
  rw [mul_comm q N]
  refine Nat.mul_le_mul_left N ?_
  refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
  refine (natDegree_pow_le).trans ?_
  have : ((1 : ℤ[X]) + X).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
  nlinarith
end GroundTheory.PAdicHodge.ACris
