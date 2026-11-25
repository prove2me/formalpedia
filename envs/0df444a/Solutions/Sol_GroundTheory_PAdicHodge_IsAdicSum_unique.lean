-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsAdicSum.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:08:26.000188+00:00
-- url     : https://prove2.me/submissions/6cb464a3-c0a5-46a7-81cc-e535676ea50a

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog

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
open _root_.WittVector
variable {R : Type*} [CommRing R] (I : Ideal R)
variable {I}
namespace GroundTheory.PAdicHodge
namespace IsAdicSum
theorem _root_.solution [IsHausdorff I R] {a : ℕ → R} {s s' : R} (hs : IsAdicSum I a s)
    (hs' : IsAdicSum I a s') : s = s' := by
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I)
  intro k
  obtain ⟨N, hN⟩ := hs k
  obtain ⟨N', hN'⟩ := hs' k
  have h := sub_mem (hN (max N N') (le_max_left _ _)) (hN' (max N N') (le_max_right _ _))
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  convert h using 1
  ring
end IsAdicSum
end GroundTheory.PAdicHodge
