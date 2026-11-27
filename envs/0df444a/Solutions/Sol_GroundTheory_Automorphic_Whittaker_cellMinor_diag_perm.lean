-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.cellMinor_diag_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:18.57674+00:00
-- url     : https://prove2.me/submissions/8b3cd558-45eb-4f5c-b8de-3f40aa947628

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_cellMinor_normalForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (w : Equiv.Perm (Fin n)) (t : Fin n → Fˣ) :
    cellMinor w (Iwasawa.diagGL F n t * permGL F w) =
      fun k => ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) := by
  have := cellMinor_normalForm w (Iwasawa.unipotent F n).one_mem (Iwasawa.unipotent F n).one_mem t
  rwa [one_mul, mul_one] at this
end GroundTheory.Automorphic.Whittaker
