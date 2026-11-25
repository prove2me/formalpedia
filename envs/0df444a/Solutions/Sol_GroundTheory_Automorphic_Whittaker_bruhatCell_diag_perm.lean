-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.bruhatCell_diag_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:46.385654+00:00
-- url     : https://prove2.me/submissions/ca4cc815-4007-43a7-8a5b-95663f5fbbc9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_normalForm

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
theorem _root_.solution (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) :
    bruhatCell (Iwasawa.diagGL F n t * permGL F w) = w := by
  have := bruhatCell_normalForm (Iwasawa.unipotent F n).one_mem (Iwasawa.unipotent F n).one_mem t w
  rwa [one_mul, mul_one] at this
end GroundTheory.Automorphic.Whittaker
