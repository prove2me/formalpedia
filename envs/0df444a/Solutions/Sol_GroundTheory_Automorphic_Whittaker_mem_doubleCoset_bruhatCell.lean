-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.mem_doubleCoset_bruhatCell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:34.512463+00:00
-- url     : https://prove2.me/submissions/df9e3360-9f48-4d14-b357-94b44a8bb237

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_doubleCoset_permGL


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
theorem _root_.solution (g : GL (Fin n) F) :
    g ∈ doubleCoset (permGL F (bruhatCell g)) (borel n F) (borel n F) :=
  (exists_mem_doubleCoset_permGL g).choose_spec
end GroundTheory.Automorphic.Whittaker
