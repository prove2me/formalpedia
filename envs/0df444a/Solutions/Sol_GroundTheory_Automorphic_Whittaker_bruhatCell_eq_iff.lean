-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.bruhatCell_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:01.126379+00:00
-- url     : https://prove2.me/submissions/9e709e2d-3987-42b5-b978-b56a7d032cad

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_doubleCoset_bruhatCell
import Theorems.Thm_GroundTheory_Automorphic_doubleCoset_permGL_injective


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
theorem _root_.solution {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)} :
    bruhatCell g = w ↔ g ∈ doubleCoset (permGL F w) (borel n F) (borel n F) := by
  constructor
  · rintro rfl
    exact mem_doubleCoset_bruhatCell g
  · intro h
    exact doubleCoset_permGL_injective (mem_doubleCoset_bruhatCell g) h
end GroundTheory.Automorphic.Whittaker
