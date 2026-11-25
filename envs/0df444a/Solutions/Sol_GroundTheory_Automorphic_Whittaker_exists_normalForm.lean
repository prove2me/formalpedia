-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:29:25.787046+00:00
-- url     : https://prove2.me/submissions/a86f770c-f68b-4aac-a0ce-e14a46881f5c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_doubleCoset_bruhatCell
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_doubleCoset_iff_normalForm

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
    ∃ u ∈ Iwasawa.unipotent F n, ∃ t : Fin n → Fˣ, ∃ v ∈ Iwasawa.unipotent F n,
      g = u * Iwasawa.diagGL F n t * permGL F (bruhatCell g) * v :=
  mem_doubleCoset_iff_normalForm.1 (mem_doubleCoset_bruhatCell g)
end GroundTheory.Automorphic.Whittaker
