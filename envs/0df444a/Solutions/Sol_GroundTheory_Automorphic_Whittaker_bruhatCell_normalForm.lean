-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.bruhatCell_normalForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:43.437726+00:00
-- url     : https://prove2.me/submissions/43dc7ba3-f39c-45e1-857b-db6f2c4c96b8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_eq_iff
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
theorem _root_.solution {u v : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n)
    (hv : v ∈ Iwasawa.unipotent F n) (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) :
    bruhatCell (u * Iwasawa.diagGL F n t * permGL F w * v) = w :=
  bruhatCell_eq_iff.2 (mem_doubleCoset_iff_normalForm.2 ⟨u, hu, t, v, hv, rfl⟩)
end GroundTheory.Automorphic.Whittaker
