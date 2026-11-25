-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_eq_mul_diag_perm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:44:05.203676+00:00
-- url     : https://prove2.me/submissions/474bd963-6234-46a1-9941-08542d326a11

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_normalForm

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
theorem _root_.solution {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)}
    (hg : bruhatCell g = w) :
    ∃ t : Fin n → Fˣ, ∃ a ∈ Iwasawa.unipotent F n, ∃ b ∈ Iwasawa.unipotent F n,
      g = a * (Iwasawa.diagGL F n t * permGL F w) * b := by
  obtain ⟨u, hu, t, v, hv, e⟩ := exists_normalForm g
  rw [hg] at e
  exact ⟨t, u, hu, v, hv, by rw [e]; group⟩
end GroundTheory.Automorphic.Whittaker
