-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.cellMinor_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:47:26.941149+00:00
-- url     : https://prove2.me/submissions/878d57b2-2647-41f8-988a-5004fb221de9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_normalForm
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
theorem _root_.solution {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)} (hg : bruhatCell g = w)
    {a b : GL (Fin n) F} (ha : a ∈ Iwasawa.unipotent F n) (hb : b ∈ Iwasawa.unipotent F n) :
    cellMinor w (a * g * b) = cellMinor w g := by
  obtain ⟨u, hu, t, v, hv, hg'⟩ := exists_normalForm g
  rw [hg] at hg'
  rw [hg', show a * (u * Iwasawa.diagGL F n t * permGL F w * v) * b =
      (a * u) * Iwasawa.diagGL F n t * permGL F w * (v * b) by group,
    cellMinor_normalForm w ((Iwasawa.unipotent F n).mul_mem ha hu)
      ((Iwasawa.unipotent F n).mul_mem hv hb),
    cellMinor_normalForm w hu hv]
end GroundTheory.Automorphic.Whittaker
