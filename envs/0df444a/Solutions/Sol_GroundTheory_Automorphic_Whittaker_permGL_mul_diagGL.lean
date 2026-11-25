-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.permGL_mul_diagGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:43.945676+00:00
-- url     : https://prove2.me/submissions/28c3824c-e800-4080-a25c-0b480cf5453c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_permGL_apply
import Theorems.Thm_GroundTheory_Automorphic_permGL_mul_apply


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
theorem _root_.solution (w : Equiv.Perm (Fin n)) (d : Fin n → Fˣ) :
    permGL F w * Iwasawa.diagGL F n d = Iwasawa.diagGL F n (fun r => d (w⁻¹ r)) * permGL F w := by
  ext r c
  rw [Units.val_mul, Units.val_mul, Iwasawa.coe_diagGL, Iwasawa.coe_diagGL, permGL_mul_apply,
    diagonal_apply, diagonal_mul, permGL_apply]
  by_cases h : r = w c
  · have : w⁻¹ r = c := Equiv.Perm.inv_eq_iff_eq.2 h
    rw [if_pos this, if_pos h, mul_one]
  · have : w⁻¹ r ≠ c := fun e => h (Equiv.Perm.inv_eq_iff_eq.1 e)
    rw [if_neg this, if_neg h, mul_zero]
end GroundTheory.Automorphic.Whittaker
