-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigma_diag_mul_permGL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:08.657724+00:00
-- url     : https://prove2.me/submissions/3d5f905d-6607-445c-a91d-adcf0a02cebf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_diag_mul_permGL_apply

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
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n))
    (hw : ∀ b, w (Fin.rev (w b)) = Fin.rev b) (ht : ∀ b, t (w b) = t (Fin.rev b)) :
    sigma (Iwasawa.diagGL F n t * permGL F w) = Iwasawa.diagGL F n t * permGL F w := by
  refine Units.ext ?_
  ext i j
  rw [sigma_apply, diag_mul_permGL_apply, diag_mul_permGL_apply]
  have hiff : Fin.rev j = w (Fin.rev i) ↔ i = w j := by
    constructor
    · intro h
      have := hw (Fin.rev i)
      rw [← h, Fin.rev_rev, Fin.rev_rev] at this
      exact this.symm
    · intro h
      rw [h, hw j]
  by_cases h : i = w j
  · rw [if_pos (hiff.2 h), if_pos h, h, ht j]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
end GroundTheory.Automorphic.Whittaker
