-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.conj_rootElt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:08.052623+00:00
-- url     : https://prove2.me/submissions/50a7febf-f2fd-4cc9-95fd-584b22371d3b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_diag_mul_permGL_mul_single
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_single_mul_diag_mul_permGL

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
theorem _root_.solution (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) (i j : Fin n) (a : F) :
    (Iwasawa.diagGL F n t * permGL F w) * rootElt i j a * (Iwasawa.diagGL F n t * permGL F w)⁻¹ =
      rootElt (w i) (w j) ((t (w i) : F) / (t (w j) : F) * a) := by
  by_cases h : i = j
  · subst h
    rw [rootElt_self, rootElt_self, mul_one, mul_inv_cancel]
  have h' : w i ≠ w j := fun e => h (w.injective e)
  rw [mul_inv_eq_iff_eq_mul]
  refine Units.ext ?_
  rw [Units.val_mul (Iwasawa.diagGL F n t * permGL F w) (rootElt i j a),
    Units.val_mul (rootElt (w i) (w j) _) (Iwasawa.diagGL F n t * permGL F w),
    coe_rootElt h, coe_rootElt h', mul_add, add_mul, mul_one, one_mul,
    diag_mul_permGL_mul_single, single_mul_diag_mul_permGL]
  congr 2
  have : (t (w j) : F) ≠ 0 := Units.ne_zero _
  field_simp
end GroundTheory.Automorphic.Whittaker
