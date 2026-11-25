-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.diag_mul_permGL_mul_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:06.808809+00:00
-- url     : https://prove2.me/submissions/c4d90015-0733-4a02-b4d7-ee3b40cbec73

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_diag_mul_permGL_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) (i j : Fin n)
    (a : F) :
    ((Iwasawa.diagGL F n t * permGL F w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        Matrix.single i j a = Matrix.single (w i) j ((t (w i) : F) * a) := by
  ext r c
  by_cases hc : c = j
  · subst hc
    rw [Matrix.mul_single_apply_same, diag_mul_permGL_apply, Matrix.single_apply]
    by_cases hr : r = w i
    · subst hr
      simp
    · rw [if_neg hr, if_neg (fun e => hr (e.1.symm)), zero_mul]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc, Matrix.single_apply_of_col_ne _ _ (Ne.symm hc)]
end GroundTheory.Automorphic.Whittaker
