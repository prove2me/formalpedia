-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.single_mul_diag_mul_permGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:11.278354+00:00
-- url     : https://prove2.me/submissions/21af82e7-b1e9-4479-a4f5-5f94e5200dae

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
theorem _root_.solution (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) (k j : Fin n)
    (b : F) :
    Matrix.single k (w j) b *
        ((Iwasawa.diagGL F n t * permGL F w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.single k j (b * (t (w j) : F)) := by
  ext r c
  by_cases hr : r = k
  · subst hr
    rw [Matrix.single_mul_apply_same, diag_mul_permGL_apply, Matrix.single_apply]
    by_cases hc : c = j
    · subst hc
      simp
    · rw [if_neg (fun e => hc (w.injective e).symm), if_neg (fun e => hc e.2.symm), mul_zero]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hr, Matrix.single_apply_of_row_ne (Ne.symm hr)]
end GroundTheory.Automorphic.Whittaker
