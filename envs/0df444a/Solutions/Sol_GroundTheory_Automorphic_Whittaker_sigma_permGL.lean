-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.sigma_permGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:10.554939+00:00
-- url     : https://prove2.me/submissions/d620d429-83e8-4f8e-8ea7-64add27333e9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_permGL_apply
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
theorem _root_.solution (w : Equiv.Perm (Fin n)) :
    sigma (permGL F w) = permGL F (Fin.revPerm * w⁻¹ * Fin.revPerm) := by
  refine Units.ext ?_
  ext i j
  rw [sigma_apply, permGL_apply, permGL_apply]
  simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply]
  have hiff : Fin.rev j = w (Fin.rev i) ↔ i = Fin.rev (w⁻¹ (Fin.rev j)) := by
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  by_cases h : Fin.rev j = w (Fin.rev i)
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]
end GroundTheory.Automorphic.Whittaker
