-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.leviProj_leviIncl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:23.306798+00:00
-- url     : https://prove2.me/submissions/ca57e6e2-df16-499c-9e9d-4c951212905e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_of_mem_levi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (m : levi F n β) : leviProj F n β (leviIncl m) = m :=
  leviProj_of_mem_levi m.2
end GroundTheory.Automorphic.Parabolic
