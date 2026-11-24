-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.diagGL_mem_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:44:54.695651+00:00
-- url     : https://prove2.me/submissions/9f609657-c5b8-445c-ba4f-0df67f59c759

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
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
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (d : Fin n → Fˣ) : diagGL F n d ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  have : i ≠ j := fun h => hij (h ▸ rfl)
  simp [diagonal_apply_ne _ this]
end GroundTheory.Automorphic.Parabolic
