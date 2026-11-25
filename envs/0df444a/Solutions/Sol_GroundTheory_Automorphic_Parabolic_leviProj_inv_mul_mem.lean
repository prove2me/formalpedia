-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.leviProj_inv_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:30.798026+00:00
-- url     : https://prove2.me/submissions/b4ffa908-b5c6-47db-81c3-576d3b7a6ac3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_leviIncl
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical_iff_leviProj

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
variable (F n β)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (p : blockUpper F n β) :
    ((leviIncl (leviProj F n β p))⁻¹ * p : blockUpper F n β).1 ∈ unipotentRadical F n β := by
  rw [mem_unipotentRadical_iff_leviProj, map_mul, map_inv, leviProj_leviIncl, inv_mul_cancel]
end GroundTheory.Automorphic.Parabolic
