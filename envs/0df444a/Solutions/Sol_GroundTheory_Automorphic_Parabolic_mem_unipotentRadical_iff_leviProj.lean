-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_unipotentRadical_iff_leviProj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:08.935503+00:00
-- url     : https://prove2.me/submissions/12cca755-be4d-440a-979b-56e82d20cf62

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups

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
theorem _root_.solution {p : blockUpper F n β} :
    (p : GL (Fin n) F) ∈ unipotentRadical F n β ↔ leviProj F n β p = 1 := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    rw [← (Subtype.ext hqp : q = p)]
    exact hq
  · intro h
    exact ⟨p, h, rfl⟩
end GroundTheory.Automorphic.Parabolic
