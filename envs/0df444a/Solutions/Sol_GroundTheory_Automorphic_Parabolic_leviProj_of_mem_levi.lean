-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.leviProj_of_mem_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:50.031422+00:00
-- url     : https://prove2.me/submissions/12e54d58-7fc6-42f5-b128-e77a6c6fc678

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockDiagPart_of_forall

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
theorem _root_.solution {m : GL (Fin n) F} (hm : m ∈ levi F n β) :
    leviProj F n β ⟨m, levi_le_blockUpper hm⟩ = ⟨m, hm⟩ :=
  Subtype.ext (Units.ext (blockDiagPart_of_forall (mem_levi.1 hm)))
end GroundTheory.Automorphic.Parabolic
