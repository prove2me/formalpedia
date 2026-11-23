-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.leviProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:40.285417+00:00
-- url     : https://prove2.me/submissions/bf987b27-ec49-46bc-8a0d-155361032c22

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
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (p : blockUpper F n β) (i j : Fin n) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) i j =
      if β i = β j then (p : GL (Fin n) F) i j else 0 := rfl
end GroundTheory.Automorphic.Parabolic
