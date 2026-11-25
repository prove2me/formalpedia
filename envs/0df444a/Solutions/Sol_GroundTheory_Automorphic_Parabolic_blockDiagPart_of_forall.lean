-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.blockDiagPart_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:55:31.142311+00:00
-- url     : https://prove2.me/submissions/8c841490-17db-4b33-921f-cf1464e7b901

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
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {A : Matrix (Fin n) (Fin n) F}
    (hA : ∀ i j, β i ≠ β j → A i j = 0) : blockDiagPart F n β A = A := by
  ext i j
  rw [blockDiagPart_apply]
  split_ifs with h
  · rfl
  · exact (hA i j h).symm
end GroundTheory.Automorphic.Parabolic
