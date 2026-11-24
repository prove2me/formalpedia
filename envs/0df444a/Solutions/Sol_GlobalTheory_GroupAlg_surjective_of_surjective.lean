-- Prove2me | solution 1 for GlobalTheory.GroupAlg.surjective_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:06:32.330878+00:00
-- url     : https://prove2.me/submissions/39a3f66c-86c7-414a-94da-903c2311289e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.GroupAlg
variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)
namespace GlobalTheory.GroupAlg
theorem _root_.solution (hu : Function.Surjective u) :
    Function.Surjective (mapDomainRingHom R u) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    obtain ⟨y, rfl⟩ := hu x
    exact ⟨single y r, mapDomain_single⟩
end GlobalTheory.GroupAlg
