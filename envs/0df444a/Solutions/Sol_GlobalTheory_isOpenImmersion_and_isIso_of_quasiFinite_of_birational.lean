-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_and_isIso_of_quasiFinite_of_birational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:44.59909+00:00
-- url     : https://prove2.me/submissions/41799177-ce5f-4455-8dc0-1527b97f51cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_quasiFinite_of_birational
import Theorems.Thm_GlobalTheory_isIso_of_isFinite_of_birational
import Theorems.Thm_GlobalTheory_isIso_of_isProper_of_quasiFinite_of_birational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
open GlobalTheory
universe u
variable {X Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (f : X ⟶ Y) [IsSeparated f]
    [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] :
    IsOpenImmersion f ∧ (IsFinite f → IsIso f) ∧ (IsProper f → IsIso f) :=
  ⟨isOpenImmersion_of_quasiFinite_of_birational f hY U hU,
    fun _ ↦ isIso_of_isFinite_of_birational f hY U hU,
    fun _ ↦ isIso_of_isProper_of_quasiFinite_of_birational f hY U hU⟩
end GlobalTheory
