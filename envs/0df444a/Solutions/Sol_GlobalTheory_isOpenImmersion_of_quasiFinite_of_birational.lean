-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_of_quasiFinite_of_birational
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:05:00.598846+00:00
-- url     : https://prove2.me/submissions/4f5bebfb-175e-4c24-b8bd-a5bcb6a40891

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Theorems.Thm_GlobalTheory_birational_of_isIso_morphismRestrict
import Theorems.Thm_GlobalTheory_isOpenImmersion_of_quasiFinite_of_isIso_stalkMap

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
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] : IsOpenImmersion f :=
  have ⟨_, _⟩ := birational_of_isIso_morphismRestrict f U hU
  isOpenImmersion_of_quasiFinite_of_isIso_stalkMap f hY
end GlobalTheory
