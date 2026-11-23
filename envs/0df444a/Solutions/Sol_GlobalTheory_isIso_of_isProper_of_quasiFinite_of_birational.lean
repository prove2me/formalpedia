-- Prove2me | solution 1 for GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:18.614465+00:00
-- url     : https://prove2.me/submissions/8a168b0e-24ed-4a2e-b965-e654bd17fe65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Theorems.Thm_GlobalTheory_birational_of_isIso_morphismRestrict
import Theorems.Thm_GlobalTheory_isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
variable {X Y : Scheme.{u}}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (f : X ⟶ Y) [IsProper f]
    [LocallyQuasiFinite f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : Nonempty U) [IsIso (f ∣_ U)] : IsIso f := by
  obtain ⟨hd, hs⟩ := _root_.GlobalTheory.birational_of_isIso_morphismRestrict f U hU
  exact _root_.GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap f hY
end _root_.GlobalTheory
end GlobalTheory
