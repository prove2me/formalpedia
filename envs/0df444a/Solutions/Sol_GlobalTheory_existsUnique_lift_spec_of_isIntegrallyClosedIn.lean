-- Prove2me | solution 1 for GlobalTheory.existsUnique_lift_spec_of_isIntegrallyClosedIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:54.899041+00:00
-- url     : https://prove2.me/submissions/b49b814c-f2b4-4998-98f5-dd7b984f1d41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_isIso_fromNormalization
import Theorems.Thm_GlobalTheory_isIso_fromNormalization_spec_of_isIntegrallyClosedIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {Z Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution [IsIntegrallyClosedIn R R']
    (p : Z ⟶ Y) [IsIntegralHom p] (a : Spec (.of R') ⟶ Z) (b : Spec (.of R) ⟶ Y)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ b) :
    ∃! c : Spec (.of R) ⟶ Z,
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ c = a ∧ c ≫ p = b := by
  have := isIso_fromNormalization_spec_of_isIntegrallyClosedIn R R'
  exact existsUnique_lift_of_isIso_fromNormalization _ p a b h
end GlobalTheory
