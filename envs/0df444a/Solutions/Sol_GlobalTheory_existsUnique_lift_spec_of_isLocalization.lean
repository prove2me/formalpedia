-- Prove2me | solution 1 for GlobalTheory.existsUnique_lift_spec_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:22:31.514504+00:00
-- url     : https://prove2.me/submissions/38d668c2-2a52-437e-ac6d-f0761329cc66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
import Theorems.Thm_GlobalTheory_isIntegrallyClosedIn_of_isLocalization
import Theorems.Thm_GlobalTheory_existsUnique_lift_spec_of_isIntegrallyClosedIn

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
theorem _root_.solution [IsIntegrallyClosed R] (M : Submonoid R)
    (hM : M ≤ nonZeroDivisors R) [IsLocalization M R']
    (p : Z ⟶ Y) [IsIntegralHom p] (a : Spec (.of R') ⟶ Z) (b : Spec (.of R) ⟶ Y)
    (h : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ b) :
    ∃! c : Spec (.of R) ⟶ Z,
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ c = a ∧ c ≫ p = b := by
  have := isIntegrallyClosedIn_of_isLocalization M hM R'
  exact existsUnique_lift_spec_of_isIntegrallyClosedIn p a b h
end GlobalTheory
