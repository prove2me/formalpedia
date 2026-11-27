-- Prove2me | solution 1 for GlobalTheory.existsUnique_lift_normalization_spec_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:37:58.798194+00:00
-- url     : https://prove2.me/submissions/6a952972-803d-4d82-984a-677914f1b82f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
import Theorems.Thm_GlobalTheory_existsUnique_lift_spec_of_isLocalization

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
namespace GlobalTheory
theorem _root_.solution [IsIntegrallyClosed R]
    (M : Submonoid R) (hM : M ≤ nonZeroDivisors R) [IsLocalization M R']
    (χ₀ : Spec (.of R) ⟶ Y) (χ₁ : Spec (.of R') ⟶ X)
    (h : χ₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ χ₀) :
    ∃! χ : Spec (.of R) ⟶ f.normalization,
      Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ χ = χ₁ ≫ f.toNormalization ∧
        χ ≫ f.fromNormalization = χ₀ :=
  existsUnique_lift_spec_of_isLocalization M hM f.fromNormalization (χ₁ ≫ f.toNormalization) χ₀
    (by rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, h])
end GlobalTheory
