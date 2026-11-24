-- Prove2me | solution 1 for GlobalTheory.isPullback_toNormalization_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:47.268921+00:00
-- url     : https://prove2.me/submissions/d0ba797f-ec39-4a78-8a06-d209ef372baf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_isPullback_toNormalization_of_mono
import Theorems.Thm_GlobalTheory_isPreimmersion_of_isPullback_localization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] PreservesNormalization.isIso_normalizationPullback
variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (M : Submonoid R)
  [IsLocalization M R'] {Y Y' : Scheme.{u}} {b : Y' ⟶ Y} {t : Y' ⟶ Spec (.of R')}
  {s : Y ⟶ Spec (.of R)}
include M
namespace GlobalTheory
theorem _root_.solution
    (hb : IsPullback b t s (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    {X V : Scheme.{u}} (f' : X ⟶ V) [IsIntegralHom f'] (i : V ⟶ Y') [IsOpenImmersion i]
    (f : X ⟶ Y) (H : f = f' ≫ i ≫ b) [QuasiCompact f] [QuasiSeparated f] :
    IsPullback f.toNormalization f' f.fromNormalization (i ≫ b) :=
  have := PreservesNormalization.of_isPullback_localization M hb
  have := isPreimmersion_of_isPullback_localization M hb
  isPullback_toNormalization_of_mono f' (i ≫ b) f H
end GlobalTheory
