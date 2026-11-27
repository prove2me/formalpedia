-- Prove2me | solution 1 for GlobalTheory.isOpenImmersion_lift_toNormalization_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:46.904808+00:00
-- url     : https://prove2.me/submissions/0ba737cb-aa79-4a5e-aa73-751e846d8906

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_isOpenImmersion_lift_toNormalization_of_mono
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
    {X : Scheme.{u}} (f' : X ⟶ Y') [QuasiCompact f'] [LocallyQuasiFinite f']
    [LocallyOfFiniteType f'] [IsSeparated f'] (f : X ⟶ Y) (H : f = f' ≫ b) [QuasiCompact f]
    [QuasiSeparated f] :
    IsOpenImmersion (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) ∧
      IsSchemeTheoreticallyDominant (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) ∧
      IsDominant (pullback.lift f.toNormalization f' (by simp [H]) :
        X ⟶ pullback f.fromNormalization b) :=
  have := PreservesNormalization.of_isPullback_localization M hb
  have := isPreimmersion_of_isPullback_localization M hb
  isOpenImmersion_lift_toNormalization_of_mono f' b f H
end GlobalTheory
