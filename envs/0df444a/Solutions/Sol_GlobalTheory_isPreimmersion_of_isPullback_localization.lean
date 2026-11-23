-- Prove2me | solution 1 for GlobalTheory.isPreimmersion_of_isPullback_localization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:08.312335+00:00
-- url     : https://prove2.me/submissions/4b74b175-7a43-436e-968f-8f85af9dcb6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure

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
    (hb : IsPullback b t s (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    IsPreimmersion b :=
  MorphismProperty.of_isPullback (P := @IsPreimmersion) hb.flip (.of_isLocalization M)
end GlobalTheory
