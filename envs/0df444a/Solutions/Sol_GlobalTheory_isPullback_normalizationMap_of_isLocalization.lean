-- Prove2me | solution 1 for GlobalTheory.isPullback_normalizationMap_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:03.670538+00:00
-- url     : https://prove2.me/submissions/288fc5a2-80cd-4a50-9f21-6db661d1e921

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
    (hb : IsPullback b t s (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    {X X' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {a : X' ⟶ X} [QuasiCompact f]
    [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f'] (h : IsPullback a f' f b) :
    IsPullback (normalizationMap f' f a b h.w) f'.fromNormalization f.fromNormalization b :=
  have := PreservesNormalization.of_isPullback_localization M hb
  isPullback_normalizationMap h
end GlobalTheory
