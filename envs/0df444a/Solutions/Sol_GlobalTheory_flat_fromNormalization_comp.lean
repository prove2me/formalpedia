-- Prove2me | solution 1 for GlobalTheory.flat_fromNormalization_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:18:09.236704+00:00
-- url     : https://prove2.me/submissions/d4f5db36-cf53-4e76-b5c9-72d0c32a6106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_flat_normalization_of_fractionRing

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [IsDedekindDomain R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (s : Y ⟶ Spec (.of R)) (c : X ⟶ Spec (.of K))
    (hc : f ≫ s = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    Flat (f.fromNormalization ≫ s) :=
  flat_normalization_of_fractionRing f K _ c (by simpa using hc)
end GlobalTheory
