-- Prove2me | solution 1 for GlobalTheory.flat_normalization_of_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:07:23.026356+00:00
-- url     : https://prove2.me/submissions/c18340f8-64a6-4ea7-9872-ff455ff778f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_flat_normalization
import Theorems.Thm_GlobalTheory_flat_of_fractionRing

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
    [IsFractionRing R K] (p : f.normalization ⟶ Spec (.of R)) (c : X ⟶ Spec (.of K))
    (hc : f.toNormalization ≫ p = c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) : Flat p :=
  have : Flat (f.toNormalization ≫ p) := hc ▸ flat_of_fractionRing K c
  flat_normalization f p
end GlobalTheory
