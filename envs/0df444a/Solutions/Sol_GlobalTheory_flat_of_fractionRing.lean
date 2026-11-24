-- Prove2me | solution 1 for GlobalTheory.flat_of_fractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:47.327625+00:00
-- url     : https://prove2.me/submissions/5142836b-6bf7-4b34-97fc-3b33b2c52f4f

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (c : X ⟶ Spec (.of K)) : Flat (c ≫ Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  inferInstance
end GlobalTheory
