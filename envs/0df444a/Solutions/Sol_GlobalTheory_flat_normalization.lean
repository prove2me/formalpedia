-- Prove2me | solution 1 for GlobalTheory.flat_normalization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:57:45.387968+00:00
-- url     : https://prove2.me/submissions/0886f3e5-0722-4cad-8875-029de0252fb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Theorems.Thm_GlobalTheory_flat_of_isSchemeTheoreticallyDominant

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
theorem _root_.solution [IsDedekindDomain R] (p : f.normalization ⟶ Spec (.of R))
    [Flat (f.toNormalization ≫ p)] : Flat p :=
  flat_of_isSchemeTheoreticallyDominant
    (fun _ _ _ h ↦ IsDedekindDomain.flat_iff_torsion_eq_bot.mpr h) f.toNormalization p
end GlobalTheory
