-- Prove2me | solution 1 for GlobalTheory.flat_normalization_of_isBezout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:35.852176+00:00
-- url     : https://prove2.me/submissions/41e87b25-4071-460b-bea6-6193bba67854

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
theorem _root_.solution [IsDomain R] [IsBezout R]
    (p : f.normalization ⟶ Spec (.of R)) [Flat (f.toNormalization ≫ p)] : Flat p :=
  flat_of_isSchemeTheoreticallyDominant
    (fun _ _ _ h ↦ Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr h) f.toNormalization p
end GlobalTheory
