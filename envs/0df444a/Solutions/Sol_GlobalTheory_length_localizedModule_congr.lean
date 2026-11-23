-- Prove2me | solution 1 for GlobalTheory.length_localizedModule_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:06.508649+00:00
-- url     : https://prove2.me/submissions/89728c5e-8f95-4f48-aa0c-c94264ea1a60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {S : Type*} [CommRing S]
namespace GlobalTheory
theorem _root_.solution (T : Submonoid S) {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N] (e : M ≃ₗ[S] N) :
    Module.length (Localization T) (LocalizedModule T M) =
      Module.length (Localization T) (LocalizedModule T N) :=
  (IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T N) (Localization T) e).length_eq
end GlobalTheory
