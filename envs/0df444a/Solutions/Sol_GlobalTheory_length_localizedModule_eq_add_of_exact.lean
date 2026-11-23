-- Prove2me | solution 1 for GlobalTheory.length_localizedModule_eq_add_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:43.466806+00:00
-- url     : https://prove2.me/submissions/07bee4f0-e35b-4b78-b953-983586adeb84

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
theorem _root_.solution (T : Submonoid S) {N M P : Type*}
    [AddCommGroup N] [AddCommGroup M] [AddCommGroup P] [Module S N] [Module S M] [Module S P]
    (f : N →ₗ[S] M) (g : M →ₗ[S] P) (hf : Function.Injective f) (hg : Function.Surjective g)
    (H : Function.Exact f g) :
    Module.length (Localization T) (LocalizedModule T M) =
      Module.length (Localization T) (LocalizedModule T N) +
        Module.length (Localization T) (LocalizedModule T P) :=
  Module.length_eq_add_of_exact (LocalizedModule.map T f) (LocalizedModule.map T g)
    (LocalizedModule.map_injective T f hf) (LocalizedModule.map_surjective T g hg)
    (LocalizedModule.map_exact T f g H)
end GlobalTheory
