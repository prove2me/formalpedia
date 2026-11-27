-- Prove2me | solution 1 for GlobalTheory.cohOn.map_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:36:57.687262+00:00
-- url     : https://prove2.me/submissions/aeaf593f-3fb7-4465-b5bb-99c9939b9c66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable {F G H : X.Modules} {U V W : X.Opens} {n : ℕ}
namespace GlobalTheory.cohOn
theorem _root_.solution (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] (φ : F ⟶ G) (x : cohOn F U n) :
    map R φ U n x = map S φ U n x := rfl
end GlobalTheory.cohOn
