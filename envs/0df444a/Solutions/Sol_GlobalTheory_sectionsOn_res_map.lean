-- Prove2me | solution 1 for GlobalTheory.sectionsOn.res_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:09.832388+00:00
-- url     : https://prove2.me/submissions/a6f26832-908d-4e0e-a7a3-d7f3ad9d4a9e

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
open GlobalTheory.sectionsOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable {F G H : X.Modules} {U V W : X.Opens}
namespace GlobalTheory.sectionsOn
theorem _root_.solution (φ : F ⟶ G) (h : V ≤ U) (x : sectionsOn F U) :
    res R G h (map R φ U x) = map R φ V (res R F h x) :=
  (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x).symm
end GlobalTheory.sectionsOn
