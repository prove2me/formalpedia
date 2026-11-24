-- Prove2me | solution 1 for GlobalTheory.cohOn.zeroEquiv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:30:01.971199+00:00
-- url     : https://prove2.me/submissions/54064430-084e-490a-9224-f242aae16da2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_SiteCoh_zeroEquiv_map


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
variable {F G : X.Modules} {U V : X.Opens}
namespace GlobalTheory.cohOn
theorem _root_.solution (φ : F ⟶ G) (x : cohOn F U 0) :
    zeroEquiv R G U (map R φ U 0 x) = sectionsOn.map R φ U (zeroEquiv R F U x) :=
  SiteCoh.zeroEquiv_map ((toAbSheaf X).map φ) U (toH' F U 0 x)
end GlobalTheory.cohOn
