-- Prove2me | solution 1 for GlobalTheory.cohOn.zeroEquiv_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:43.994154+00:00
-- url     : https://prove2.me/submissions/2b4446ce-92e6-4451-98de-3e60ff61d3d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_SiteCoh_zeroEquiv_res


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
theorem _root_.solution (h : V ≤ U) (x : cohOn F U 0) :
    zeroEquiv R F V (res R F h 0 x) = sectionsOn.res R F h (zeroEquiv R F U x) :=
  SiteCoh.zeroEquiv_res ((toAbSheaf X).obj F) (homOfLE h) (toH' F U 0 x)
end GlobalTheory.cohOn
