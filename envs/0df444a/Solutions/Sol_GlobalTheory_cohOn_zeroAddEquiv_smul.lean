-- Prove2me | solution 1 for GlobalTheory.cohOn.zeroAddEquiv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:41.544001+00:00
-- url     : https://prove2.me/submissions/6c3cc279-43ba-41de-8e18-942193011d56

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
variable {F G : X.Modules} {U V : X.Opens}
namespace GlobalTheory.cohOn
theorem _root_.solution (r : R) (x : cohOn F U 0) :
    zeroAddEquiv F U (r • x) = restrictGlobal X U (algebraMap R Γ(X, ⊤) r) • zeroAddEquiv F U x :=
  congrArg (sectionsOn.toΓ F U) ((zeroEquiv R F U).map_smul r x)
end GlobalTheory.cohOn
