-- Prove2me | solution 1 for GlobalTheory.cohOn.res_eq_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:27.097253+00:00
-- url     : https://prove2.me/submissions/9b2e7a2a-3bf8-41ab-bd85-448cacea72d9

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
theorem _root_.solution (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] (h : V ≤ U) (x : cohOn F U n) :
    res R F h n x = res S F h n x := rfl
end GlobalTheory.cohOn
