-- Prove2me | solution 1 for GlobalTheory.cohOn.moduleOfRingHom_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:18.313797+00:00
-- url     : https://prove2.me/submissions/66bce953-9cfb-462e-88df-df6e37e004ce

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
namespace GlobalTheory.cohOn
theorem _root_.solution {R : Type v} [CommRing R] (f : R →+* Γ(X, ⊤)) {F : X.Modules}
    {U : X.Opens} {n : ℕ} (r : R) (x : cohOn F U n) :
    letI := moduleOfRingHom f F U n
    r • x = f r • x := rfl
end GlobalTheory.cohOn
