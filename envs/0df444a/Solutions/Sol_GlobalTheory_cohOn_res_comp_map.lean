-- Prove2me | solution 1 for GlobalTheory.cohOn.res_comp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:23.426042+00:00
-- url     : https://prove2.me/submissions/fb6af769-cc9c-46dc-919c-25dfde6ef656

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_cohOn_res_map

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
variable (n)
namespace GlobalTheory.cohOn
theorem _root_.solution (φ : F ⟶ G) (h : V ≤ U) :
    res R G h n ∘ₗ map R φ U n = map R φ V n ∘ₗ res R F h n :=
  LinearMap.ext (res_map R φ h)
end GlobalTheory.cohOn
