-- Prove2me | solution 1 for GlobalTheory.cohOn.res_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:32:57.052803+00:00
-- url     : https://prove2.me/submissions/f0dba2b7-b22c-4624-8a6b-3121a123c8cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Theorems.Thm_GlobalTheory_SiteCoh_res_map_apply


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
theorem _root_.solution (φ : F ⟶ G) (h : V ≤ U) (x : cohOn F U n) :
    res R G h n (map R φ U n x) = map R φ V n (res R F h n x) := by
  apply (toH' G V n).injective
  rw [toH'_res, toH'_map, toH'_map, toH'_res, SiteCoh.res_map_apply]
end GlobalTheory.cohOn
