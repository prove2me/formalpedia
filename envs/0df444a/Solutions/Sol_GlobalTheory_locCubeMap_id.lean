-- Prove2me | solution 1 for GlobalTheory.locCubeMap_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:34.519251+00:00
-- url     : https://prove2.me/submissions/724f212a-a44e-4cd1-95bb-9c8e8d87b628

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube

set_option autoImplicit false
open CategoryTheory Limits
universe v u
open GlobalTheory
variable {ι : Type} {R : Type u} [CommRing R]
variable (f : ι → R) (M : Type v) [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution : locCubeMap f (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  refine NatTrans.ext (funext fun s => ModuleCat.hom_ext ?_)
  exact IsLocalizedModule.map_id _ (toLocCube f M s)
end GlobalTheory
