-- Prove2me | solution 1 for GlobalTheory.locCubeMap_app_toLocCube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:19.906792+00:00
-- url     : https://prove2.me/submissions/24e58f08-7ad0-42b7-aa47-297fec6cdfbb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v u
open GlobalTheory
variable {ι : Type} {R : Type u} [CommRing R]
variable (f : ι → R) (M : Type v) [AddCommGroup M] [Module R M]
variable {M}
namespace GlobalTheory
theorem _root_.solution {N : Type v} [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N)
    (s : Finset ι) (m : M) :
    ((locCubeMap f φ).app s).hom (toLocCube f M s m) = toLocCube f N s (φ m) :=
  IsLocalizedModule.map_apply _ _ _ φ m
end GlobalTheory
