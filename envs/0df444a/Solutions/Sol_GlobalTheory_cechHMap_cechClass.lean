-- Prove2me | solution 1 for GlobalTheory.cechHMap_cechClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:36:22.299874+00:00
-- url     : https://prove2.me/submissions/537c457e-99c9-4a02-995c-a393207f4964

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Theorems.Thm_GlobalTheory_Cube_termMap_mem_ker
import Theorems.Thm_GlobalTheory_homologyMap_cechClass


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe t v u
noncomputable section
open GlobalTheory
variable {X Y : Scheme.{u}} {ι : Type}
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable (F : X.Modules) {G H : X.Modules} (V : X.Opens) (U : ι → X.Opens)
variable [LinearOrder ι]
variable {F}
namespace GlobalTheory
theorem _root_.solution (φ : F ⟶ G) (n : ℕ)
    (x : LinearMap.ker (Cube.d (cechCube R F V U) (n + 1))) :
    (cechHMap R V U φ n).hom (cechClass (cechCube R F V U) n x) =
      cechClass (cechCube R G V U) n ⟨_, Cube.termMap_mem_ker (cechCubeMap R V U φ) x.2⟩ :=
  homologyMap_cechClass (cechCubeMap R V U φ) n x _ rfl
end GlobalTheory
