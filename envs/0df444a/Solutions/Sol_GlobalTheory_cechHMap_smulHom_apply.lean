-- Prove2me | solution 1 for GlobalTheory.cechHMap_smulHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:15.557811+00:00
-- url     : https://prove2.me/submissions/85b76786-43ad-4f37-9994-c8dd578be3d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
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
namespace GlobalTheory
theorem _root_.solution (r : R) (n : ℕ) (x : cechH R F V U n) :
    (cechHMap R V U (smulHom F (algebraMap R Γ(X, ⊤) r)) n).hom x = r • x := by
  obtain ⟨x, rfl⟩ := cechClass_surjective (cechCube R F V U) n x
  exact (homologyMap_cechClass (cechCubeMap R V U _) n x (r • x) rfl).trans
    (map_smul (cechClass (cechCube R F V U) n) r x)
end GlobalTheory
