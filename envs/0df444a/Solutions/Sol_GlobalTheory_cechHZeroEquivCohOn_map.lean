-- Prove2me | solution 1 for GlobalTheory.cechHZeroEquivCohOn_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:36:42.230544+00:00
-- url     : https://prove2.me/submissions/7f845d8f-de26-480a-b73a-b0c1581a3f9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Theorems.Thm_GlobalTheory_cechHZeroEquiv_map
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
import Theorems.Thm_GlobalTheory_SiteCoh_zeroEquiv_map
import Theorems.Thm_GlobalTheory_cechAbCubeMap_app_apply
import Theorems.Thm_GlobalTheory_cechAbHMap_id
import Theorems.Thm_GlobalTheory_cechAbHZeroEquiv_symm_apply
import Theorems.Thm_GlobalTheory_cohOn_zeroEquiv_map
import Theorems.Thm_GlobalTheory_coh_zeroEquiv_map
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
import Theorems.Thm_GlobalTheory_presheafCechHZeroEquiv_symm_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass
attribute [local simp] GlobalTheory.cechAbCubeMap_app_apply
attribute [local simp] GlobalTheory.cechAbHMap_id
attribute [local simp] GlobalTheory.cechAbHZeroEquiv_symm_apply
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id
attribute [local simp] GlobalTheory.presheafCechHZeroEquiv_symm_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe t v u
noncomputable section
open GlobalTheory
variable {X Y : Scheme.{u}} {ι : Type}
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable (F : X.Modules) {G H : X.Modules} (V : X.Opens) (U : ι → X.Opens)
variable [LinearOrder ι]
variable {V U} (hc : V ≤ ⨆ i, U i)
variable {F}
namespace GlobalTheory
theorem _root_.solution (φ : F ⟶ G) (x : cechH R F V U 0) :
    cechHZeroEquivCohOn R G hc ((cechHMap R V U φ 0).hom x) =
      cohOn.map R φ V 0 (cechHZeroEquivCohOn R F hc x) := by
  apply (cohOn.zeroEquiv R G V).injective
  simp only [cechHZeroEquivCohOn, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    cohOn.zeroEquiv_map, cechHZeroEquiv_map]
end GlobalTheory
