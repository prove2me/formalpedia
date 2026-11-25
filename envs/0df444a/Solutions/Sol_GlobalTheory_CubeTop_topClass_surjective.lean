-- Prove2me | solution 1 for GlobalTheory.CubeTop.topClass_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:46.630023+00:00
-- url     : https://prove2.me/submissions/f8cbdcaf-d04c-4fe5-bd0b-fe9872bf0f83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_TopClassSurjective
import Theorems.Thm_GlobalTheory_CubeTop_topTerm_surjective
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_comp
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.CubeTop
variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]
namespace GlobalTheory.CubeTop
theorem _root_.solution (A : Cube.{0} ι R) : Function.Surjective (topClass A) :=
  ((ModuleCat.epi_iff_surjective ((cubeComplex A).pOpcycles (Fintype.card ι) ≫
    ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
      (d_top A)).inv)).1 inferInstance).comp (topTerm_surjective A rfl)
end GlobalTheory.CubeTop
