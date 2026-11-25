-- Prove2me | solution 1 for GlobalTheory.sum_cubeSign_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:42:36.933588+00:00
-- url     : https://prove2.me/submissions/f477bf7b-2be2-4c94-9374-656de18b3ca1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractions
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
import Theorems.Thm_GlobalTheory_GrSum_map_of
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
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} [LinearOrder ι] {t : Finset ι} (ht : t.card = 2) :
    ∑ i ∈ t, cubeSign t i = 0 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hab]
  have h := cubeSign_mul_erase (t := {a, b}) (by simp) (by simp) hab
  rw [Finset.erase_insert (by simpa using hab), Finset.pair_comm,
    Finset.erase_insert (by simpa using hab.symm), cubeSign_singleton, cubeSign_singleton,
    mul_one, mul_one, Finset.pair_comm] at h
  rw [h]; ring
end GlobalTheory
