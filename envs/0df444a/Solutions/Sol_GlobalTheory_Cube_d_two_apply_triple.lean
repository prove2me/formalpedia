-- Prove2me | solution 1 for GlobalTheory.Cube.d_two_apply_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:10.387999+00:00
-- url     : https://prove2.me/submissions/b5a31938-b87c-491f-9255-a5ef785944ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexGradedModuleExactAtOfLargeDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCoboundaryOfFractionCocycleHomogeneousIdea
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
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open MvPolynomial DirectSum
open GlobalTheory
namespace GlobalTheory
namespace Cube
theorem _root_.solution {ι : Type} [LinearOrder ι] {R : Type*} [Ring R]
    (A : Cube ι R) (x : Cube.Term A 2) {i j l : ι} (hij : i < j) (hjl : j < l) :
    Cube.d A 2 x ⟨{i, j, l}, by rw [Finset.card_eq_three]; exact ⟨i, j, l, hij.ne, (hij.trans hjl).ne, hjl.ne, rfl⟩⟩ =
      Cube.res A (by intro k; simp; tauto) (x ⟨{j, l}, Finset.card_pair hjl.ne⟩) -
        Cube.res A (by intro k; simp; tauto) (x ⟨{i, l}, Finset.card_pair (hij.trans hjl).ne⟩) +
        Cube.res A (by intro k; simp; tauto) (x ⟨{i, j}, Finset.card_pair hij.ne⟩) := by
  have hil := hij.trans hjl
  rw [Cube.d_apply_extend, Finset.sum_insert (by simp [hij.ne, hil.ne]), Finset.sum_pair hjl.ne,
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hjl.ne),
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hil.ne),
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hij.ne)]
  have e1 : ({i, j, l} : Finset ι).erase i = {j, l} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hij.ne', hil.ne']
  have e2 : ({i, j, l} : Finset ι).erase j = {i, l} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hij.ne, hjl.ne']
  have e3 : ({i, j, l} : Finset ι).erase l = {i, j} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hil.ne, hjl.ne]
  have s1 : cubeSign ({i, j, l} : Finset ι) i = 1 :=
    cubeSign_eq_one_of_forall_le (by simp [hij.le, hil.le])
  have s2 : cubeSign ({i, j, l} : Finset ι) j = -1 := by
    have := cubeSign_erase_of_lt (t := {i, j, l}) (by simp) hij
    rw [e1, cubeSign_eq_one_of_forall_le (by simp [hjl.le])] at this
    omega
  have s3 : cubeSign ({i, j, l} : Finset ι) l = 1 := by
    have a1 := cubeSign_erase_of_lt (t := {i, j, l}) (by simp) hil
    rw [e1] at a1
    have a2 := cubeSign_erase_of_lt (t := {j, l}) (by simp) hjl
    rw [Finset.erase_insert (by simp [hjl.ne]), cubeSign_singleton] at a2
    omega
  rw [Cube.res_congr A _ e1 _ (by intro k; simp; tauto), Cube.res_congr A _ e2 _ (by intro k; simp; tauto),
    Cube.res_congr A _ e3 _ (by intro k; simp; tauto), s1, s2, s3]
  simp only [one_smul, neg_smul]
  abel
end Cube
end GlobalTheory
