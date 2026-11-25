-- Prove2me | solution 1 for GlobalTheory.AbLaw.CechOne.d_two_apply_triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:47:43.911209+00:00
-- url     : https://prove2.me/submissions/8b14f2de-bcb0-468d-874a-b9f7dd9fbff9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
namespace GlobalTheory.AbLaw.CechOne
theorem _root_.solution {κ : Type} [LinearOrder κ] (A : GlobalTheory.Cube.{0} κ R) (x : GlobalTheory.Cube.Term A 2)
    {i j k : κ} (h : i < j) (h' : j < k) (hc : ({i, j, k} : Finset κ).card = 2 + 1) :
    GlobalTheory.Cube.d A 2 x ⟨{i, j, k}, hc⟩ =
      GlobalTheory.Cube.res A (by simp) (x ⟨{j, k}, Finset.card_pair h'.ne⟩) -
        GlobalTheory.Cube.res A (by simp) (x ⟨{i, k}, Finset.card_pair (h.trans h').ne⟩) +
        GlobalTheory.Cube.res A (by simp [Finset.insert_subset_iff]) (x ⟨{i, j}, Finset.card_pair h.ne⟩) := by
  have h'' := h.trans h'
  rw [GlobalTheory.Cube.d_apply_extend, Finset.sum_insert (by simp [h.ne, h''.ne]), Finset.sum_pair h'.ne,
    ← GlobalTheory.Cube.extend_apply_of_eq A x (Finset.card_pair h'.ne),
    ← GlobalTheory.Cube.extend_apply_of_eq A x (Finset.card_pair h''.ne),
    ← GlobalTheory.Cube.extend_apply_of_eq A x (Finset.card_pair h.ne)]
  have e1 : ({i, j, k} : Finset κ).erase i = {j, k} := Finset.erase_insert (by simp [h.ne, h''.ne])
  have e2 : ({i, j, k} : Finset κ).erase j = {i, k} := by
    rw [Finset.erase_insert_of_ne h.ne, Finset.erase_insert (by simp [h'.ne])]
  have e3 : ({i, j, k} : Finset κ).erase k = {i, j} := by
    rw [Finset.erase_insert_of_ne h''.ne, Finset.erase_insert_of_ne h'.ne, Finset.erase_singleton]
    rfl
  have s1 : cubeSign ({i, j, k} : Finset κ) i = 1 :=
    cubeSign_eq_one_of_forall_le (by simp [h.le, h''.le])
  have s2 : cubeSign ({i, j, k} : Finset κ) j = -1 := by
    have := cubeSign_erase_of_lt (t := {i, j, k}) (by simp) h
    rw [e1, cubeSign_eq_one_of_forall_le (by simp [h'.le])] at this
    omega
  have s3 : cubeSign ({i, j, k} : Finset κ) k = 1 := by
    have h1 := cubeSign_erase_of_lt (t := {i, j, k}) (by simp) h''
    have h2 := cubeSign_erase_of_lt (t := {j, k}) (by simp) h'
    rw [Finset.erase_insert (by simp [h'.ne]), cubeSign_singleton] at h2
    rw [e1] at h1
    omega
  rw [GlobalTheory.Cube.res_congr A _ e1 _ (by simp), GlobalTheory.Cube.res_congr A _ e2 _ (by simp),
    GlobalTheory.Cube.res_congr A _ e3 _ (by simp [Finset.insert_subset_iff])]
  simp only [s1, s2, s3, one_smul, neg_smul, sub_eq_add_neg, add_assoc]
end GlobalTheory.AbLaw.CechOne
