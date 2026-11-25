-- Prove2me | solution 1 for GroundTheory.GroupCoh.revCochain_cupCochain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:25:22.811286+00:00
-- url     : https://prove2.me/submissions/1fa392d8-3096-4bac-ac09-55853b2534f1

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse
import Definitions.Def_GroundTheory_TateCohomology_CupGraded
import Theorems.Thm_GroundTheory_GroupCoh_braiding_hom_tmul
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_GroundTheory_GroupCoh_partialProd_add
import Theorems.Thm_GroundTheory_GroupCoh_partialProd_last_revInv
import Theorems.Thm_GroundTheory_GroupCoh_partialProd_prefix
import Theorems.Thm_GroundTheory_GroupCoh_triangle_add
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tensor___tmul_caf50afb1144
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (h : p + q = n) (h' : q + p = n) (f : (Fin p → G) → A)
    (g : (Fin q → G) → B) (x : Fin n → G) :
    revCochain n (cupCochain h f g) x =
      (-1 : k) ^ (p * q) • (β_ B A).hom.hom (cupCochain h' (revCochain q g) (revCochain p f) x) := by
  subst h'
  have hpre : (fun i : Fin p => revInv x ⟨i, by omega⟩) =
      revInv (fun j : Fin p => x ⟨q + j, by omega⟩) := by
    funext i
    simp only [revInv_apply]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega
  have hsuf : (fun j : Fin q => revInv x ⟨p + j, by omega⟩) =
      revInv (fun i : Fin q => x ⟨i, by omega⟩) := by
    funext j
    simp only [revInv_apply]
    congr 2
    ext
    simp only [Fin.val_rev]
    omega
  have hP₁ : Fin.partialProd (revInv x) ⟨p, by omega⟩ =
      (Fin.partialProd (fun j : Fin p => x ⟨q + j, by omega⟩) (Fin.last p))⁻¹ := by
    rw [← partialProd_prefix (revInv x) (m := p) (by omega) le_rfl, hpre, ← partialProd_last_revInv]
    rfl
  have hP : Fin.partialProd x (Fin.last (q + p)) =
      Fin.partialProd (fun i : Fin q => x ⟨i, by omega⟩) (Fin.last q) *
        Fin.partialProd (fun j : Fin p => x ⟨q + j, by omega⟩) (Fin.last p) := by
    have := partialProd_add x (fun j : Fin p => x ⟨q + j, by omega⟩) (p := q) (q := p)
      le_rfl (fun _ => rfl) le_rfl
    rw [← partialProd_prefix x (m := q) (by omega) le_rfl] at this
    exact this
  have hP₂ : Fin.partialProd x ⟨q, by omega⟩ =
      Fin.partialProd (fun i : Fin q => x ⟨i, by omega⟩) (Fin.last q) :=
    (partialProd_prefix x (m := q) (by omega) le_rfl).symm
  rw [revCochain_apply, cupCochain_apply, cupCochain_apply, revCochain_apply, revCochain_apply,
    hpre, hsuf, hP₁, hP₂, map_smul, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul,
    map_smul, braiding_hom_tmul, tensor_ρ_tmul, ← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul, hP, mul_inv_cancel_right, smul_smul, ← pow_add, ← pow_add,
    triangle_add]
  congr 2
  ring
end GroundTheory.GroupCoh
