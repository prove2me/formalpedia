-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_sum_eq_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:28:04.857134+00:00
-- url     : https://prove2.me/submissions/434f43ac-5b31-4837-936b-33ceff9c26cd

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Theorems.Thm_GroundTheory_GroupCoh_coeffOneProj_apply
import Theorems.Thm_GroundTheory_GroupCoh_indSES_obj_g
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
import Theorems.Thm_P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.indSES_obj_g
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_map____b9067ca7808e
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__c57492aa2d98
attribute [local simp] P2M_GroundTheory_GroupCoh_indSES_obj_X__e6c60d2b2881



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
open scoped MonoidAlgebra
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (M : Rep.{u} k G) {ι : Type*}
    (b : Module.Basis ι k[G] M.ρ.asModule) :
    ∃ φ : M.V →ₗ[k] M.V, ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m := by
  let φ : M.V →ₗ[k] M.V := M.ρ.asModuleEquiv.toLinearMap ∘ₗ
    (b.repr.symm.toLinearMap.restrictScalars k) ∘ₗ Finsupp.mapRange.linearMap coeffOneProj ∘ₗ
    (b.repr.toLinearMap.restrictScalars k) ∘ₗ M.ρ.asModuleEquiv.symm.toLinearMap
  refine ⟨φ, fun m => ?_⟩
  apply M.ρ.asModuleEquiv.symm.injective
  apply b.repr.injective
  simp only [map_sum, φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
    Representation.asModuleEquiv_symm_map_rho, map_smul, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply]
  generalize b.repr (M.ρ.asModuleEquiv.symm m) = c
  ext i : 1
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, coeffOneProj_apply, smul_eq_mul,
    MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.single_mul_single,
    mul_one, one_mul, inv_inv]
  conv_rhs => rw [← MonoidAlgebra.sum_coeff_single (c i)]
  exact (Finsupp.sum_fintype _ _ (by simp)).symm
end GroundTheory.GroupCoh
