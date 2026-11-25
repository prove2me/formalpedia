-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.subsingleton_tateNegOne_gr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:10:30.749663+00:00
-- url     : https://prove2.me/submissions/842585ac-2e78-4b4f-82ca-c5cffc887074

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_algEquiv_algebraMap_integer
import Theorems.Thm_GroundTheory_LocalField_quotient_mk_sum
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_grHom_toAdd
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_grHom_eq_one_iff
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_val_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_exists_mem_filt
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_augMap_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_tateNorm_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_subsingleton_tateNegOne_gr_iff
import Theorems.Thm_GroundTheory_LocalField_algEquiv_smul_sum
import Theorems.Thm_GroundTheory_LocalField_augMap_apply
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_smul_sum_mem_normalLattice_add_iff
import Theorems.Thm_GroundTheory_LocalField_tateNorm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
open GroundTheory.LocalField.NormalLatticeData
variable (D : NormalLatticeData K L)
attribute [local instance] action
namespace GroundTheory.LocalField.NormalLatticeData
theorem _root_.solution (j : ℕ) : Subsingleton (TateNegOne Gal(L/K) (D.filt.gr j)) := by
  rw [D.filt.subsingleton_tateNegOne_gr_iff]
  intro x hx hN
  obtain ⟨c, hc⟩ := (mem_normalLattice_iff D.π D.θ).mp (D.mem_filt.mp hx)
  let x' : D.filt.F j := ⟨x, hx⟩
  have hN' : ((tateNorm Gal(L/K) (D.filt.F j) x' : D.filt.F j) : D.units 0) ∈ D.filt.F (j + 1) := by
    rwa [D.filt.coe_tateNorm_F]
  rw [← grHom_eq_one_iff, ← toAdd_eq_zero, tateNorm_apply, map_prod, toAdd_prod] at hN'
  simp_rw [grHom_toAdd, val_coe_smul_F] at hN'
  rw [quotient_mk_sum, QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup] at hN'
  have e : ∑ σ : Gal(L/K), (σ (D.val x') - 1) =
      D.π ^ (D.k + j) • ∑ τ, (∑ σ : Gal(L/K), c (σ⁻¹ * τ)) • τ D.θ := by
    have h1 : ∀ σ : Gal(L/K), σ (D.val x') - 1 = σ (D.val x' - 1) := fun σ => by
      rw [map_sub, map_one]
    simp_rw [h1]
    show ∑ σ : Gal(L/K), σ (D.val x - 1) = _
    simp_rw [← hc, algEquiv_smul_sum, ← smul_sum]
    rw [sum_comm]
    simp_rw [sum_smul]
  rw [e] at hN'
  have hdiv := (smul_sum_mem_normalLattice_add_iff D.π D.θ D.irreducible.ne_zero
    D.linearIndependent (D.k + j) 1 _).mp hN' 1
  have hsumc : ∑ σ : Gal(L/K), c (σ⁻¹ * 1) = ∑ σ, c σ := by
    simp_rw [mul_one]
    exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)
  rw [hsumc, pow_one] at hdiv
  obtain ⟨e0, he0⟩ := hdiv
  choose m hm hmv using fun τ => D.exists_mem_filt j (c τ)
  refine ⟨m, hm, ?_⟩
  let m' : Gal(L/K) → D.filt.F j := fun τ => ⟨m τ, hm τ⟩
  have e1 : x / augMap Gal(L/K) (D.units 0) m =
      ((x' / augMap Gal(L/K) (D.filt.F j) m' : D.filt.F j) : D.units 0) := by
    rw [Subgroup.coe_div, D.filt.coe_augMap_F]
  rw [e1, ← grHom_eq_one_iff, map_div, div_eq_one]
  apply Multiplicative.toAdd.injective
  rw [grHom_toAdd, augMap_apply, map_prod, toAdd_prod]
  simp_rw [map_div, toAdd_div, grHom_toAdd, val_coe_smul_F, ← QuotientAddGroup.mk_sub]
  rw [quotient_mk_sum, QuotientAddGroup.eq_iff_sub_mem, Submodule.mem_toAddSubgroup]
  have e2 : D.val x' - 1 - ∑ τ : Gal(L/K), (τ (D.val (m' τ)) - 1 - (D.val (m' τ) - 1)) =
      e0 • D.π ^ (D.k + j + 1) • D.θ := by
    show D.val x - 1 - ∑ τ : Gal(L/K), (τ (D.val (m τ)) - 1 - (D.val (m τ) - 1)) = _
    rw [← hc]
    simp_rw [hmv]
    have he0' : ∑ τ, algebraMap 𝒪[K] L (c τ) = algebraMap 𝒪[K] L D.π * algebraMap 𝒪[K] L e0 := by
      rw [← map_sum, he0, map_mul]
    simp only [Algebra.smul_def, map_add, map_one, map_mul, map_pow,
      algEquiv_algebraMap_integer, add_sub_cancel_left, Finset.mul_sum, sum_sub_distrib]
    have h3 : ∑ τ : Gal(L/K), algebraMap 𝒪[K] L (c τ) * (algebraMap 𝒪[K] L D.π ^ (D.k + j) * D.θ) =
        (∑ τ, algebraMap 𝒪[K] L (c τ)) * (algebraMap 𝒪[K] L D.π ^ (D.k + j) * D.θ) := by
      rw [Finset.sum_mul]
    rw [h3, he0']
    ring_nf
  rw [e2]
  have : D.π ^ (D.k + j + 1) • (1 : Gal(L/K)) D.θ ∈ D.lat (D.k + j + 1) :=
    Submodule.subset_span ⟨1, rfl⟩
  simpa using Submodule.smul_mem _ e0 this
end GroundTheory.LocalField.NormalLatticeData
