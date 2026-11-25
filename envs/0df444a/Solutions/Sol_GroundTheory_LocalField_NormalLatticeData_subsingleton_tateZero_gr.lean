-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.subsingleton_tateZero_gr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:39:45.244798+00:00
-- url     : https://prove2.me/submissions/6005ef05-fd45-485e-841e-81e1560c5399

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_div_mem_filt_iff
import Theorems.Thm_GroundTheory_LocalField_algEquiv_algebraMap_integer
import Theorems.Thm_GroundTheory_LocalField_quotient_mk_sum
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_grHom_toAdd
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_grHom_eq_one_iff
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_val_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_exists_mem_filt
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_tateNorm_F
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_subsingleton_tateZero_gr_iff
import Theorems.Thm_GroundTheory_LocalField_algEquiv_smul_sum
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_smul_sum_mem_normalLattice_add_iff
import Theorems.Thm_GroundTheory_LocalField_smul_sum_sub_smul_sum
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
theorem _root_.solution (j : ℕ) : Subsingleton (TateZero Gal(L/K) (D.filt.gr j)) := by
  rw [D.filt.subsingleton_tateZero_gr_iff]
  intro x hx hinv
  obtain ⟨c, hc⟩ := (mem_normalLattice_iff D.π D.θ).mp (D.mem_filt.mp hx)
  have hdiv : ∀ σ : Gal(L/K), D.π ^ 1 ∣ c σ - c 1 := by
    intro σ
    have h1 := D.div_mem_filt_iff.mp (hinv σ)
    rw [← add_assoc] at h1
    have e : D.val (σ • x) - D.val x = D.π ^ (D.k + j) • ∑ τ, (c (σ⁻¹ * τ) - c τ) • τ D.θ := by
      rw [← smul_sum_sub_smul_sum, ← algEquiv_smul_sum, hc, val_smul, map_sub, map_one]
      ring
    rw [e] at h1
    have h2 := (smul_sum_mem_normalLattice_add_iff D.π D.θ D.irreducible.ne_zero
      D.linearIndependent (D.k + j) 1 _).mp h1 σ
    rw [inv_mul_cancel] at h2
    have := dvd_neg.mpr h2
    rwa [neg_sub] at this
  obtain ⟨y, hy, hyv⟩ := D.exists_mem_filt j (c 1)
  refine ⟨y, hy, ?_⟩
  let x' : D.filt.F j := ⟨x, hx⟩
  let y' : D.filt.F j := ⟨y, hy⟩
  have e1 : x / tateNorm Gal(L/K) (D.units 0) y =
      ((x' / tateNorm Gal(L/K) (D.filt.F j) y' : D.filt.F j) : D.units 0) := by
    rw [Subgroup.coe_div, D.filt.coe_tateNorm_F]
  rw [e1, ← grHom_eq_one_iff, map_div, div_eq_one]
  apply Multiplicative.toAdd.injective
  rw [grHom_toAdd, tateNorm_apply, map_prod, toAdd_prod]
  simp_rw [grHom_toAdd, val_coe_smul_F]
  rw [quotient_mk_sum, QuotientAddGroup.eq_iff_sub_mem, Submodule.mem_toAddSubgroup]
  have e2 : D.val x' - 1 - ∑ σ : Gal(L/K), (σ (D.val y') - 1) =
      D.π ^ (D.k + j) • ∑ σ, (c σ - c 1) • σ D.θ := by
    show D.val x - 1 - ∑ σ : Gal(L/K), (σ (D.val y) - 1) = _
    rw [← hc, hyv]
    simp only [Algebra.smul_def, map_add, map_one, map_mul, map_pow, map_sub,
      algEquiv_algebraMap_integer, add_sub_cancel_left, Finset.mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun σ _ => ?_
    ring
  rw [e2]
  exact (smul_sum_mem_normalLattice_add_iff D.π D.θ D.irreducible.ne_zero D.linearIndependent
    (D.k + j) 1 _).mpr hdiv
end GroundTheory.LocalField.NormalLatticeData
