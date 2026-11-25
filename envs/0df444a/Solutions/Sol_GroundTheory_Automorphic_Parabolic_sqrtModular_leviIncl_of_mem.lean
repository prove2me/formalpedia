-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.sqrtModular_leviIncl_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:56:30.643288+00:00
-- url     : https://prove2.me/submissions/4f7e2df6-c1aa-49a6-8f0a-c811fe004787

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_pow_mul_mem_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Measures_modularCharacter_eq_one_of_mem_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagGL_mem_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_conj_apply_mem
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {γ : Fin n → ℕ} (m : levi F n β)
    (hm : (m : GL (Fin n) F) ∈ unipotentRadical F n γ) :
    sqrtModular F n β (leviIncl m) = 1 := by
  have key : modularCharacter (leviIncl m) = 1 := by
    obtain ⟨e, he⟩ := exists_pow_mul_mem_of_isCompact F n
      (Set.toFinite ({(m : GL (Fin n) F), (m : GL (Fin n) F)⁻¹} : Set _)).isCompact
    let t : blockUpper F n β :=
      ⟨rankTorus F n γ e, levi_le_blockUpper (diagGL_mem_levi _)⟩
    have hint : ((t * leviIncl m * t⁻¹ : blockUpper F n β) : GL (Fin n) F) ∈ integralGL F n := by
      show rankTorus F n γ e * (m : GL (Fin n) F) * (rankTorus F n γ e)⁻¹ ∈ integralGL F n
      rw [mem_integralGL_iff]
      refine ⟨rankTorus_conj_apply_mem hm (fun i j => he _ (by simp) i j), fun i j => ?_⟩
      have : (rankTorus F n γ e * (m : GL (Fin n) F) * (rankTorus F n γ e)⁻¹)⁻¹ =
          rankTorus F n γ e * (m : GL (Fin n) F)⁻¹ * (rankTorus F n γ e)⁻¹ := by group
      rw [this]
      exact rankTorus_conj_apply_mem ((unipotentRadical F n γ).inv_mem hm)
        (fun i j => he _ (by simp) i j) i j
    have h1 := Measures.modularCharacter_eq_one_of_mem_integralGL (t * leviIncl m * t⁻¹) hint
    rw [map_mul, map_mul, mul_comm (modularCharacter t), mul_assoc, ← map_mul, mul_inv_cancel,
      map_one, mul_one] at h1
    exact h1
  show ((NNReal.sqrt (modularCharacter (leviIncl m)) : ℝ) : ℂ) = 1
  rw [key]
  simp
end GroundTheory.Automorphic.Parabolic
