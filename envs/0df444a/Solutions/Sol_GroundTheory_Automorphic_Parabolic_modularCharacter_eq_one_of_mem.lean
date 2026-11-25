-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.modularCharacter_eq_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:45:18.621048+00:00
-- url     : https://prove2.me/submissions/8b2ad444-0ea2-450d-9c19-4c68bdc8982a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_mem_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompact_of_bound
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_pow_mul_mem_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Measures_modularCharacter_eq_one_of_mem_integralGL
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



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
open MeasureTheory Measure
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ unipotentRadical F n β) : modularCharacter p = 1 := by
  classical
  let u : unipotentRadical F n β := ⟨p, hp⟩
  obtain ⟨e, he⟩ := exists_pow_mul_mem_of_isCompact F n
    (Set.toFinite ({(p : GL (Fin n) F), (p : GL (Fin n) F)⁻¹} : Set _)).isCompact
  have hmem := mem_integralGL_iff F n |>.1 <| (mem_unipotentCompact (u := u)).1
    (mem_unipotentCompact_of_bound (fun i j => he _ (by simp [u]) i j)
      (fun i j => he _ (by simp [u]) i j))
  let t : blockUpper F n β := ⟨rankTorus F n β e, rankTorus_mem_blockUpper e⟩
  have h1 : modularCharacter (t * p * t⁻¹) = 1 :=
    Measures.modularCharacter_eq_one_of_mem_integralGL (t * p * t⁻¹)
      ((mem_integralGL_iff F n).2 hmem)
  rw [map_mul, map_mul, mul_comm (modularCharacter t), mul_assoc, ← map_mul, mul_inv_cancel,
    map_one, mul_one] at h1
  exact h1
end GroundTheory.Automorphic.Parabolic
