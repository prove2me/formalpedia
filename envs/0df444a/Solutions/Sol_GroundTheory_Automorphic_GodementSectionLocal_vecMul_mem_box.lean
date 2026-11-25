-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.vecMul_mem_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:45:13.786139+00:00
-- url     : https://prove2.me/submissions/ce54a394-a681-4128-8590-c2d31e9901bd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_mem_box
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_mul_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open GroundTheory.LocalField
noncomputable section
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
omit [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution {k : GL (Fin 2) F} (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F])
    {n : ℤ} {x : Fin 2 → F} (hx : x ∈ box F n) :
    x ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ box F n := by
  refine mem_box.2 fun j ↦ ?_
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  have h : ∀ i, x i * (k : Matrix (Fin 2) (Fin 2) F) i j ∈ valBall F n := fun i ↦ by
    simpa using mul_mem_valBall (mem_box.1 hx i) (mem_valBall_zero_iff.2 (hk i j))
  exact add_mem (h 0) (h 1)
end GroundTheory.Automorphic.GodementSectionLocal
