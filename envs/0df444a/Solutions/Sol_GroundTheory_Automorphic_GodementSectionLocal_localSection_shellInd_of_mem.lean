-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementSectionLocal.localSection_shellInd_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:51:03.93773+00:00
-- url     : https://prove2.me/submissions/f8a94883-2680-4314-b8ff-e2090b560d13

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GodementSectionLocal
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_vecMul_zero_cons_mem_shell_iff
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_ord_det_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_localSection_eq_of_support_subset_shell
import Theorems.Thm_GroundTheory_Automorphic_GodementSectionLocal_apply_eq_one_of_isUnramified
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_measurableSet_ordShell
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
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
namespace GroundTheory.Automorphic.GodementSectionLocal
theorem _root_.solution {χ₁ χ₂ : Fˣ →* ℂˣ} (hu₁ : IsUnramifiedChar χ₁)
    (hu₂ : IsUnramifiedChar χ₂) (s : ℂ) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    localSection χ₁ χ₂ s (shellInd F) k = 1 := by
  rw [localSection_eq_of_support_subset_shell χ₁ χ₂ s (Ψ := shellInd F) Set.support_indicator_subset hk,
    apply_eq_one_of_isUnramified hu₁ (ord_det_eq_zero hk), Units.val_one, one_mul]
  have hpt : (fun u : Fˣ ↦ slice (shellInd F) k u * (((χ₁ * χ₂⁻¹) u : ℂˣ) : ℂ)) =
      (ordShell F 0).indicator 1 := by
    funext u
    by_cases hu : ord (u : F) = 0
    · have hmem : ![0, (u : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∈ shell F :=
        (vecMul_zero_cons_mem_shell_iff hk u).2 hu
      have h1 : χ₁ u = 1 := apply_eq_one_of_isUnramified hu₁ hu
      have h2 : χ₂ u = 1 := apply_eq_one_of_isUnramified hu₂ hu
      simp [slice, shellInd, Set.indicator_of_mem hmem, h1, h2,
        Set.indicator_of_mem (show u ∈ ordShell F 0 from hu)]
    · have hmem : ![0, (u : F)] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) ∉ shell F :=
        fun h ↦ hu ((vecMul_zero_cons_mem_shell_iff hk u).1 h)
      simp [slice, shellInd, Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem (show u ∉ ordShell F 0 from hu)]
  calc ∫ u, slice (shellInd F) k u * (((χ₁ * χ₂⁻¹) u : ℂˣ) : ℂ) ∂multHaar F
      = ∫ u, (ordShell F 0).indicator (1 : Fˣ → ℂ) u ∂multHaar F := by rw [hpt]
    _ = 1 := by
      rw [integral_indicator (measurableSet_ordShell 0)]
      simp [measureReal_def, multHaar_ordShell]
end GroundTheory.Automorphic.GodementSectionLocal
