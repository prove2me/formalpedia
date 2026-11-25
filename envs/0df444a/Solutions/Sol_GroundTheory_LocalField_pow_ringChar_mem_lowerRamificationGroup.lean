-- Prove2me | solution 1 for GroundTheory.LocalField.pow_ringChar_mem_lowerRamificationGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:30.083801+00:00
-- url     : https://prove2.me/submissions/d45bfe24-fd38-4295-bd19-d83b73fbf2fc

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Theorems.Thm_GroundTheory_LocalField_pow_ringChar_eq_one_unitFiltration
import Theorems.Thm_GroundTheory_LocalField_ramificationQuotientToUnits_mk
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.ramificationQuotientToUnits_mk
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L n) :
    σ ^ ringChar 𝓀[L] ∈ lowerRamificationGroup K L (n + 1 : ℕ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have h : ((⟨σ, hσ⟩ : lowerRamificationGroup K L n) ^ ringChar 𝓀[L]) ∈
      (ramificationToUnits hϖ n).ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_ringChar_eq_one_unitFiltration hn]
  rw [ker_ramificationToUnits, Subgroup.mem_subgroupOf] at h
  simpa using h
end GroundTheory.LocalField
