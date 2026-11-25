-- Prove2me | solution 1 for GroundTheory.ProfCoh.apply_eq_of_mem_lowerRamificationGroup_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:23:22.70997+00:00
-- url     : https://prove2.me/submissions/7a70ec18-1fcb-40d2-9b7b-0fe540a4356a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_LocalField_eq_of_pow_eq_one_of_residue_eq
import Theorems.Thm_GroundTheory_LocalField_mem_integer_of_pow_eq_one
import Theorems.Thm_GroundTheory_LocalField_ramificationQuotientToUnits_mk
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_residue_integerAlgEquiv_of_mem_zero
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.ramificationQuotientToUnits_mk
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.ProfCoh
theorem _root_.solution {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0)
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0) {ζ : L} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  let z : 𝒪[L] := ⟨ζ, mem_integer_of_pow_eq_one hm0 hζ⟩
  have hz : z ^ m = 1 := Subtype.ext (by simpa [z] using hζ)
  have h := eq_of_pow_eq_one_of_residue_eq hm (x := integerAlgEquiv K L σ z) (y := z)
    (by rw [← map_pow, hz, map_one]) hz (residue_integerAlgEquiv_of_mem_zero K L hσ z)
  simpa [z] using congrArg Subtype.val h
end GroundTheory.ProfCoh
