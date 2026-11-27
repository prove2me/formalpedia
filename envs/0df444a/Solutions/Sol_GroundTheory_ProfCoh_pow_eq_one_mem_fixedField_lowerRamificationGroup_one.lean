-- Prove2me | solution 1 for GroundTheory.ProfCoh.pow_eq_one_mem_fixedField_lowerRamificationGroup_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:50:41.825218+00:00
-- url     : https://prove2.me/submissions/25137f42-15f7-422b-ade2-32840da58b88

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
import Theorems.Thm_GroundTheory_ProfCoh_algEquiv_apply_eq_of_pow_prime_pow_apply_eq
import Theorems.Thm_GroundTheory_LocalField_isPGroup_lowerRamificationGroup_one
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
namespace GroundTheory.ProfCoh
theorem _root_.solution {ζ : L}
    (hζ : ζ ^ ringChar 𝓀[K] = 1) : ζ ∈ fixedField (lowerRamificationGroup K L 1) := by
  refine (mem_fixedField_iff _ _).2 fun σ hσ ↦ ?_
  obtain ⟨n, hn⟩ := isPGroup_lowerRamificationGroup_one K L ⟨σ, hσ⟩
  have hσn : σ ^ ringChar 𝓀[K] ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact algEquiv_apply_eq_of_pow_prime_pow_apply_eq (CharP.char_is_prime 𝓀[K] _) hζ σ
    (by rw [hσn, AlgEquiv.one_apply])
end GroundTheory.ProfCoh
