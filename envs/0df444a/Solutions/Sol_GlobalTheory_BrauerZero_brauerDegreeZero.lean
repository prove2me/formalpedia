-- Prove2me | solution 1 for GlobalTheory.BrauerZero.brauerDegreeZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:43.16658+00:00
-- url     : https://prove2.me/submissions/aac81fda-3300-4aa7-91d2-a5cb15e24249

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__BrauerDegreeZero_fefd58e19a2fa426
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldRestrictClassFunctionOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldInductionIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MemVirtualCharactersIffSubCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IrreducibleCharacterLinearOrInducedAbelianByPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharactersMulComapConjIndLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IndMulClassFunEqIndMulRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemClosureInducedCentralByPrimePower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IndApplyOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionFromSubgroupTransStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedClassFunctionMemInducedDegreeOneCharDiffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InducedOneSubIndexMemDegreeOneCharacterDiffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLtCommutatorMemOfNeTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BrauerDegreeZero
import Theorems.Thm_GlobalTheory_BrauerZero_virtualCharacter_degreeZero_mem_degreeOneDiff
import Theorems.Thm_GlobalTheory_BrauerZero_exists_sum_induced_characters_of_mem_degreeOneDiff
import Theorems.Thm_GlobalTheory_BI_isChar_and_isIrrChar_of_rep
import Theorems.Thm_GlobalTheory_BI_isChar_mem_virt_complex
import Theorems.Thm_GlobalTheory_BI_isChar_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BrauerZero
namespace GlobalTheory.BrauerZero
theorem _root_.solution : GlobalTheory.Published.BrauerDegreeZero := by
  intro G _ _ V _ _ _ ρ
  classical
  have hchar := (isChar_and_isIrrChar_of_rep ℂ ℂ G V ρ).1
  have hV : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) ∈ Virt ℂ ℂ G := by
    have e : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) =
        (fun g => algebraMap ℂ ℂ (ρ.character g)) - (Module.finrank ℂ V) • (fun _ => (1 : ℂ)) := by
      funext g; simp [Representation.character]
    rw [e]
    exact sub_mem (isChar_mem_virt_complex hchar)
      (nsmul_mem (isChar_mem_virt_complex (isChar_one ℂ ℂ G)) _)
  have h1 : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) 1 = 0 := by simp
  exact exists_sum_induced_characters_of_mem_degreeOneDiff (virtualCharacter_degreeZero_mem_degreeOneDiff _ G le_rfl _ hV h1)
end GlobalTheory.BrauerZero
