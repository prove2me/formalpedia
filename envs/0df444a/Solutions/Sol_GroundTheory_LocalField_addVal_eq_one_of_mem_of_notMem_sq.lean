-- Prove2me | solution 1 for GroundTheory.LocalField.addVal_eq_one_of_mem_of_notMem_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:44.594029+00:00
-- url     : https://prove2.me/submissions/93aa90f1-3178-452b-abc3-34c28b1db4cc

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_exists_addVal_eq_coe
import Theorems.Thm_GroundTheory_LocalField_mem_maximalIdeal_pow_iff_le_addVal
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
namespace GroundTheory.LocalField
theorem _root_.solution {x : R} (h1 : x ∈ IsLocalRing.maximalIdeal R)
    (h2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) : addVal R x = 1 := by
  rw [← pow_one (IsLocalRing.maximalIdeal R), mem_maximalIdeal_pow_iff_le_addVal] at h1
  rw [mem_maximalIdeal_pow_iff_le_addVal, not_le] at h2
  have h0 : x ≠ 0 := by
    rintro rfl
    simp at h2
  obtain ⟨k, hk⟩ := exists_addVal_eq_coe h0
  rw [hk] at h1 h2 ⊢
  norm_cast at h1 h2 ⊢
  omega
end GroundTheory.LocalField
