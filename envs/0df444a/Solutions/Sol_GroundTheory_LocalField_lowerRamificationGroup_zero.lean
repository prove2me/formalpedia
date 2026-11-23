-- Prove2me | solution 1 for GroundTheory.LocalField.lowerRamificationGroup_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:49.671795+00:00
-- url     : https://prove2.me/submissions/20986263-1ffa-4ea4-a0bd-eaf8ba8f2ab2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Theorems.Thm_GroundTheory_LocalField_mem_lowerRamificationGroup_iff
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
open ValuativeRel IsLocalRing
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)
variable {K L}
variable (K L)
namespace GroundTheory.LocalField
theorem _root_.solution : lowerRamificationGroup K L 0 = (residueAlgEquiv K L).ker := by
  ext σ
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff]
  have : ((0 : ℤ) + 1).toNat = 1 := rfl
  rw [mem_lowerRamificationGroup_iff, this, pow_one]
  refine ⟨fun h r ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := residue_surjective r
    rw [residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff]
    exact h x
  · have := h (residue 𝒪[L] x)
    rwa [residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff] at this
end GroundTheory.LocalField
