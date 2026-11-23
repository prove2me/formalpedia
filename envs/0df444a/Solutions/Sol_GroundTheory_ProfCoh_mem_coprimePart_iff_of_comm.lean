-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_coprimePart_iff_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:08.684921+00:00
-- url     : https://prove2.me/submissions/1aef8e67-fa49-47b1-b8ba-7f445aaaa499

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
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
variable {Q Q' : Type*} [Group Q] [Group Q']
namespace GroundTheory.ProfCoh
theorem _root_.solution {p : ℕ} (hQ : ∀ a b : Q, a * b = b * a) {x : Q} :
    x ∈ coprimePart p Q ↔ (orderOf x).Coprime p := by
  let S : Subgroup Q :=
    { carrier := {x | (orderOf x).Coprime p}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb ↦
        Nat.Coprime.coprime_dvd_left ((Commute.orderOf_mul_dvd_lcm (hQ a b)).trans
          (Nat.lcm_dvd_mul _ _)) (Nat.Coprime.mul_left ha hb)
      inv_mem' := fun {a} ha ↦ by simpa using ha }
  have h : coprimePart p Q = S :=
    le_antisymm ((Subgroup.closure_le S).2 fun _ hx ↦ hx) fun _ hx ↦ Subgroup.subset_closure hx
  rw [h]
  rfl
end GroundTheory.ProfCoh
