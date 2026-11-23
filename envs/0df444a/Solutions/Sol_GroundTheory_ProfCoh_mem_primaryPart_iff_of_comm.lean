-- Prove2me | solution 1 for GroundTheory.ProfCoh.mem_primaryPart_iff_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:08.79439+00:00
-- url     : https://prove2.me/submissions/b5ac5976-bd62-488a-8554-008accf06bcd

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hQ : ∀ a b : Q, a * b = b * a)
    {x : Q} : x ∈ primaryPart p Q ↔ ∃ n : ℕ, orderOf x = p ^ n := by
  let S : Subgroup Q :=
    { carrier := {x | ∃ n : ℕ, orderOf x = p ^ n}
      one_mem' := ⟨0, by simp⟩
      mul_mem' := fun {a b} ha hb ↦ by
        obtain ⟨m, hm⟩ := ha
        obtain ⟨n, hn⟩ := hb
        have h := (Commute.orderOf_mul_dvd_lcm (hQ a b)).trans (Nat.lcm_dvd_mul _ _)
        rw [hm, hn, ← pow_add] at h
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h
        exact ⟨k, hk⟩
      inv_mem' := fun {a} ha ↦ by simpa using ha }
  have h : primaryPart p Q = S :=
    le_antisymm ((Subgroup.closure_le S).2 fun _ hx ↦ hx) fun _ hx ↦ Subgroup.subset_closure hx
  rw [h]
  rfl
end GroundTheory.ProfCoh
