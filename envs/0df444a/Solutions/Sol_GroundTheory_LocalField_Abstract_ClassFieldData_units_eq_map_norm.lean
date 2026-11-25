-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.units_eq_map_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:08.895974+00:00
-- url     : https://prove2.me/submissions/02a967a7-6d40-4427-aabb-4b213848203b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_tateZeroVal_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_norm_mem_units
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mem_units
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relInertiaDegree_ne_zero
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open GroundTheory.LocalField.Abstract.ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)
variable {K L : OpenSubgroup G}
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) :
    D.units K = (D.units L).map (norm A (K : Subgroup G) (L : Subgroup G)) := by
  refine le_antisymm ?_ ?_
  · intro u hU
    have h1 : D.tateZeroVal hLK (u : tateZero A (K : Subgroup G) (L : Subgroup G)) = 1 := by
      rw [tateZeroVal_mk, valuationMod_apply, D.mem_units.1 hU, toAdd_one, map_zero, ofAdd_zero]
    have h2 : (u : tateZero A (K : Subgroup G) (L : Subgroup G)) = 1 :=
      (D.tateZeroVal_bijective hax hLK hu).1 (by rw [h1, map_one])
    obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff u).1 h2
    refine ⟨x, ?_, hx⟩
    show x ∈ D.units L
    rw [D.mem_units]
    have h3 := D.valuation_norm hLK x
    rw [hx, D.mem_units.1 hU] at h3
    exact (ProfiniteInteger.pow_left_inj (D.relInertiaDegree_ne_zero hLK)).1
      (by rw [one_pow]; exact h3.symm)
  · rintro _ ⟨x, hx, rfl⟩
    exact D.norm_mem_units hLK hx
end GroundTheory.LocalField.Abstract.ClassFieldData
