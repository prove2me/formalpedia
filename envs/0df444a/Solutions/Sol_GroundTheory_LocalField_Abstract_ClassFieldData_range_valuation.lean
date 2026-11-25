-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.range_valuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:21:42.387806+00:00
-- url     : https://prove2.me/submissions/ca55a30d-e9a4-4125-a57b-9bea757f216b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_eq_iff

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
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (K : OpenSubgroup G) : (D.valuation K).range = D.val.range := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact (D.exists_valuation K a).choose_spec.1
  · intro hz
    have h : z ^ inertiaDegree D.deg K ∈
        (D.val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range := by
      rw [D.range_val_comp_norm K]
      exact ⟨z, hz, rfl⟩
    obtain ⟨a, ha⟩ := h
    exact ⟨a, (D.valuation_eq_iff K a z).2 ha⟩
end GroundTheory.LocalField.Abstract.ClassFieldData
