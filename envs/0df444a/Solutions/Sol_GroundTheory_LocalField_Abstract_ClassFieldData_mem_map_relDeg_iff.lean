-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.mem_map_relDeg_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:49:03.624712+00:00
-- url     : https://prove2.me/submissions/4750602d-9c0c-4fb6-9fe7-6d6eb7189151

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_inertiaDegree_eq_mul
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relDeg_eq_iff

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
theorem _root_.solution {K L : OpenSubgroup G} (hLK : L ≤ K) {x : Multiplicative ℤ̂} :
    x ∈ ((L : Subgroup G).subgroupOf K).map (D.relDeg K) ↔
      ∃ y, y ^ relInertiaDegree D.deg K L = x := by
  have hf := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨y, hy⟩ := D.exists_pow_eq_deg L ⟨σ, hσ⟩
    refine ⟨y, ?_⟩
    rw [eq_comm, relDeg_eq_iff, ← pow_mul, ← hf]
    exact hy.symm
  · rintro ⟨y, rfl⟩
    obtain ⟨σ, hσ, hσy⟩ := (D.mem_map_deg_iff L).2 ⟨y, rfl⟩
    refine ⟨⟨σ, hLK hσ⟩, hσ, ?_⟩
    rw [relDeg_eq_iff, ← pow_mul, ← hf]
    exact hσy
end GroundTheory.LocalField.Abstract.ClassFieldData
