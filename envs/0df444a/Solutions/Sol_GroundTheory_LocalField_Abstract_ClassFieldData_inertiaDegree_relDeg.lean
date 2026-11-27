-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.inertiaDegree_relDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:58.999521+00:00
-- url     : https://prove2.me/submissions/7dd19247-3a25-4253-8df7-9090f6ef3773

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_inertiaDegree_eq_mul
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_index_range_powMonoidHom
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mem_map_relDeg_iff

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
theorem _root_.solution {K L : OpenSubgroup G} (hLK : L ≤ K) :
    inertiaDegree (D.relDeg K) ((L : Subgroup G).subgroupOf K) = relInertiaDegree D.deg K L := by
  have hf := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK
  have hne : relInertiaDegree D.deg K L ≠ 0 := fun h => D.inertiaDegree_ne_zero L (by rw [hf, h, zero_mul])
  have h : ((L : Subgroup G).subgroupOf K).map (D.relDeg K) =
      (powMonoidHom (relInertiaDegree D.deg K L) : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range := by
    ext x
    rw [D.mem_map_relDeg_iff hLK]
    rfl
  rw [inertiaDegree, h, index_range_powMonoidHom hne]
end GroundTheory.LocalField.Abstract.ClassFieldData
