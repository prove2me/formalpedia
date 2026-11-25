-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.relInertiaDegree_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:49:16.344312+00:00
-- url     : https://prove2.me/submissions/6cbd4acb-993e-4d81-b97c-25c3b219a719

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_inertiaDegree_eq_mul

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
    relInertiaDegree D.deg K L ≠ 0 := fun h =>
  D.inertiaDegree_ne_zero L (by
    rw [inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK, h,
      zero_mul])
end GroundTheory.LocalField.Abstract.ClassFieldData
