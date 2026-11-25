-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift.inertiaDegree_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:38:11.450435+00:00
-- url     : https://prove2.me/submissions/3cf8f447-0848-42e8-9dce-be6193c78d65

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
import Theorems.Thm_GroundTheory_LocalField_Abstract_inertiaDegree_frobeniusClosure


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
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A)
variable {D} {K L : OpenSubgroup G}
open GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)
namespace GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift
theorem _root_.solution :
    inertiaDegree D.deg ((s.field L hLK : OpenSubgroup G) : Subgroup G) =
      s.deg * inertiaDegree D.deg K :=
  inertiaDegree_frobeniusClosure D.continuous_deg (mem_normalizer hLK s.mem) s.degree_ne_zero
    s.deg_eq
end GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift
