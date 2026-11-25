-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift.relDeg_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:48:26.341211+00:00
-- url     : https://prove2.me/submissions/70f5e67e-5181-4f49-bfb2-4618dd1b6eb9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_inertiaDegree_field
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relDeg_pow


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
    D.relDeg (s.field L hLK) ⟨s.elt, s.elt_mem_field hLK⟩ = Multiplicative.ofAdd 1 := by
  refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero (s.field L hLK))).1 ?_
  rw [D.relDeg_pow, inertiaDegree_field, ← ofAdd_nsmul, nsmul_one]
  exact s.deg_eq
end GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift
