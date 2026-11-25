-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.recFrob_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:09:09.538355+00:00
-- url     : https://prove2.me/submissions/5f3d53c2-016b-4860-8e41-3bd7e04f1481

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_congr

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
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution {s t : D.FrobeniusLift K} (h : s.elt = t.elt) :
    D.recFrob L hLK s = D.recFrob L hLK t := by
  unfold recFrob
  rw [FrobeniusLift.field_congr hLK h]
end GroundTheory.LocalField.Abstract.ClassFieldData
