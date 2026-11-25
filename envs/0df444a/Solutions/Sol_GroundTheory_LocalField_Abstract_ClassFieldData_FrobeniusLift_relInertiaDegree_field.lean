-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift.relInertiaDegree_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:12:08.701448+00:00
-- url     : https://prove2.me/submissions/9b75ff83-bb7e-4b5a-b377-0016e0a89bbb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_inertiaDegree_field
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
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
open GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
namespace GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift
theorem _root_.solution (s : D.FrobeniusLift K) :
    relInertiaDegree D.deg K (s.field L hLK) = s.deg := by
  have h := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G))
    (L := ((s.field L hLK : OpenSubgroup G) : Subgroup G)) (fun x hx => s.field_le hLK hx)
  rw [s.inertiaDegree_field hLK] at h
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K)) h).symm
end GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift
