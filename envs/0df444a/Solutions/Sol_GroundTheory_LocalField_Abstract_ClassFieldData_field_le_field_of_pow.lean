-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.field_le_field_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:51:19.593591+00:00
-- url     : https://prove2.me/submissions/d9172db8-ff37-4086-b600-7ded124110d1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Theorems.Thm_GroundTheory_LocalField_Abstract_frobeniusClosure_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_le_frobeniusClosure


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
theorem _root_.solution (s1 s2 : D.FrobeniusLift K) (k : ℕ) (h2 : s2.elt = s1.elt ^ k) :
    s2.field L hLK ≤ s1.field L hLK := by
  intro x hx
  refine frobeniusClosure_le (s1.field L hLK).isClosed ?_ le_frobeniusClosure hx
  rw [h2]
  exact Subgroup.pow_mem _ (s1.elt_mem_field hLK) k
end GroundTheory.LocalField.Abstract.ClassFieldData
