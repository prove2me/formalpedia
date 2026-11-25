-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:34.106877+00:00
-- url     : https://prove2.me/submissions/3b833d8a-9220-406b-952e-cd4fc602ea5e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
variable (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (s : D.FrobeniusLift K) :
    D.reciprocity hLK hax ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = D.recFrob L hLK s := by
  show D.recHom hLK hax ⟨s.elt, s.mem⟩ = _
  rw [recHom_apply]
  apply recFrob_eq_of_mem hLK hax
  have := L.inv_mem (liftOf_spec (D := D) hLK ⟨s.elt, s.mem⟩)
  simpa using this
end GroundTheory.LocalField.Abstract.ClassFieldData
