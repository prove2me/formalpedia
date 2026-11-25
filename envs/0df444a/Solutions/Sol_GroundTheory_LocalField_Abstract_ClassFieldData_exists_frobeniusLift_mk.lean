-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.exists_frobeniusLift_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:11.379518+00:00
-- url     : https://prove2.me/submissions/5c42fdc8-2cc0-4b5d-a70c-710f7ca73e4f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap

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
variable (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
include hLK
omit [IsDiscreteModule G A] [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    ∃ s : D.FrobeniusLift K,
      ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = q := by
  induction q using QuotientGroup.induction_on with
  | H τ => exact ⟨liftOf hLK τ, mk_liftOf hLK τ⟩
end GroundTheory.LocalField.Abstract.ClassFieldData
