-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift.field_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:41.737555+00:00
-- url     : https://prove2.me/submissions/a57127f6-12c5-4597-9bcd-8027642c4e03

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
import Theorems.Thm_GroundTheory_LocalField_Abstract_frobeniusClosure_inf_ker


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
    ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker = (L : Subgroup G) ⊓ D.deg.ker :=
  frobeniusClosure_inf_ker D.continuous_deg L.isOpen (mem_normalizer hLK s.mem) s.degree_ne_zero
    s.deg_eq
end GroundTheory.LocalField.Abstract.ClassFieldData.FrobeniusLift
