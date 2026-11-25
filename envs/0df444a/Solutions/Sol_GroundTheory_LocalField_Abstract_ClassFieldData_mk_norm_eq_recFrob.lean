-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.mk_norm_eq_recFrob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:37:26.643859+00:00
-- url     : https://prove2.me/submissions/933d19d1-4a40-413b-b8d0-ac3bbb8a137e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_inf_ker
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mk_norm_eq_primeNorm

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
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hax : ClassFieldAxiom G A) (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.recFrob L hLK s :=
  D.mk_norm_eq_primeNorm hax (s.field_le hLK) hLK (fun x hx => by
    have := (s.field_inf_ker hLK).le hx
    exact this.1) hπ
end GroundTheory.LocalField.Abstract.ClassFieldData
