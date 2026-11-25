-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.reciprocity_mk_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:17.146137+00:00
-- url     : https://prove2.me/submissions/233b8ee9-1d3d-4496-981a-009ff2fb3c60

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ReciprocityMap
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_reciprocity_mk
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mk_norm_eq_recFrob


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
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK hax ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (QuotientGroup.mk (norm A (K : Subgroup G)
        ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) :
          tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  rw [reciprocity_mk, D.mk_norm_eq_recFrob hLK hax s hπ]
end GroundTheory.LocalField.Abstract.ClassFieldData
