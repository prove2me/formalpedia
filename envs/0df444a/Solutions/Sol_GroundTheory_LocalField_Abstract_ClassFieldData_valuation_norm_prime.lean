-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.valuation_norm_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:23:32.48019+00:00
-- url     : https://prove2.me/submissions/0edf1cdd-9e8a-4a0d-b791-0e08f6082b4e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Multiplicative
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_relInertiaDegree_field
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm


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
theorem _root_.solution (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    D.valuation K (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) =
      Multiplicative.ofAdd (s.deg : ℤ̂) := by
  rw [D.valuation_norm (s.field_le hLK), hπ, FrobeniusLift.relInertiaDegree_field, ← ofAdd_nsmul,
    nsmul_one]
end GroundTheory.LocalField.Abstract.ClassFieldData
