-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.valuation_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:34.225996+00:00
-- url     : https://prove2.me/submissions/932f84ee-4275-4a63-8953-1f9ae6e0473c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_pow

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
open GroundTheory.LocalField.Abstract.ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (K : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) (z : Multiplicative ℤ̂) :
    D.valuation K a = z ↔ D.val (norm A ⊤ (K : Subgroup G) a) = z ^ inertiaDegree D.deg K := by
  rw [← ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K), valuation_pow]
end GroundTheory.LocalField.Abstract.ClassFieldData
