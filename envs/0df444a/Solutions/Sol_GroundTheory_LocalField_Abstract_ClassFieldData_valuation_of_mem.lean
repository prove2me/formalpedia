-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.valuation_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:59:49.674009+00:00
-- url     : https://prove2.me/submissions/e690e43b-9d06-4f84-9af6-7cce36fbef1c

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_relIndex_eq_mul
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relInertiaDegree_ne_zero
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_valuation_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_of_mem
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti


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
theorem _root_.solution {K L : OpenSubgroup G} (hLK : L ≤ K) {a : A} (ha : a ∈ fixedModule A (K : Subgroup G)) :
    D.valuation L ⟨a, fixedModule_anti hLK ha⟩ =
      D.valuation K ⟨a, ha⟩ ^ relRamificationIndex D.deg K L := by
  refine (ProfiniteInteger.pow_left_inj (D.relInertiaDegree_ne_zero hLK)).1 ?_
  rw [← valuation_norm D hLK, ← pow_mul, ← relIndex_eq_mul hLK]
  have hn : norm A (K : Subgroup G) (L : Subgroup G) ⟨a, fixedModule_anti hLK ha⟩ =
      ⟨a, ha⟩ ^ (L : Subgroup G).relIndex K :=
    Subtype.ext (by rw [coe_norm_of_mem hLK ha]; rfl)
  rw [hn, map_pow]
end GroundTheory.LocalField.Abstract.ClassFieldData
