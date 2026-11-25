-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.norm_mem_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:33.467116+00:00
-- url     : https://prove2.me/submissions/4c3d1531-4e68-4a61-ad80-3d0ca37db568

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Unramified
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_mem_units
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
open GroundTheory.LocalField.Abstract.ClassFieldData
open ProfiniteInteger
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)
variable {K L : OpenSubgroup G}
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (hLK : L ≤ K) {a : fixedModule A (L : Subgroup G)} (ha : a ∈ D.units L) :
    norm A (K : Subgroup G) (L : Subgroup G) a ∈ D.units K := by
  rw [D.mem_units, D.valuation_norm hLK, D.mem_units.1 ha, one_pow]
end GroundTheory.LocalField.Abstract.ClassFieldData
