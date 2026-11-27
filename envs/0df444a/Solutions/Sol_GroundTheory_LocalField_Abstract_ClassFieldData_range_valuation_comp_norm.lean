-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.range_valuation_comp_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:47:01.742049+00:00
-- url     : https://prove2.me/submissions/77d94a58-b8cd-47e4-a041-facb2eafefb1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_range_valuation
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
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution {K L : OpenSubgroup G} (hLK : L ≤ K) :
    ((D.valuation K).comp (norm A (K : Subgroup G) (L : Subgroup G))).range =
      (D.valuation K).range.map (powMonoidHom (relInertiaDegree D.deg K L)) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨D.valuation L a, ?_, (D.valuation_norm hLK a).symm⟩
    rw [range_valuation, ← D.range_valuation L]
    exact ⟨a, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [range_valuation, ← D.range_valuation L] at hy
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, D.valuation_norm hLK a⟩
end GroundTheory.LocalField.Abstract.ClassFieldData
