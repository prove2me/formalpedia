-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.relIndex_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:15:10.695972+00:00
-- url     : https://prove2.me/submissions/30b66f04-c31c-4d85-8878-b4fb1be1fe4d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_relIndex_sup_of_le_normalizer
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_P2M_GroundTheory_Variant__N1_relIndex_sup_of_le_normalizer_7514b13ff881
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
variable {G : Type*} [Group G]
variable (d : G →* Multiplicative ℤ̂)
variable {d}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {K L : Subgroup G} (hLK : L ≤ K) :
    L.relIndex K = relRamificationIndex d K L * relInertiaDegree d K L := by
  have hP : L ⊔ (d.ker ⊓ K) ≤ K := sup_le hLK inf_le_right
  rw [← Subgroup.relIndex_mul_relIndex L (L ⊔ (d.ker ⊓ K)) K le_sup_left hP]
  congr 1
  · rw [relRamificationIndex]
    refine relIndex_sup_of_le_normalizer ?_
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgK : g ∈ K := hLK hg
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, map_mul, map_inv]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, K.mul_mem (K.mul_mem hgK h2) (K.inv_mem hgK)⟩
      rw [h1, mul_one, mul_inv_cancel]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : d x = (d g)⁻¹ * (d g * d x * (d g)⁻¹) * d g := by group
        rw [this, h1]; group
      · have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [this]
        exact K.mul_mem (K.mul_mem (K.inv_mem hgK) h2) hgK
  · rw [relInertiaDegree, ← Subgroup.relIndex_comap, Subgroup.comap_map_eq,
      ← Subgroup.inf_relIndex_right (L ⊔ d.ker) K]
    congr 1
    refine le_antisymm (le_inf (sup_le_sup_left inf_le_left L) hP) ?_
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx1
    have hzK : z ∈ K := by
      have := K.mul_mem (K.inv_mem (hLK hy)) hx2
      simpa using this
    exact Subgroup.mul_mem_sup hy (Subgroup.mem_inf.2 ⟨hz, hzK⟩)
end GroundTheory.LocalField.Abstract
