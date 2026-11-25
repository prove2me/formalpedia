-- Prove2me | solution 1 for GroundTheory.LocalField.hasBasis_nhds_one_unitFiltrationUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:41.302764+00:00
-- url     : https://prove2.me/submissions/0712ef39-45e0-4472-92d3-4e7c71476e4e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Theorems.Thm_GroundTheory_LocalField_mem_unitFiltrationUnits_iff
import Theorems.Thm_GroundTheory_LocalField_isOpen_unitFiltrationUnits
import Theorems.Thm_GroundTheory_LocalField_exists_pow_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution :
    (𝓝 (1 : Kˣ)).HasBasis (fun _ ↦ True) (fun n ↦ (unitFiltrationUnits K n : Set Kˣ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [Filter.hasBasis_iff]
  intro t
  constructor
  · intro ht
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at ht
    obtain ⟨t', ht', hsub⟩ := ht
    rw [Units.val_one, IsValuativeTopology.mem_nhds_iff'] at ht'
    obtain ⟨γ, hγ⟩ := ht'
    obtain ⟨n, hn, hlt⟩ := exists_pow_lt hϖ γ.ne_zero
    refine ⟨n, trivial, fun x hx ↦ hsub (hγ ?_)⟩
    exact ((mem_unitFiltrationUnits_iff hn hϖ).mp hx).trans_lt hlt
  · rintro ⟨n, -, hn⟩
    exact Filter.mem_of_superset
      ((isOpen_unitFiltrationUnits n).mem_nhds (Subgroup.one_mem _)) hn
end GroundTheory.LocalField
