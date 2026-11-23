-- Prove2me | solution 1 for GroundTheory.LocalField.tendsto_zero_iff_valBall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:55.017682+00:00
-- url     : https://prove2.me/submissions/669e7067-d32f-47b9-b3e0-5f1daef5377b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_valBall_mem_nhds
import Theorems.Thm_GroundTheory_LocalField_exists_pow_lt
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {ι : Type*} {l : Filter ι} {f : ι → K} :
    Tendsto f l (𝓝 0) ↔ ∀ N : ℤ, ∀ᶠ i in l, f i ∈ valBall K N := by
  constructor
  · intro hf N
    exact hf (valBall_mem_nhds N)
  · intro hf
    rw [(IsValuativeTopology.hasBasis_nhds_zero K).tendsto_right_iff]
    intro γ _
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    obtain ⟨n, -, hn⟩ := exists_pow_lt hϖ γ.ne_zero
    filter_upwards [hf n] with i hi
    refine lt_of_le_of_lt ?_ hn
    rw [← map_pow, ← normalizedValuation_le_iff, map_pow, normalizedValuation_uniformizer hϖ,
      ← WithZero.exp_nsmul]
    simpa [mem_valBall] using hi
end GroundTheory.LocalField
