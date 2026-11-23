-- Prove2me | solution 1 for GroundTheory.LocalField.mem_unitFiltrationUnits_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:12.562792+00:00
-- url     : https://prove2.me/submissions/0dc19ded-355f-417a-886c-2decd75864e7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Theorems.Thm_GroundTheory_LocalField_mem_range_unitsIncl_iff
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
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    {x : Kˣ} :
    x ∈ unitFiltrationUnits K n ↔ valuation K ((x : K) - 1) ≤ valuation K (ϖ : K) ^ n := by
  have hset := hϖ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (v := valuation K) n
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) := hu
    rw [hset] at this
    simpa using this
  · intro h
    have hϖ1 : valuation K (ϖ : K) < 1 :=
      valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
    have hlt : valuation K ((x : K) - 1) < 1 :=
      h.trans_lt (pow_lt_one₀ zero_le hϖ1 (by omega))
    have hx1 : valuation K (x : K) = 1 := by
      have := (valuation K).map_one_add_of_lt hlt
      simpa using this
    obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr (by
      rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one]; exact hx1)
    refine ⟨u, ?_, rfl⟩
    show ((u : 𝒪[K]) - 1 : 𝒪[K]) ∈ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    rw [hset]
    simpa using h
end GroundTheory.LocalField
