-- Prove2me | solution 1 for GroundTheory.LocalField.val_image_unitFiltrationUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:21.309039+00:00
-- url     : https://prove2.me/submissions/ef4fdb03-c89e-48fe-bd71-54d39f190324

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Theorems.Thm_GroundTheory_LocalField_mem_unitFiltrationUnits_iff
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
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ((↑) : Kˣ → K) '' (unitFiltrationUnits K n : Set Kˣ) =
      {y : K | valuation K (y - 1) ≤ valuation K (ϖ : K) ^ n} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_unitFiltrationUnits_iff hn hϖ).mp hx
  · intro hy
    have hϖ1 : valuation K (ϖ : K) < 1 :=
      valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : valuation K ((0 : K) - 1) ≤ valuation K (ϖ : K) ^ n := hy
      simp only [zero_sub, Valuation.map_neg, map_one] at this
      exact (pow_lt_one₀ zero_le hϖ1 (by omega)).not_ge this
    exact ⟨Units.mk0 y hy0, (mem_unitFiltrationUnits_iff hn hϖ).mpr hy, rfl⟩
end GroundTheory.LocalField
