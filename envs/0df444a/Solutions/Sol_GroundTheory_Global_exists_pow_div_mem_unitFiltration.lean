-- Prove2me | solution 1 for GroundTheory.Global.exists_pow_div_mem_unitFiltration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:59.927817+00:00
-- url     : https://prove2.me/submissions/3f75cf2e-918d-4a54-8f93-16533567f810

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_div_mem_unitFiltration_iff
import Theorems.Thm_GroundTheory_Global_exists_units_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = ε * ϖ ^ d)
include hϖ hnd
namespace GroundTheory.Global
theorem _root_.solution {j : ℕ} (hj : d + 1 ≤ j) {h : 𝒪[K]ˣ}
    (hh : h ∈ unitFiltration K (j + d)) :
    ∃ g ∈ unitFiltration K j, h / g ^ n ∈ unitFiltration K (j + 1 + d) := by
  obtain ⟨b, hb⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hh
  have hg := isUnit_one_add_mul hϖ (n := j) (by omega) ((ε⁻¹ : 𝒪[K]ˣ) * b)
  have hg1 : ((hg.unit : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ j * ((ε⁻¹ : 𝒪[K]ˣ) * b) := by
    rw [IsUnit.unit_spec, add_sub_cancel_left]
  refine ⟨hg.unit, ?_, ?_⟩
  · rw [mem_unitFiltration, hg1, mem_maximalIdeal_pow_iff hϖ]
    exact dvd_mul_right _ _
  · obtain ⟨c, hc⟩ := exists_units_pow_eq hnd hj hg1
    rw [div_mem_unitFiltration_iff, mem_maximalIdeal_pow_iff hϖ]
    exact ⟨-c, by linear_combination hb - hc - ϖ ^ (j + d) * b * (Units.mul_inv ε)⟩
end GroundTheory.Global
