-- Prove2me | solution 1 for GroundTheory.Global.pow_mem_unitFiltration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:15.001899+00:00
-- url     : https://prove2.me/submissions/099393c9-dea1-4c1e-b195-26e78081a08e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
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
theorem _root_.solution {j : ℕ} (hj : d + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) : u ^ n ∈ unitFiltration K (j + d) := by
  obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hu
  obtain ⟨c, hc⟩ := exists_units_pow_eq hnd hj ha
  rw [mem_unitFiltration, hc, add_sub_cancel_left, mem_maximalIdeal_pow_iff hϖ]
  exact dvd_mul_right _ _
end GroundTheory.Global
