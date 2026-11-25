-- Prove2me | solution 1 for GroundTheory.Global.exists_one_add_uniformizer_pow_mul_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:16:29.478372+00:00
-- url     : https://prove2.me/submissions/e7dfbc2a-4115-4c52-9cb4-8ac9635af42d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_exists_one_add_pow_eq

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
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] hϖ
namespace GroundTheory.Global
theorem _root_.solution {j : ℕ} (hj : d + 1 ≤ j) (a : 𝒪[K]) :
    ∃ c : 𝒪[K], (1 + ϖ ^ j * a) ^ n = 1 + ϖ ^ (j + d) * (ε * a + ϖ * c) := by
  obtain ⟨c₀, hc₀⟩ := exists_one_add_pow_eq (ϖ ^ j * a) n
  obtain ⟨t, rfl⟩ : ∃ t, j = d + 1 + t := ⟨j - (d + 1), by omega⟩
  refine ⟨ϖ ^ t * a ^ 2 * c₀, ?_⟩
  rw [hc₀, hnd]
  ring
end GroundTheory.Global
