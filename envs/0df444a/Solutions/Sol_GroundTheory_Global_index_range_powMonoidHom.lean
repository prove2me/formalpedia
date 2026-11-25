-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:54:25.637126+00:00
-- url     : https://prove2.me/submissions/a55627b7-4821-45cb-b0c7-e247dacb1e86

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_eq_mul

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
variable {n : ℕ}
namespace GroundTheory.Global
theorem _root_.solution (hn : (n : K) ≠ 0) :
    ((powMonoidHom n : Kˣ →* Kˣ).range.index : ℝ) =
      n * Nat.card (rootsOfUnity n K) * (Nat.card 𝓀[K] : ℝ) ^ ord (n : K) := by
  obtain ⟨d, hd, h⟩ := index_range_powMonoidHom_eq_mul hn
  rw [h, hd, zpow_natCast]
  push_cast
  ring
end GroundTheory.Global
