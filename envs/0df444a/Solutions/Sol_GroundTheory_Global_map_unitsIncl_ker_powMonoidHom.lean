-- Prove2me | solution 1 for GroundTheory.Global.map_unitsIncl_ker_powMonoidHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:55.64933+00:00
-- url     : https://prove2.me/submissions/3f2a51b5-2f78-433b-8c96-2eaf75e608eb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_LocalField_mem_range_unitsIncl_iff


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
theorem _root_.solution (hn : n ≠ 0) :
    (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker.map (unitsIncl K) = rootsOfUnity n K := by
  ext x
  rw [Subgroup.mem_map, mem_rootsOfUnity]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hu
    rw [← map_pow, hu, map_one]
  · intro hx
    have hv : normalizedValuation K (x : K) ^ n = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, map_one]
    have hv1 : normalizedValuation K (x : K) = 1 := by
      have hne : normalizedValuation K (x : K) ≠ 0 := by simp
      have hlog := congrArg WithZero.log hv
      rw [WithZero.log_pow, WithZero.log_one, smul_eq_zero] at hlog
      rcases hlog with h | h
      · exact absurd h hn
      · rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
    obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr hv1
    refine ⟨u, ?_, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    apply unitsIncl_injective
    rw [map_pow, hx, map_one]
end GroundTheory.Global
