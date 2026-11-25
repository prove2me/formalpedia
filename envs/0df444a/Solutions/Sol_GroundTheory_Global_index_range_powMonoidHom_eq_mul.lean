-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:44:05.157136+00:00
-- url     : https://prove2.me/submissions/ee99dd7c-f529-4fbe-8e35-a0f971c26718

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_integerUnits_of_eq
import Theorems.Thm_GroundTheory_Global_exists_natCast_eq_unit_mul_pow
import Theorems.Thm_GroundTheory_Global_natCard_rootsOfUnity_eq
import Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_units_eq

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
    ∃ d : ℕ, ord (n : K) = d ∧ (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * Nat.card (rootsOfUnity n K) * Nat.card 𝓀[K] ^ d := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨d, ε, hnd, hord⟩ := exists_natCast_eq_unit_mul_pow hn hϖ
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨d, hord, ?_⟩
  rw [index_range_powMonoidHom_units_eq hϖ, index_range_powMonoidHom_integerUnits_of_eq hϖ hnd,
    natCard_rootsOfUnity_eq hn0, mul_assoc]
end GroundTheory.Global
