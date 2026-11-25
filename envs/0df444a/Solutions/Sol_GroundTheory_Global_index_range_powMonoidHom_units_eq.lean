-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom_units_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:24.490843+00:00
-- url     : https://prove2.me/submissions/ed0266bc-52a1-448d-a606-5906fed15d82

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_multiplicativeInt
import Theorems.Thm_GroundTheory_Global_range_powMonoidHom_prod

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
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (n : ℕ) :
    (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.index := by
  set e := unitsEquivIntProd hϖ
  have hmap : (powMonoidHom n : Kˣ →* Kˣ).range.map (e : Kˣ →* Multiplicative ℤ × 𝒪[K]ˣ) =
      (powMonoidHom n : Multiplicative ℤ × 𝒪[K]ˣ →* _).range := by
    ext p
    rw [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e.symm q ^ n, ⟨e.symm q, rfl⟩, by simp⟩
  rw [← Subgroup.index_map_equiv _ e, hmap, range_powMonoidHom_prod, Subgroup.index_prod,
    index_range_powMonoidHom_multiplicativeInt]
end GroundTheory.Global
