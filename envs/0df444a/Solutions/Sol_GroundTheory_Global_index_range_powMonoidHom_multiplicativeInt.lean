-- Prove2me | solution 1 for GroundTheory.Global.index_range_powMonoidHom_multiplicativeInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:56.56524+00:00
-- url     : https://prove2.me/submissions/402f13e1-c4e9-4081-995a-4f74ca9510a6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex

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
omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.Global
theorem _root_.solution (n : ℕ) :
    (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range.index = n := by
  have h : (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range =
      (AddSubgroup.zmultiples (n : ℤ)).toSubgroup := by
    ext x
    rw [MonoidHom.mem_range, Multiplicative.mem_toSubgroup, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.toAdd y, by simp⟩
    · rintro ⟨k, hk⟩
      refine ⟨Multiplicative.ofAdd k, ?_⟩
      apply Multiplicative.toAdd.injective
      simp [hk]
  rw [h, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
  simp
end GroundTheory.Global
