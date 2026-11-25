-- Prove2me | solution 1 for GroundTheory.Global.hasHerbrandQuotient_of_cycHerbrand_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:21.183038+00:00
-- url     : https://prove2.me/submissions/25275f83-7713-4a64-8768-2c99e6f6153e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrandInfinite
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.GroupCoh
open scoped NumberField.LiesOver
open GroundTheory GroundTheory.Global
variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
namespace GroundTheory.Global
theorem _root_.solution {ρ : Representation k G V} {σ : G}
    (h : cycHerbrand ρ σ ≠ 0) : HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) := by
  rw [cycHerbrand_eq] at h
  have h0 : Nat.card (CycTateZero ρ σ) ≠ 0 := fun h' ↦ h (by rw [h', Nat.cast_zero, zero_div])
  have h1 : Nat.card (CycTateNegOne ρ σ) ≠ 0 := fun h' ↦ h (by rw [h', Nat.cast_zero, div_zero])
  exact ⟨Nat.finite_of_card_ne_zero h0, Nat.finite_of_card_ne_zero h1⟩
end GroundTheory.Global
