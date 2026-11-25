-- Prove2me | solution 1 for GroundTheory.LocalField.indFun_zpowers_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:06.003989+00:00
-- url     : https://prove2.me/submissions/68d8908c-511a-4213-9e76-aac3dc1749ab

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal

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
open GroundTheory GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution (s : G) :
    indFun (Subgroup.zpowers s).subtype
      (fun c ↦ if c = ⟨s, Subgroup.mem_zpowers s⟩ then (Nat.card (Subgroup.zpowers s) : ℂ) else 0) =
      classCount s := by
  funext g
  have hN : (Nat.card (Subgroup.zpowers s) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [indFun_apply, classCount, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have hin : ∀ c : Subgroup.zpowers s, (if (Subgroup.zpowers s).subtype c = t⁻¹ * g * t then
      (if c = ⟨s, Subgroup.mem_zpowers s⟩ then (Nat.card (Subgroup.zpowers s) : ℂ) else 0) else 0) =
      if c = ⟨s, Subgroup.mem_zpowers s⟩ then
        (if t⁻¹ * g * t = s then (Nat.card (Subgroup.zpowers s) : ℂ) else 0) else 0 := by
    intro c
    by_cases hc : c = ⟨s, Subgroup.mem_zpowers s⟩
    · subst hc
      simp only [Subgroup.coe_subtype, if_true]
      by_cases h : s = t⁻¹ * g * t
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    · simp [hc]
  rw [Finset.sum_congr rfl fun c _ ↦ hin c, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  split_ifs
  · field_simp
  · simp
end GroundTheory.LocalField
