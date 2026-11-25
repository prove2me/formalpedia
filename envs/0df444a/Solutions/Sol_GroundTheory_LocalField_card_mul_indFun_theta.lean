-- Prove2me | solution 1 for GroundTheory.LocalField.card_mul_indFun_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:48.882941+00:00
-- url     : https://prove2.me/submissions/a3f74e0f-203a-4c1e-a37c-5030103118e9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
import Theorems.Thm_GroundTheory_LocalField_sylowCent_le_elemSub
import Theorems.Thm_GroundTheory_LocalField_mk_eq_mk_xIn_iff

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
variable {G : Type u} [Group G]
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
variable {p x}
omit hp
namespace GroundTheory.LocalField
theorem _root_.solution (g : G) :
    (Nat.card (sylowCent p x) : ℂ) * indFun (elemSub p x).subtype (theta p x) g =
      ∑ t : G, if x⁻¹ * (t⁻¹ * g * t) ∈ sylowCent p x then 1 else 0 := by
  set H := elemSub p x
  set P := sylowCent p x
  set Q := H ⧸ sylowCentIn p x
  have hinner : ∀ z : G, ∑ h : H, (if (H.subtype h) = z then theta p x h else 0) =
      if x⁻¹ * z ∈ P then (Nat.card Q : ℂ) else 0 := by
    intro z
    by_cases hz : z ∈ H
    · rw [Finset.sum_eq_single ⟨z, hz⟩]
      · rw [show H.subtype ⟨z, hz⟩ = z from rfl, if_pos rfl, theta]
        have hiff := mk_eq_mk_xIn_iff (p := p) (x := x) ⟨z, hz⟩
        by_cases hc : x⁻¹ * z ∈ P
        · rw [if_pos (hiff.mpr hc), if_pos hc]
        · rw [if_neg (fun h ↦ hc (hiff.mp h)), if_neg hc]
      · intro h _ hne
        rw [if_neg]
        intro h'
        exact hne (Subtype.ext h')
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · rw [Finset.sum_eq_zero, if_neg]
      · intro hP
        apply hz
        have := H.mul_mem (mem_elemSub_self (p := p)) (sylowCent_le_elemSub hP)
        rwa [mul_inv_cancel_left] at this
      · intro h _
        rw [if_neg]
        intro h'
        exact hz (h' ▸ h.2)
  have hcard : (Nat.card H : ℂ) = Nat.card Q * Nat.card P := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (sylowCentIn p x),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylowCent_le_elemSub).toEquiv]
    push_cast
    rfl
  have hQ : (Nat.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hP : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [indFun_apply, Finset.sum_congr rfl fun t _ ↦ hinner _, hcard, ← mul_assoc, mul_inv,
    mul_comm (Nat.card Q : ℂ)⁻¹, ← mul_assoc, mul_inv_cancel₀ hP, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  split_ifs
  · exact inv_mul_cancel₀ hQ
  · simp
end GroundTheory.LocalField
