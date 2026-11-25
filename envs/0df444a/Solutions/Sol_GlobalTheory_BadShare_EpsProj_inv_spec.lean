-- Prove2me | solution 1 for GlobalTheory.BadShare.EpsProj.inv_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:12:46.958157+00:00
-- url     : https://prove2.me/submissions/72f2ba70-cace-41d4-976e-0ef278e4c008

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SubgroupCharacterIdempotentProperties
import Theorems.Thm_GlobalTheory_BadShare_EpsProj_pow_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.EpsProj
variable {G : Type} [Group G] [Fintype G] {S : G → Prop} {χ : G → ℂ}
namespace GlobalTheory.BadShare.EpsProj
theorem _root_.solution (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) :
    S u⁻¹ ∧ χ u⁻¹ = (χ u)⁻¹ ∧ ‖χ u‖ = 1 := by
  have hc : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  have hi : u⁻¹ = u ^ (Fintype.card G - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hc), pow_card_eq_one]
  have hS : S u⁻¹ := by rw [hi]; exact (pow_spec h1 hm c1 cm hu _).1
  refine ⟨hS, ?_, ?_⟩
  · have := cm _ _ hu hS
    rw [mul_inv_cancel, c1] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  · have := (pow_spec h1 hm c1 cm hu (Fintype.card G)).2
    rw [pow_card_eq_one, c1] at this
    exact Complex.norm_eq_one_of_pow_eq_one this.symm hc
end GlobalTheory.BadShare.EpsProj
