-- Prove2me | solution 1 for GlobalTheory.BadShare.EpsProj.eps_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:38.122499+00:00
-- url     : https://prove2.me/submissions/5dd5fb42-ee04-4e66-8d9c-1445dbb00f0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SubgroupCharacterIdempotentProperties
import Theorems.Thm_GlobalTheory_BadShare_EpsProj_inv_spec

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
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) {u : G} (hu : S u) (y : G) :
    eps S χ (u⁻¹ * y) = χ u * eps S χ y := by
  obtain ⟨hi, ci, -⟩ := inv_spec h1 hm c1 cm hu
  unfold eps
  by_cases hy : S y
  · rw [if_pos hy, if_pos (hm _ _ hi hy), cm _ _ hi hy, ci, mul_inv, inv_inv, mul_div_assoc]
  · have : ¬ S (u⁻¹ * y) := fun h => hy (by simpa using hm _ _ hu h)
    rw [if_neg hy, if_neg this, mul_zero]
end GlobalTheory.BadShare.EpsProj
