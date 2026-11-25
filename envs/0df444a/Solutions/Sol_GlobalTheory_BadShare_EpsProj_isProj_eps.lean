-- Prove2me | solution 1 for GlobalTheory.BadShare.EpsProj.isProj_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:57.319798+00:00
-- url     : https://prove2.me/submissions/f1ac2d2b-b6cc-44cf-94dc-bb9aa693b4d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SubgroupCharacterIdempotentProperties
import Theorems.Thm_GlobalTheory_BadShare_EpsProj_inv_spec
import Theorems.Thm_GlobalTheory_BadShare_EpsProj_eps_mul
import Theorems.Thm_GlobalTheory_BadShare_EpsProj_sum_eps_chi

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
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) : IsProj (eps S χ) := by
  refine ⟨?_, ?_⟩
  · funext x
    unfold conv
    have : ∀ y, eps S χ y * eps S χ (y⁻¹ * x) = eps S χ y * χ y * eps S χ x := by
      intro y
      by_cases hy : S y
      · rw [eps_mul h1 hm c1 cm hy, mul_assoc]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_mul, sum_eps_chi h1 hm c1 cm, one_mul]
  · intro x
    unfold eps
    by_cases hx : S x
    · obtain ⟨hi, ci, hn⟩ := inv_spec h1 hm c1 cm hx
      rw [if_pos hx, if_pos hi, ci, map_div₀, map_inv₀, map_natCast, Complex.inv_eq_conj hn]
    · have : ¬ S x⁻¹ := fun h => hx (by simpa using (inv_spec h1 hm c1 cm h).1)
      rw [if_neg hx, if_neg this, map_zero]
end GlobalTheory.BadShare.EpsProj
