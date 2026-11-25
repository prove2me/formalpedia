-- Prove2me | solution 1 for GlobalTheory.BadShare.EpsProj.mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:43:59.457818+00:00
-- url     : https://prove2.me/submissions/11774bec-eea0-4f12-b502-6c068192a6df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SubgroupCharacterIdempotentProperties
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
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (h1 : S 1) (hm : ∀ u v, S u → S v → S (u * v)) (c1 : χ 1 = 1)
    (cm : ∀ u v, S u → S v → χ (u * v) = χ u * χ v) (x : M) :
    x ∈ LinearMap.range (op ρ (eps S χ)) ↔ ∀ u, S u → ρ u x = χ u • x := by
  constructor
  · rintro ⟨z, rfl⟩ u hu
    simp only [op, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun y => ?_
    have := eps_mul h1 hm c1 cm hu (u * y)
    rw [inv_mul_cancel_left] at this
    simp only [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, smul_smul]
    rw [← this]
  · intro h
    refine ⟨x, ?_⟩
    simp only [op, LinearMap.sum_apply, LinearMap.smul_apply]
    have : ∀ y, eps S χ y • ρ y x = (eps S χ y * χ y) • x := by
      intro y
      by_cases hy : S y
      · rw [h y hy, smul_smul]
      · have : eps S χ y = 0 := by simp [eps, hy]
        simp [this]
    simp_rw [this]
    rw [← Finset.sum_smul, sum_eps_chi h1 hm c1 cm, one_smul]
end GlobalTheory.BadShare.EpsProj
