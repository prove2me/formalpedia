-- Prove2me | solution 1 for GlobalTheory.SmoothForms.hasLog_of_isLieData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:06:54.611585+00:00
-- url     : https://prove2.me/submissions/7c884a9d-00aa-4868-ad46-aebf7d0feb0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_HasSmoothLogNearOneOfIsUnitaryLieExpData
import Theorems.Thm_GlobalTheory_SmoothForms_anti_map_exp
import Theorems.Thm_GlobalTheory_SmoothForms_exists_local_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
namespace GlobalTheory.SmoothForms
theorem _root_.solution (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G)
    (H : IsLieData σ j s) : HasLog σ j := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  haveI : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  obtain ⟨l, h1, h2, h3⟩ := exists_local_log 𝔸
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 H.inj)
  have hp' : ∀ Y, p (j Y) = Y := fun Y => LinearMap.congr_fun hp Y
  have hl : l 1 = 0 := by simpa using h3.self_of_nhds
  refine ⟨fun h => p (l h), (LinearMap.toContinuousLinearMap p).contDiff.contDiffAt.comp 1 h1, ?_, ?_⟩
  · have ht : Filter.Tendsto (fun h => -σ (l h)) (𝓝 1) (𝓝 0) := by
      have := (σ.continuous_of_finiteDimensional.continuousAt.comp h1.continuousAt).neg.tendsto
      have e : (-(⇑σ ∘ l)) 1 = 0 := by simp [hl]
      rw [e] at this
      exact this
    filter_upwards [h2, ht.eventually h3] with h ha hb hu
    have e1 : NormedSpace.exp (σ (l h)) * h = 1 := by
      rw [← anti_map_exp σ H.anti H.one, ha, hu]
    have e2 : NormedSpace.exp (-σ (l h)) * NormedSpace.exp (σ (l h)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel, NormedSpace.exp_zero]
    have e3 : NormedSpace.exp (-σ (l h)) = h := by
      rw [← mul_one (NormedSpace.exp (-σ (l h))), ← e1, ← mul_assoc, e2, one_mul]
    rw [e3] at hb
    obtain ⟨Y, hY⟩ := (H.skew (l h)).1 (neg_eq_iff_eq_neg.1 hb.symm)
    rw [← hY, hp', hY, ha]
  · have ht : Filter.Tendsto j (𝓝 0) (𝓝 0) := by
      simpa using j.continuous_of_finiteDimensional.tendsto 0
    filter_upwards [ht.eventually h3] with X hX
    rw [hX, hp']
end GlobalTheory.SmoothForms
