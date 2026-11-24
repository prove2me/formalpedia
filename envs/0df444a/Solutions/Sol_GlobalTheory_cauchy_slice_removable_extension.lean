-- Prove2me | solution 1 for GlobalTheory.cauchy_slice_removable_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:00.464079+00:00
-- url     : https://prove2.me/submissions/50b32aa2-d4bf-4f6f-bfc1-f4e67c0ba916

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CauchySliceEqRemovableExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r M : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.ball z₀ (2 * r) ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z ∈ Metric.ball z₀ (2 * r), z k ≠ 0 → ‖f z‖ ≤ M) → ∀ z ∈ Metric.ball z₀ r, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) = (if z k = 0 then limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) (fun t => f (Function.update z k t)) else f z) := by
  intro n U k f z₀ r M hr hz₀ _hU hball hd hM z hz
  set s : ℂ → ℂ := fun t => f (Function.update z k t) with hs_def

  have hupd : Differentiable ℂ (fun t : ℂ => Function.update z k t) :=
    (contDiff_update (𝕜 := ℂ) 1 z k).differentiable (by norm_num)
  have hzdist : ∀ j, ‖z j - z₀ j‖ < r := by
    intro j
    have h1 : dist z z₀ < r := hz
    rw [dist_pi_lt_iff hr] at h1
    simpa [dist_eq_norm] using h1 j
  have hzk : ‖z k‖ < r := by simpa [hz₀] using hzdist k
  have hmem : ∀ t : ℂ, ‖t‖ < 2 * r → Function.update z k t ∈ Metric.ball z₀ (2 * r) := by
    intro t ht
    rw [Metric.mem_ball, dist_pi_lt_iff (by linarith)]
    intro j
    by_cases hj : j = k
    · subst hj
      simpa [dist_eq_norm, hz₀] using ht
    · rw [Function.update_of_ne hj, dist_eq_norm]
      linarith [hzdist j]
  have hsd : DifferentiableOn ℂ s (Metric.ball (0 : ℂ) (2 * r) \ {0}) := by
    refine hd.comp hupd.differentiableOn ?_
    intro t ht
    have ht1 : ‖t‖ < 2 * r := by simpa using ht.1
    have ht2 : t ≠ 0 := ht.2
    exact ⟨hball (hmem t ht1), by simpa using ht2⟩
  have hsb : BddAbove (norm ∘ s '' (Metric.ball (0 : ℂ) (2 * r) \ {0})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have ht1 : ‖t‖ < 2 * r := by simpa using ht.1
    have ht2 : t ≠ 0 := ht.2
    exact hM _ (hmem t ht1) (by simpa using ht2)
  have hg := Complex.differentiableOn_update_limUnder_of_bddAbove
    (Metric.ball_mem_nhds (0 : ℂ) (by linarith)) hsd hsb
  set g := Function.update s 0 (limUnder (𝓝[≠] (0 : ℂ)) s) with hg_def
  have hgc : DifferentiableOn ℂ g (Metric.closedBall 0 r) :=
    hg.mono (Metric.closedBall_subset_ball (by linarith))
  have hw : z k ∈ Metric.ball (0 : ℂ) r := by simpa using hzk
  have hcauchy := (hgc.mono closure_ball_subset_closedBall).diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hcongr : (∮ t in C(0, r), (t - z k)⁻¹ • g t) = (∮ t in C(0, r), (t - z k)⁻¹ • s t) := by
    refine circleIntegral.integral_congr hr.le ?_
    intro t ht
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at ht
      linarith
    simp only [hg_def, Function.update_of_ne ht0]
  rw [hcongr] at hcauchy
  rw [hcauchy]
  by_cases h0 : z k = 0
  · rw [if_pos h0, h0, hg_def, Function.update_self]
  · rw [if_neg h0, hg_def, Function.update_of_ne h0, hs_def]
    simp only [Function.update_eq_self]
end GlobalTheory
