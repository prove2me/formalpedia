-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.pairing_convolution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:55:21.683509+00:00
-- url     : https://prove2.me/submissions/a9c6c1eb-552d-4fed-9220-67a11ba88117

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {G K k : ℝ → ℂ} (hG : Continuous G) (hK : Integrable K)
    (hk : Integrable k) (hKc : HasCompactSupport K) (hkc : HasCompactSupport k) :
    Integrable (fun s => K s * ∫ t, G (s + t) * k t) ∧
      ∫ u, G u * (K ⋆[mul ℂ ℂ] k) u = ∫ s, K s * ∫ t, G (s + t) * k t := by
  obtain ⟨M, hM⟩ := (hKc.isCompact.add hkc.isCompact).exists_bound_of_continuousOn hG.continuousOn
  set Ψ : ℝ × ℝ → ℂ := fun p => G p.1 * (K p.2 * k (p.1 - p.2)) with hΨ
  have hconv : Integrable (fun p : ℝ × ℝ => mul ℂ ℂ (K p.2) (k (p.1 - p.2))) (volume.prod volume) :=
    hK.convolution_integrand (mul ℂ ℂ) hk
  have hΨi : Integrable Ψ (volume.prod volume) := by
    refine Integrable.mono' (hconv.norm.const_mul M) ?_ (Eventually.of_forall fun p => ?_)
    · exact (hG.comp continuous_fst).aestronglyMeasurable.mul hconv.aestronglyMeasurable
    · simp only [hΨ, mul_apply', norm_mul]
      by_cases h : K p.2 * k (p.1 - p.2) = 0
      · rw [mul_eq_zero] at h
        rcases h with h | h <;> simp [h]
      · rw [mul_eq_zero, not_or] at h
        have hp : p.1 ∈ tsupport K + tsupport k :=
          ⟨p.2, subset_tsupport _ h.1, p.1 - p.2, subset_tsupport _ h.2, by ring⟩
        have := hM p.1 hp
        calc ‖G p.1‖ * (‖K p.2‖ * ‖k (p.1 - p.2)‖) ≤ M * (‖K p.2‖ * ‖k (p.1 - p.2)‖) :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = _ := rfl
  have hswap := integral_integral_swap (f := fun u s => Ψ (u, s)) hΨi
  have hinner : ∀ s, ∫ u, Ψ (u, s) = K s * ∫ t, G (s + t) * k t := by
    intro s
    rw [← integral_const_mul, ← integral_add_left_eq_self (fun u => Ψ (u, s)) s]
    congr 1; funext t; simp only [hΨ]; rw [add_sub_cancel_left]; ring
  refine ⟨?_, ?_⟩
  · have := hΨi.integral_prod_right
    simpa only [hinner] using this
  · calc ∫ u, G u * (K ⋆[mul ℂ ℂ] k) u = ∫ u, ∫ s, Ψ (u, s) := by
          congr 1; funext u
          rw [convolution_mul, ← integral_const_mul]
      _ = ∫ s, ∫ u, Ψ (u, s) := hswap
      _ = ∫ s, K s * ∫ t, G (s + t) * k t := by simp only [hinner]
end GroundTheory.Automorphic.LineKernel
