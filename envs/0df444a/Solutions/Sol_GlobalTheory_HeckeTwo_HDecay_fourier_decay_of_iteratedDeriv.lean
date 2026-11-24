-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.fourier_decay_of_iteratedDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:21:50.362922+00:00
-- url     : https://prove2.me/submissions/ac28795b-70a5-4f69-bf17-167df32c6b47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hi : ∀ n : ℕ, Integrable (iteratedDeriv n f)) (N : ℕ) :
    ∃ C : ℝ, ∀ ν : ℝ, ‖𝓕 f ν‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  have hbound : ∀ (u : ℝ → ℂ) (ν : ℝ), ‖𝓕 u ν‖ ≤ ∫ t, ‖u t‖ := by
    intro u ν
    rw [Real.fourier_real_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext t
    simp [Circle.norm_smul]
  set A := ∫ t, ‖f t‖
  set B := ∫ t, ‖iteratedDeriv N f t‖
  refine ⟨2 ^ N * (A + B / (2 * Real.pi) ^ N), fun ν => ?_⟩
  have h1 : ‖𝓕 f ν‖ ≤ A := hbound f ν
  have h2 : (2 * Real.pi) ^ N * (|ν| ^ N * ‖𝓕 f ν‖) ≤ B := by
    have := hbound (iteratedDeriv N f) ν
    rw [Real.fourier_iteratedDeriv (N := ⊤) hf (fun n _ => hi n) le_top] at this
    have e : ‖(2 * (Real.pi : ℂ) * I * (ν : ℂ)) ^ N • 𝓕 f ν‖ = (2 * Real.pi) ^ N * (|ν| ^ N * ‖𝓕 f ν‖) := by
      rw [norm_smul, norm_pow]
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        abs_of_pos Real.pi_pos, mul_one]
      ring
    rw [e] at this
    exact this
  have hx : 0 ≤ |ν| := abs_nonneg ν
  have hq : 0 ≤ ‖𝓕 f ν‖ := norm_nonneg _
  have hpi : 0 < (2 * Real.pi) ^ N := by positivity
  have h3 : |ν| ^ N * ‖𝓕 f ν‖ ≤ B / (2 * Real.pi) ^ N := by
    rw [le_div_iff₀ hpi]; linarith
  have h4 : (1 + |ν|) ^ N ≤ 2 ^ N * (1 + |ν| ^ N) := by
    rcases le_total 1 |ν| with h | h
    · calc (1 + |ν|) ^ N ≤ (2 * |ν|) ^ N := by gcongr; linarith
        _ = 2 ^ N * |ν| ^ N := by rw [mul_pow]
        _ ≤ 2 ^ N * (1 + |ν| ^ N) := by gcongr; linarith
    · calc (1 + |ν|) ^ N ≤ (2 : ℝ) ^ N := by gcongr; linarith
        _ ≤ 2 ^ N * (1 + |ν| ^ N) := by
          have : 0 ≤ |ν| ^ N := by positivity
          nlinarith [pow_pos (two_pos : (0:ℝ) < 2) N]
  have hpos : 0 < (1 + |ν|) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖𝓕 f ν‖ * (1 + |ν|) ^ N ≤ ‖𝓕 f ν‖ * (2 ^ N * (1 + |ν| ^ N)) := by gcongr
    _ = 2 ^ N * (‖𝓕 f ν‖ + |ν| ^ N * ‖𝓕 f ν‖) := by ring
    _ ≤ 2 ^ N * (A + B / (2 * Real.pi) ^ N) := by gcongr
end GlobalTheory.HeckeTwo.HDecay
