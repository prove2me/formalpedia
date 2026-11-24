-- Prove2me | solution 1 for GlobalTheory.GallagherLemma.fourier_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:17.81287+00:00
-- url     : https://prove2.me/submissions/33f34e5d-f313-4263-a97b-7a7c5ab5e646

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real
open GlobalTheory GlobalTheory.GallagherLemma
namespace GlobalTheory.GallagherLemma
theorem _root_.solution (l δ : ℝ) (hδ : 0 ≤ δ) (c : ℂ) (w : ℝ) :
    𝓕 ((Set.Ico (l - δ) l).indicator (fun _ => c)) w =
      c * cexp (-(2 * π * w * l : ℝ) * I) * ∫ u in (0 : ℝ)..δ, cexp ((2 * π * w * u : ℝ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : ∀ v : ℝ, cexp (↑(-2 * π * v * w) * I) • (Set.Ico (l - δ) l).indicator (fun _ => c) v =
      (Set.Ico (l - δ) l).indicator (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) * c) v := by
    intro v
    by_cases hv : v ∈ Set.Ico (l - δ) l <;> simp [hv]
  simp_rw [this]
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h2 := intervalIntegral.integral_comp_sub_left (a := 0) (b := δ)
    (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) * c) l
  rw [sub_zero] at h2
  rw [← h2, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [mul_comm _ c, mul_assoc c, ← Complex.exp_add]
  congr 2
  push_cast
  ring
end GlobalTheory.GallagherLemma
