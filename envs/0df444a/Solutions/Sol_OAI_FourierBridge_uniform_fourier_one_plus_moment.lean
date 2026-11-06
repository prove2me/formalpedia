-- Prove2me | solution 1 for OAI.FourierBridge.uniform_fourier_one_plus_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:32:58.368584+00:00
-- url     : https://prove2.me/submissions/fce9ef0a-c450-4822-9c8d-2ab0df43ac3a

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_uniform_fourier_coefficient_moment

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge
namespace OAI.FourierBridge
theorem _root_.solution
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) ≤
      (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa using b.integrable_pow_mul volume 0
  have hIJ : Integrable (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hIrhs : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hpow := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hintegral :
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
    calc
      _ ≤ ∫ t : ℝ, (2 : ℝ) ^ J *
          (‖b t‖ + ‖t‖ ^ J * ‖b t‖) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (by intro t; positivity))
          hIrhs (Filter.Eventually.of_forall hpoint)
      _ = (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
        rw [integral_const_mul, integral_add hI0 hIJ]
  have hbound0 := uniform_fourier_coefficient_moment g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hboundJ := uniform_fourier_coefficient_moment g J S C hS hC hsource
  calc
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        S * ((2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖))) :=
      mul_le_mul_of_nonneg_left hintegral hS
    _ = (2 : ℝ) ^ J *
        (S * (∫ t : ℝ, ‖b t‖) +
          S * (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by ring
    _ ≤ (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · simpa [coefficientMomentBound, b] using hbound0
      · simpa [coefficientMomentBound, b] using hboundJ
end OAI.FourierBridge
