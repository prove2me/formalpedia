-- Prove2me | solution 1 for OAI.FourierBridge.coupled_log_separation_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:29.940086+00:00
-- url     : https://prove2.me/submissions/b39ec5bc-6441-4dad-9842-ddc5be801106

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_profileMomentConstant_nonneg
import Theorems.Thm_OAI_FourierBridge_coefficientMomentBound_nonneg
import Theorems.Thm_OAI_FourierBridge_coupled_cutoff_active
import Theorems.Thm_OAI_FourierBridge_exists_complex_smooth_cutoff_with_derivative_bounds
import Theorems.Thm_OAI_FourierBridge_schwartzDerivativeDecayConstant_nonneg
import Theorems.Thm_OAI_FourierBridge_schwartz_derivative_decay_finite
import Theorems.Thm_OAI_FourierBridge_coupled_log_separation
import Theorems.Thm_OAI_FourierBridge_coupled_log_coefficient_bound

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
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : 𝓢(ℝ, ℂ)) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ (b : ℝ → ℝ → ℂ) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 ≤ R →
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) * logPhase t (a j * y j)) *
              b R t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b R t‖) ≤ C := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let L : ℝ := T + 1
  let m : ℝ := Real.exp (-L)
  let H : ℝ := Real.exp L
  let CF : ℝ := schwartzDerivativeDecayConstant F (A + K) K
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -L ≤ 0 by linarith))
  have hH : 1 ≤ H := by
    dsimp [H]
    simpa using (Real.exp_le_exp.mpr hL)
  have hCF : 0 ≤ CF := schwartzDerivativeDecayConstant_nonneg F (A + K) K
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let b : ℝ → ℝ → ℂ :=
    fun R t => (𝓕 (logProfile V F R 1 hVc hVs (F.smooth ⊤))) t
  let P : ℝ := profileMomentConstant K L H CW CF
  let B : ℝ := (2 : ℝ) ^ J *
    (coefficientMomentBound 0 P + coefficientMomentBound J P)
  let C : ℝ := B / m ^ (A + K)
  have hP : 0 ≤ P :=
    profileMomentConstant_nonneg K L H CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (coefficientMomentBound_nonneg 0 P hP)
        (coefficientMomentBound_nonneg J P hP))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨b, C, hC, ?_⟩
  intro R hR
  constructor
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_log_separation W F V R a y
      hVc hVs (F.smooth ⊤) hactive
  · have hbound := coupled_log_coefficient_bound V F R m H L CW CF A J
      hVc hVs (F.smooth ⊤) hR hm hm1 hH hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa [m, H, L, K] using hwindow)
      (by intro j hj i hi u hu
          exact schwartz_derivative_decay_finite F A K j i u
            (by simpa [K] using hj) hi hu)
    have hmPow : 0 < m ^ (A + K) := pow_pos hm _
    dsimp [C]
    apply (le_div_iff₀ hmPow).mpr
    simpa [B, P, b, K, m, H, L, CF,
      mul_comm, mul_left_comm, mul_assoc] using hbound
end OAI.FourierBridge
