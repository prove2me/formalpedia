-- Prove2me | solution 1 for OAI.FourierBridge.coupled_log_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:32:19.97457+00:00
-- url     : https://prove2.me/submissions/64f2fee3-6405-4f2b-b556-89a8f58721c8

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_smooth_log_separation
import Theorems.Thm_OAI_FourierBridge_logPhase_sum

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
    (W : ι → ℝ → ℂ) (F V : ℝ → ℂ) (R : ℝ)
    (a y : ι → ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFs : ContDiff ℝ ∞ F)
    (hactive : (∏ j : ι, W j (y j)) ≠ 0 →
      V (∑ j : ι, a j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F (R * Real.exp (∑ j : ι, a j * y j)) =
      ∫ t : ℝ,
        (∏ j : ι, W j (y j) * logPhase t (a j * y j)) *
          (𝓕 (logProfile V F R 1 hVc hVs hFs)) t := by
  classical
  let s : ℝ := ∑ j : ι, a j * y j
  let P : ℂ := ∏ j : ι, W j (y j)
  let b := 𝓕 (logProfile V F R 1 hVc hVs hFs)
  have hsep : V s * F (R * Real.exp s) =
      ∫ t : ℝ, logPhase t s * b t := by
    calc
      V s * F (R * Real.exp s) =
          ∫ t : ℝ, Complex.exp
            ((↑(2 * Real.pi * inner ℝ t s) * Complex.I)) * b t := by
        simpa [b] using
          (smooth_log_separation V F R 1 s hVc hVs hFs)
      _ = ∫ t : ℝ, logPhase t s * b t := by
        apply integral_congr_ae
        filter_upwards [] with t
        congr 1
        simp only [logPhase, Real.inner_apply]
        congr 1
        push_cast
        ring
  have hcut : P * F (R * Real.exp s) =
      P * (V s * F (R * Real.exp s)) := by
    by_cases hP : P = 0
    · simp [hP]
    · rw [hactive (by simpa [P, s] using hP)]
      ring
  calc
    P * F (R * Real.exp s) = P * (V s * F (R * Real.exp s)) := hcut
    _ = P * (∫ t : ℝ, logPhase t s * b t) := by rw [hsep]
    _ = ∫ t : ℝ, P * (logPhase t s * b t) := by
      rw [integral_const_mul]
    _ = ∫ t : ℝ,
          (∏ j : ι, W j (y j) * logPhase t (a j * y j)) * b t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show logPhase t s = ∏ j : ι, logPhase t (a j * y j) by
        simpa [s] using logPhase_sum (Finset.univ : Finset ι) t
          (fun j => a j * y j)]
      rw [Finset.prod_mul_distrib]
      simp only [P]
      ring
end OAI.FourierBridge
