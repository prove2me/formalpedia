-- Prove2me | solution 1 for MartingaleHT.FiniteWaiting.theorem_7_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:46:26.300508+00:00
-- url     : https://prove2.me/submissions/818a4e47-66d5-47ab-b885-d8d9766aca27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErlangA_Diffusion_Queue
import Definitions.Def_MartingaleHT_FiniteWaiting_Model
import Theorems.Thm_MartingaleHT_FiniteWaiting_theorem_7_4_martingales

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MartingaleHT.FiniteWaiting
open ErlangA.Diffusion

theorem t74_representation (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (lam μ θ : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A S R : Ω → ℝ → ℝ) (Q : Ω → ℝ → ℕ)
    (hsys : IsFiniteWaitingSystem P n m lam μ θ A S R Q) :
    (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      scaled n Q ω t 0 = scaled n Q ω 0 0 + scaledMart1 n lam A ω t
        - scaledMart2 n μ S Q ω t - scaledMart3 n θ R Q ω t
        + (lam - μ * n) * t / Real.sqrt n
        - (∫ s in (0 : ℝ)..t, (μ * min (scaled n Q ω s 0) 0 + θ * max (scaled n Q ω s 0) 0))
        - scaledBlocked n m lam A Q ω t) := by
  have hr : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  filter_upwards [hsys.eqn] with ω hω t ht
  obtain ⟨i1, i2⟩ := hsys.integrable ω t ht
  have hpt : ∀ s, μ * min (scaled n Q ω s 0) 0 + θ * max (scaled n Q ω s 0) 0 =
      (μ * (min (Q ω s : ℝ) n - n) + θ * max ((Q ω s : ℝ) - n) 0) / Real.sqrt n := by
    intro s
    simp only [scaled]
    rcases le_total (Q ω s : ℝ) n with h | h
    · have h1 : ((Q ω s : ℝ) - n) / Real.sqrt n ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
      rw [min_eq_left h1, max_eq_right h1, min_eq_left h, max_eq_right (by linarith)]
      field_simp
      ring
    · have h1 : 0 ≤ ((Q ω s : ℝ) - n) / Real.sqrt n := div_nonneg (by linarith) hr.le
      rw [min_eq_right h1, max_eq_left h1, min_eq_right h, max_eq_left (by linarith)]
      field_simp
      ring
  have hint : (∫ s in (0 : ℝ)..t,
      (μ * min (scaled n Q ω s 0) 0 + θ * max (scaled n Q ω s 0) 0)) =
      (μ * (busyTime n Q ω t - n * t) + θ * waitTime n Q ω t) / Real.sqrt n := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      ((i1.sub intervalIntegrable_const).const_mul μ) (i2.const_mul θ),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub i1 intervalIntegrable_const]
    simp [busyTime, waitTime]
    ring
  rw [hint]
  have hQ := hω t ht
  simp only [scaled, scaledMart1, scaledMart2, scaledMart3, scaledBlocked]
  rw [hQ]
  field_simp
  ring

end MartingaleHT.FiniteWaiting

open MartingaleHT.FiniteWaiting ErlangA.Diffusion

theorem solution (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (lam μ θ : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A S R : Ω → ℝ → ℝ) (Q : Ω → ℝ → ℕ)
    (hsys : IsFiniteWaitingSystem P n m lam μ θ A S R Q) :
    (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      scaled n Q ω t 0 = scaled n Q ω 0 0 + scaledMart1 n lam A ω t
        - scaledMart2 n μ S Q ω t - scaledMart3 n θ R Q ω t
        + (lam - μ * n) * t / Real.sqrt n
        - (∫ s in (0 : ℝ)..t, (μ * min (scaled n Q ω s 0) 0 + θ * max (scaled n Q ω s 0) 0))
        - scaledBlocked n m lam A Q ω t) ∧
    ∃ ℱ : Filtration ℝ≥0 mΩ, (∀ t, ℱ t = genSigma P n lam μ θ A S R Q t) ∧
      (HasPQV ℱ P (fun t ω => scaledMart1 n lam A ω t) (fun t _ => lam * t / n) ∧
        ∀ t : ℝ≥0, Integrable (fun _ : Ω => lam * t / n) P) ∧
      (HasPQV ℱ P (fun t ω => scaledMart2 n μ S Q ω t) (fun t ω => μ / n * busyTime n Q ω t) ∧
        ∀ t : ℝ≥0, Integrable (fun ω => μ / n * busyTime n Q ω t) P) ∧
      (HasPQV ℱ P (fun t ω => scaledMart3 n θ R Q ω t) (fun t ω => θ / n * waitTime n Q ω t) ∧
        ∀ t : ℝ≥0, Integrable (fun ω => θ / n * waitTime n Q ω t) P) :=
  ⟨t74_representation n hn m lam μ θ P A S R Q hsys,
    theorem_7_4_martingales n hn m lam μ θ P A S R Q hsys⟩
