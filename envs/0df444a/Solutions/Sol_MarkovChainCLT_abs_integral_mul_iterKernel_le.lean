-- Prove2me | solution 1 for MarkovChainCLT.abs_integral_mul_iterKernel_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T00:33:30.250463+00:00
-- url     : https://prove2.me/submissions/0452e2ad-290d-460d-a821-9b325aebc65f

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Theorems.Thm_MarkovChainCLT_integral_mul_coord_eq
import Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_geom_le
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 4000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : 4 * ρ ≤ 1 / 4) (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (r : X → ℝ) (hr : Measurable r) (Br : ℝ) (hBr : ∀ x, |r x| ≤ Br)
    (hmean : ∫ x, r x ∂π = 0) (d : ℕ) :
    |∫ x, r x * (∫ y, r y ∂(iterKernel P d x)) ∂π|
      ≤ (1 / 2 : ℝ) ^ (d / N) * ∫ x, (r x) ^ 2 ∂π := by
  classical
  set ν : Measure (ℕ → X) := chainMeasure P π with hν
  set S : ℝ := ∫ x, (r x) ^ 2 ∂π with hS
  have hS0 : 0 ≤ S := integral_nonneg (fun x => sq_nonneg _)
  set Q : ℕ → X → ℝ := fun d x => ∫ y, r y ∂(iterKernel P d x) with hQ
  have hQm : ∀ d, Measurable (Q d) :=
    fun d => (hr.stronglyMeasurable.integral_kernel (κ := iterKernel P d)).measurable
  have hQB : ∀ d x, |Q d x| ≤ Br := by
    intro d x
    rw [hQ]
    refine le_trans abs_integral_le_integral_abs ?_
    have h1 : Integrable (fun z => |r z|) (iterKernel P d x) :=
      ⟨(continuous_abs.measurable.comp hr).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := Br) (ae_of_all _ (fun z => by simpa using hBr z))⟩
    have h2 := integral_mono h1 (integrable_const Br) (fun z => hBr z)
    simpa using h2
  set a : ℕ → ℝ := fun d => (1 / 2 : ℝ) ^ (d / N) with ha
  have ha0 : ∀ d, 0 ≤ a d := by intro d; rw [ha]; positivity
  have hapos : ∀ d, 0 < a d := by intro d; rw [ha]; positivity
  -- the covariance bound
  set c : ℕ → ℝ := fun d => ∫ x, r x * Q d x ∂π with hc
  show |c d| ≤ a d * S
  · have hgeo := integral_sq_iterKernel_geom_le P π hinv N hN ρ hρ0 hρ hrate r hr Br hBr hmean d
    have hα : (0 : ℝ) < a d := hapos d
    have hint1 : Integrable (fun x => r x * Q d x) π := by
      refine ⟨(hr.mul (hQm d)).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := Br ^ 2) (ae_of_all _ (fun z => ?_))⟩
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [hBr z, hQB d z, abs_nonneg (r z), abs_nonneg (Q d z)]
    have hint2 : Integrable (fun x => (1 / 2 : ℝ) * (a d * (r x) ^ 2
        + (a d)⁻¹ * (Q d x) ^ 2)) π := by
      refine Integrable.const_mul (Integrable.add ?_ ?_) _
      · refine Integrable.const_mul ?_ _
        exact ⟨(hr.pow_const 2).aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := Br ^ 2) (ae_of_all _ (fun z => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hBr z, abs_nonneg (r z), sq_abs (r z)]))⟩
      · refine Integrable.const_mul ?_ _
        exact ⟨((hQm d).pow_const 2).aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := Br ^ 2) (ae_of_all _ (fun z => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hQB d z, abs_nonneg (Q d z), sq_abs (Q d z)]))⟩
    have hpt : ∀ x : X, |r x * Q d x|
        ≤ (1 / 2 : ℝ) * (a d * (r x) ^ 2 + (a d)⁻¹ * (Q d x) ^ 2) := by
      intro x
      have hkey : a d * |r x| * (a d * |r x|) + |Q d x| * |Q d x|
          - 2 * (a d * |r x| * |Q d x|) ≥ 0 := by
        nlinarith [sq_nonneg (a d * |r x| - |Q d x|)]
      have hinv' : (a d)⁻¹ * a d = 1 := inv_mul_cancel₀ (ne_of_gt hα)
      rw [abs_mul]
      have hstep : a d * (|r x| * |Q d x|) ≤ (1 / 2) * ((a d) ^ 2 * |r x| ^ 2 + |Q d x| ^ 2) := by
        nlinarith [sq_nonneg (a d * |r x| - |Q d x|)]
      have h2a : (0 : ℝ) < 2 * a d := by linarith
      have hdiv : |r x| * |Q d x|
          ≤ (1 / 2 : ℝ) * (a d * |r x| ^ 2 + (a d)⁻¹ * |Q d x| ^ 2) := by
        refine le_of_mul_le_mul_left ?_ h2a
        have hrhs : (2 * a d) * ((1 / 2 : ℝ) * (a d * |r x| ^ 2 + (a d)⁻¹ * |Q d x| ^ 2))
            = (a d) ^ 2 * |r x| ^ 2 + |Q d x| ^ 2 := by
          field_simp
        rw [hrhs]
        nlinarith [sq_nonneg (a d * |r x| - |Q d x|)]
      calc |r x| * |Q d x|
          ≤ (1 / 2 : ℝ) * (a d * |r x| ^ 2 + (a d)⁻¹ * |Q d x| ^ 2) := hdiv
        _ = (1 / 2 : ℝ) * (a d * (r x) ^ 2 + (a d)⁻¹ * (Q d x) ^ 2) := by
            rw [sq_abs, sq_abs]
    have hmono := integral_mono hint1.abs hint2 hpt
    have habs : |c d| ≤ ∫ x, |r x * Q d x| ∂π := by
      rw [hc]
      exact abs_integral_le_integral_abs
    have hcalc : ∫ x, (1 / 2 : ℝ) * (a d * (r x) ^ 2 + (a d)⁻¹ * (Q d x) ^ 2) ∂π
        = (1 / 2 : ℝ) * (a d * S + (a d)⁻¹ * ∫ x, (Q d x) ^ 2 ∂π) := by
      have i1 : Integrable (fun x => a d * (r x) ^ 2) π := by
        refine Integrable.const_mul ?_ _
        exact ⟨(hr.pow_const 2).aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := Br ^ 2) (ae_of_all _ (fun z => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hBr z, abs_nonneg (r z), sq_abs (r z)]))⟩
      have i2 : Integrable (fun x => (a d)⁻¹ * (Q d x) ^ 2) π := by
        refine Integrable.const_mul ?_ _
        exact ⟨((hQm d).pow_const 2).aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := Br ^ 2) (ae_of_all _ (fun z => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hQB d z, abs_nonneg (Q d z), sq_abs (Q d z)]))⟩
      rw [integral_const_mul, integral_add i1 i2, integral_const_mul, integral_const_mul, hS]
    rw [hcalc] at hmono
    have hQsq : ∫ x, (Q d x) ^ 2 ∂π ≤ (1 / 4 : ℝ) ^ (d / N) * S := hgeo
    have hid : (a d)⁻¹ * ((1 / 4 : ℝ) ^ (d / N) * S) = a d * S := by
      rw [ha]
      have hq : (1 / 4 : ℝ) = ((1 : ℝ) / 2) ^ 2 := by norm_num
      have h4 : (1 / 4 : ℝ) ^ (d / N) = ((1 / 2 : ℝ) ^ (d / N)) ^ 2 := by
        rw [hq, ← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [h4]
      field_simp
    have hstep2 : (a d)⁻¹ * ∫ x, (Q d x) ^ 2 ∂π ≤ a d * S := by
      have := mul_le_mul_of_nonneg_left hQsq (le_of_lt (inv_pos.mpr hα))
      rw [hid] at this
      exact this
    calc |c d| ≤ ∫ x, |r x * Q d x| ∂π := habs
      _ ≤ (1 / 2 : ℝ) * (a d * S + (a d)⁻¹ * ∫ x, (Q d x) ^ 2 ∂π) := hmono
      _ ≤ (1 / 2 : ℝ) * (a d * S + a d * S) := by linarith
      _ = a d * S := by ring
