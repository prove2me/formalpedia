-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.norm_kernelResolventReal_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:48:36.546549+00:00
-- url     : https://prove2.me/submissions/9f2e483b-be56-457a-aaa7-d971dd8435c5

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup
import Definitions.Def_MarkovProcess_KernelIntegral
import Definitions.Def_MarkovProcess_KernelResolvents

open Filter MeasureTheory ProbabilityTheory Set MarkovProcess
open scoped ENNReal NNReal
variable {alpha : Type*} [MeasurableSpace alpha]
theorem kib_aux (P : SubMarkovKernelSemigroup alpha)
    {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (t : NNReal) (x : alpha) :
    |kernelIntegral (P t) f x| ≤ D := by
  have hD : 0 ≤ D := (abs_nonneg _).trans (hfD x)
  have hle : (P t x) univ ≤ 1 := P.isSubMarkovKernel t x
  haveI : IsFiniteMeasure (P t x) := ⟨lt_of_le_of_lt hle ENNReal.one_lt_top⟩
  have h1 := norm_integral_le_of_norm_le_const (μ := P t x) (f := f) (C := D)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hfD y)
  have h2 : (P t x).real univ ≤ 1 := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle)
  unfold kernelIntegral
  rw [← Real.norm_eq_abs]
  calc _ ≤ D * (P t x).real univ := h1
    _ ≤ D * 1 := by gcongr
    _ = D := mul_one D

theorem solution (P : SubMarkovKernelSemigroup alpha)
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    |P.kernelResolventReal lam f x| ≤ D / lam := by
  have hint : IntegrableOn (fun t : ℝ => D * Real.exp (-lam * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hlam).const_mul D
  have h1 := norm_integral_le_of_norm_le (μ := volume.restrict (Ioi (0:ℝ)))
    (f := fun t : ℝ => Real.exp (-lam * t) * kernelIntegral (P (Real.toNNReal t)) f x) hint
    (Filter.Eventually.of_forall fun t => by
      show ‖Real.exp (-lam * t) * kernelIntegral (P (Real.toNNReal t)) f x‖ ≤ D * Real.exp (-lam * t)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
      exact mul_le_mul_of_nonneg_right (kib_aux P hfD _ x) (Real.exp_pos _).le)
  have h2 : ∫ t in Ioi (0:ℝ), D * Real.exp (-lam * t) = D / lam := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
    field_simp
    simp
  unfold SubMarkovKernelSemigroup.kernelResolventReal
  rw [← Real.norm_eq_abs, ← h2]
  exact h1
