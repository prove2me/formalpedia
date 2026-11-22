-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.integral_sq_le_mul_integral_sq_on_Icc
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:45:23.904707+00:00
-- url     : https://prove2.me/submissions/302223c4-ca82-499a-b5dc-40b735e2f119

import Mathlib

open MeasureTheory

theorem solution (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf_nn : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)), 0 ≤ f s)
    (hf_L2 : MeasureTheory.MemLp f 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    (∫ s in Set.Icc (0 : ℝ) t, f s) ^ 2
      ≤ t * ∫ s in Set.Icc (0 : ℝ) t, (f s) ^ 2 := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Set.Icc 0 t))
    Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ)) (g := f)
    (Filter.Eventually.of_forall (fun _ => zero_le_one)) hf_nn (memLp_const 1)
    (by simpa using hf_L2)
  have hbound : (∫ s in Set.Icc 0 t, f s) ≤
      Real.sqrt t * Real.sqrt (∫ s in Set.Icc 0 t, (f s)^2) := by
    simpa only [one_mul, Real.rpow_ofNat, one_pow, setIntegral_const, smul_eq_mul,
      mul_one, Real.volume_real_Icc_of_le ht, sub_zero, ← Real.sqrt_eq_rpow] using h
  have hn := integral_nonneg_of_ae hf_nn
  have hs : 0 ≤ ∫ s in Set.Icc 0 t, (f s)^2 := integral_nonneg (fun s => sq_nonneg _)
  simpa only [mul_pow, Real.sq_sqrt ht, Real.sq_sqrt hs] using pow_le_pow_left₀ hn hbound 2
#print axioms solution
