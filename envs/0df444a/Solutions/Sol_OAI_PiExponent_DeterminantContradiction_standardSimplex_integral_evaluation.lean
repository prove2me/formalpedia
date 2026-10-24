-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_integral_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:16:07.094465+00:00
-- url     : https://prove2.me/submissions/6582ddf5-b275-4955-a973-d6eb49bedade

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set

theorem solution (n : Nat) (c : ENNReal) :
    (∫⁻ t in Set.Icc (0 : Real) 1,
        (ENNReal.ofReal (1 - t)) ^ n * c ∂MeasureTheory.volume) =
      c / (n + 1 : ENNReal) := by
  let f : Real → Real := fun t => (1 - t) ^ n
  have hreal : (∫ t in Set.Icc (0 : Real) 1, f t ∂MeasureTheory.volume) =
      1 / (n + 1 : Real) := by
    dsimp [f]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : Real) ≤ 1)]
    rw [intervalIntegral.integral_comp_sub_left (f := fun x : Real => x ^ n) 1]
    simp
  have hfi : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1)) := by
    change MeasureTheory.IntegrableOn f (Set.Icc (0 : Real) 1) MeasureTheory.volume
    exact ((by fun_prop : Continuous f).continuousOn).integrableOn_compact isCompact_Icc
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : Real) 1)] f := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    dsimp [f]
    exact pow_nonneg (by linarith [ht.2] : 0 ≤ 1 - t) n
  have hbase : (∫⁻ t in Set.Icc (0 : Real) 1, ENNReal.ofReal (1 - t) ^ n ∂MeasureTheory.volume) =
      ENNReal.ofReal (1 / (n + 1 : Real)) := by
    have hpow : (∫⁻ t in Set.Icc (0 : Real) 1, ENNReal.ofReal (1 - t) ^ n ∂MeasureTheory.volume) =
        ∫⁻ t in Set.Icc (0 : Real) 1, ENNReal.ofReal (f t) ∂MeasureTheory.volume := by
      apply MeasureTheory.lintegral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      dsimp [f]
      rw [ENNReal.ofReal_pow (by linarith [ht.2] : 0 ≤ 1 - t) n]
    rw [hpow, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hnonneg, hreal]
  calc
    (∫⁻ t in Set.Icc (0 : Real) 1, (ENNReal.ofReal (1 - t)) ^ n * c ∂MeasureTheory.volume) =
        (∫⁻ t in Set.Icc (0 : Real) 1, ENNReal.ofReal (1 - t) ^ n ∂MeasureTheory.volume) * c := by
      rw [MeasureTheory.lintegral_mul_const'' c (by fun_prop)]
    _ = ENNReal.ofReal (1 / (n + 1 : Real)) * c := by rw [hbase]
    _ = c / (n + 1 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : Real) < n + 1)]
      have hden : ENNReal.ofReal ((n : Real) + 1) = (n + 1 : ENNReal) := by
        calc
          ENNReal.ofReal ((n : Real) + 1) = ENNReal.ofReal ((n + 1 : Nat) : Real) := by
            congr 1 <;> norm_cast
          _ = ((n + 1 : Nat) : ENNReal) := ENNReal.ofReal_natCast _
          _ = (n + 1 : ENNReal) := by norm_cast
      simp [ENNReal.div_eq_inv_mul, hden, mul_comm]