-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:11:32.95582+00:00
-- url     : https://prove2.me/submissions/f96882b8-a467-486e-b6b6-957c3383ee89

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ENNReal.toReal (∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume) = (↑(n + 1 : ℕ) : ℝ)⁻¹ := by
  let f : ℝ → ℝ := Set.indicator (Set.Icc (0 : ℝ) 1) (fun t => (1 - t) ^ n)
  have hfcont : Continuous (fun t : ℝ => (1 - t) ^ n) := by fun_prop
  have hfOn : MeasureTheory.IntegrableOn (fun t : ℝ => (1 - t) ^ n)
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume :=
    hfcont.continuousOn.integrableOn_compact isCompact_Icc
  have hfint : MeasureTheory.Integrable f MeasureTheory.volume := by
    simpa [f] using hfOn.integrable_indicator measurableSet_Icc
  have hfnn : 0 ≤ᵐ[MeasureTheory.volume] f := by
    filter_upwards [] with t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · simp [f, ht]
      exact pow_nonneg (sub_nonneg.mpr ht.2) n
    · simp [f, ht]
  have hcalc : (∫ t, f t ∂MeasureTheory.volume) = (↑(n + 1 : ℕ) : ℝ)⁻¹ := by
    rw [show f = Set.indicator (Set.Icc (0 : ℝ) 1) (fun t => (1 - t) ^ n) from rfl,
      MeasureTheory.integral_indicator measurableSet_Icc,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
    calc
      (∫ t in Set.Ioc (0 : ℝ) 1, (1 - t) ^ n) =
          ∫ t in Set.Ioc (0 : ℝ) 1, |t - 1| ^ n := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        change (1 - t) ^ n = |t - 1| ^ n
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub]
      _ = ∫ t in Set.uIoc (1 : ℝ) 0, |t - 1| ^ n := by
        rw [← Set.uIoc_of_ge (show (0 : ℝ) ≤ 1 by norm_num)]
      _ = (↑(n + 1 : ℕ) : ℝ)⁻¹ := by
        simpa [div_eq_mul_inv] using
          (integral_pow_abs_sub_uIoc (a := (1 : ℝ)) (b := 0) (n := n))
  have hlin : (∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume) = ENNReal.ofReal (∫ t, f t ∂MeasureTheory.volume) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfint hfnn]
    apply MeasureTheory.lintegral_congr
    intro t
    by_cases ht : 0 ≤ t ∧ t ≤ 1
    · have htmem : t ∈ Set.Icc (0 : ℝ) 1 := ht
      simp [f, ht, htmem, ENNReal.ofReal_pow, sub_nonneg.mpr ht.2]
    · have htmem : t ∉ Set.Icc (0 : ℝ) 1 := fun hm => ht hm
      simp [f, ht, htmem]
  rw [hlin, hcalc, ENNReal.toReal_ofReal]
  positivity
