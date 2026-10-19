-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_lintegral_toRealIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:31:22.127367+00:00
-- url     : https://prove2.me/submissions/f63eb084-c3ea-4345-bdcc-abcc28f47fc7

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume =
      ENNReal.ofReal (∫ t : ℝ,
        (if 0 ≤ t ∧ t ≤ 1 then (1 - t) ^ n else 0)
        ∂MeasureTheory.volume) := by
  classical
  let f : ℝ → ℝ := fun t => if 0 ≤ t ∧ t ≤ 1 then (1 - t) ^ n else 0
  have hrepr : f = Set.indicator (Set.Icc (0 : ℝ) 1) (fun t => (1 - t) ^ n) := by
    funext t
    simp only [f, Set.indicator_apply, Set.mem_Icc]
  have hcont : Continuous (fun t : ℝ => (1 - t) ^ n) :=
    (continuous_const.sub continuous_id).pow n
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (1 - t) ^ n)
      (Set.Icc 0 1) MeasureTheory.volume :=
    hcont.integrableOn_Icc
  have hfint : MeasureTheory.Integrable f MeasureTheory.volume := by
    rw [hrepr]
    exact hbase.integrable_indicator measurableSet_Icc
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume] f := by
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : 0 ≤ t ∧ t ≤ 1
    · simpa only [Pi.zero_apply, f, if_pos ht] using pow_nonneg (sub_nonneg.mpr ht.2) n
    · simp only [Pi.zero_apply, f, if_neg ht, le_refl]
  calc
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (f t) ∂MeasureTheory.volume := by
      apply MeasureTheory.lintegral_congr
      intro t
      by_cases ht : 0 ≤ t ∧ t ≤ 1
      · simp only [f, if_pos ht, ENNReal.ofReal_pow (sub_nonneg.mpr ht.2) n]
      · simp only [f, if_neg ht, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (∫ t : ℝ, f t ∂MeasureTheory.volume) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfint hnonneg).symm