-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_abs_sum_pow_three_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:34.265122+00:00
-- url     : https://prove2.me/submissions/55968788-f593-439e-ad61-a715cde2369e

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoThirdMoment
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_abs_sum_pow_three_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoThirdMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section GenericThird
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- The third absolute moment of a finite sum is at most the squared number of summands times the
sum of the third absolute moments. -/
theorem solution {ι : Type*} [Fintype ι] {f : ι → Ω → ℝ}
    (hfm : ∀ i, Measurable (f i)) (hfi : ∀ i, Integrable (fun ω => |f i ω| ^ 3) P)
    {c : ι → ℝ} (hc : ∀ i, ∫ ω, |f i ω| ^ 3 ∂P ≤ c i) :
    ∫ ω, |∑ i, f i ω| ^ 3 ∂P ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ i, c i := by
  have hdom : Integrable (fun ω => (Fintype.card ι : ℝ) ^ 2 * ∑ i, |f i ω| ^ 3) P :=
    (MeasureTheory.integrable_finsetSum _ fun i _ => hfi i).const_mul _
  have hpt : ∀ ω, |∑ i, f i ω| ^ 3 ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ i, |f i ω| ^ 3 := fun ω => by
    have h1 : |∑ i, f i ω| ^ 3 ≤ (∑ i, |f i ω|) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) 3
    have h2 := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset ι))
      (f := fun i => |f i ω|) (fun j _ => abs_nonneg (f j ω)) 2
    simpa using h1.trans h2
  have hint : Integrable (fun ω => |∑ i, f i ω| ^ 3) P :=
    LevyStochCalc.Brownian.Ito.integrable_abs_sum_pow_three_readable hfm hfi
  calc ∫ ω, |∑ i, f i ω| ^ 3 ∂P
      ≤ ∫ ω, (Fintype.card ι : ℝ) ^ 2 * ∑ i, |f i ω| ^ 3 ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = (Fintype.card ι : ℝ) ^ 2 * ∑ i, ∫ ω, |f i ω| ^ 3 ∂P := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum _ fun i _ => hfi i]
    _ ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ i, c i := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hc i) (by positivity)
