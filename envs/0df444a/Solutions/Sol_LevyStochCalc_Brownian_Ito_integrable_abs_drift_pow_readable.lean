-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integrable_abs_drift_pow_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:08.212109+00:00
-- url     : https://prove2.me/submissions/ccc8a6ab-c933-43d4-bc7b-5f3c9ce317f5

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoProcess
import Theorems.Thm_LevyStochCalc_abs_setIntegral_Ioc_le_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
/-- The integral of a jointly measurable function over a fixed set is measurable in the
parameter. -/
theorem LevyStochCalc.measurable_setIntegral {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (s : Set ℝ) :
    Measurable fun ω => ∫ t in s, f ω t ∂volume :=
  (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict s) hf.stronglyMeasurable).measurable
/-- The integral of a jointly measurable function over a fixed window is measurable in the
parameter. -/
theorem LevyStochCalc.measurable_setIntegral_Ioc {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (a b : ℝ) :
    Measurable fun ω => ∫ s in Set.Ioc a b, f ω s ∂volume :=
  measurable_setIntegral hf (Set.Ioc a b)
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Drift
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- The `n`-th power of the absolute increment of a bounded drift's integral is integrable. -/
theorem solution
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) (n : ℕ) :
    MeasureTheory.Integrable
      (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ^ n) P := by
  have hDmeas : Measurable fun ω : Ω => ∫ s in Set.Ioc u v, bdrift ω s ∂volume :=
    LevyStochCalc.measurable_setIntegral_Ioc hbm _ _
  have hvu : (0 : ℝ) ≤ v - u := sub_nonneg.mpr huv
  refine (MeasureTheory.integrable_const ((B * (v - u)) ^ n)).mono
    ((hDmeas.abs.pow_const n).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (abs_nonneg _) n),
    abs_of_nonneg (pow_nonneg (mul_nonneg hB0 hvu) n)]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (LevyStochCalc.abs_setIntegral_Ioc_le_readable (Measurable.of_uncurry_left hbm) (hB ω) huv) n
