-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_abs_sub_pow_three_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:31:43.689121+00:00
-- url     : https://prove2.me/submissions/5d1fcc91-4af0-4f73-b230-d673860dc9d4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sub_pow_four_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sub_sq_le_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section ThirdMoment
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hℱ in
/-- The increment of the `L²` Itô integral is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian (a b : ℝ) :
    Measurable fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω :=
  (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq b).mono
      (ℱ.le b)).measurable).sub
    (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq a).mono
      (ℱ.le a)).measurable)
open LevyStochCalc.Brownian.Ito in
include hℱ hC0 hCH in
/-- **Third absolute moment of an increment of the `L²` Itô integral.** For an integrand
bounded by `C`, `𝔼|∫_a^b H dW|³ ≤ ((C² + (6 + c)C⁴)/2)·(b − a)·√(b − a)`. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MeasureTheory.Integrable (fun ω => |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3) P
      ∧ ∫ ω, |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3 ∂P
        ≤ (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * ((b - a) * Real.sqrt (b - a)) := by
  have hmeas := LevyStochCalc.Brownian.Ito.measurable_sub_stochasticIntegralBrownian W ℱ hℱ H hm hp hq a b
  obtain ⟨h2int, h2le⟩ := LevyStochCalc.Brownian.Ito.integral_sub_sq_le_readable W ℱ hℱ H hm hp hq hC0 hCH ha hab
  obtain ⟨h4int, h4le⟩ := LevyStochCalc.Brownian.Ito.integral_sub_pow_four_le_readable W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hba : (0 : ℝ) < b - a := by linarith
  set lam : ℝ := Real.sqrt (b - a) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hba
  have hlamsq : lam ^ 2 = b - a := Real.sq_sqrt hba.le
  -- pointwise Young inequality `2λ|y|³ ≤ λ²y² + y⁴`
  have hyoung : ∀ y : ℝ, |y| ^ 3 ≤ (lam ^ 2 * y ^ 2 + y ^ 4) / (2 * lam) := by
    intro y
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * lam)]
    have hy2 : |y| ^ 2 = y ^ 2 := sq_abs y
    have hy3 : |y| * y ^ 2 = |y| ^ 3 := by rw [← hy2]; ring
    have hid : (lam * |y| - y ^ 2) ^ 2
        = lam ^ 2 * |y| ^ 2 - 2 * lam * (|y| * y ^ 2) + y ^ 4 := by ring
    rw [hy2, hy3] at hid
    linarith [sq_nonneg (lam * |y| - y ^ 2), hid]
  have hdomint : MeasureTheory.Integrable
      (fun ω => (lam ^ 2 * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) / (2 * lam)) P :=
    ((h2int.const_mul (lam ^ 2)).add h4int).div_const _
  have hint3 : MeasureTheory.Integrable
      (fun ω => |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3) P := by
    refine hdomint.mono ((hmeas.abs.pow_const 3).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3)]
    refine (hyoung _).trans (le_abs_self _)
  refine ⟨hint3, ?_⟩
  calc ∫ ω, |LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω| ^ 3 ∂P
      ≤ ∫ ω, (lam ^ 2 * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
          + (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4) / (2 * lam) ∂P :=
        MeasureTheory.integral_mono hint3 hdomint (fun ω => hyoung _)
    _ = (lam ^ 2 * (∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 ∂P)
          + ∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 4 ∂P) / (2 * lam) := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_add (h2int.const_mul _) h4int,
          MeasureTheory.integral_const_mul]
    _ ≤ (lam ^ 2 * (C ^ 2 * (b - a))
          + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) / (2 * lam) := by
        gcongr
    _ = (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2 * ((b - a) * lam) := by
        rw [hlamsq]
        field_simp
        rw [hlamsq]
        ring
