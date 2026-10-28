-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.memLp_two_sq_increment_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:29:27.143342+00:00
-- url     : https://prove2.me/submissions/280a7ade-4640-46f6-8bd6-f97a6277bbfe

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoQuadVarSum
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_stochasticIntegralBrownian_sub_pow_four_le_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoQuadVarSum.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A square-integrable function lies in `L²`. -/
theorem LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top {P' : Measure Ω} {f : Ω → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f P')
    (h : ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂P' < ⊤) : MemLp f 2 P' := by
  refine ⟨hf, ?_⟩
  by_contra hcon
  have htop : MeasureTheory.eLpNorm f 2 P' = ⊤ := top_le_iff.mp (not_lt.mp hcon)
  rw [← eLpNorm_two_rpow_eq_lintegral_sq f, htop,
    ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  exact lt_irrefl _ h
section IncrementL2
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
include hℱ hC0 hCH in
/-- The square of an increment of the Itô integral lies in `L²`. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) 2 P := by
  have hmeas : Measurable fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω :=
    (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq b).mono
        (ℱ.le b)).measurable).sub
      (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq a).mono
        (ℱ.le a)).measurable)
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top (hmeas.pow_const 2).aestronglyMeasurable ?_
  have hpt : ∀ ω : Ω, (‖(LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2‖₊ : ℝ≥0∞) ^ 2
      = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
    intro ω
    rw [nnnorm_pow, ENNReal.coe_pow, ← pow_mul]
  simp_rw [hpt]
  exact lt_of_le_of_lt
    (LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_pow_four_le_readable W ℱ hℱ H hm hp hq hC0 hCH ha hab)
    (by simp)
