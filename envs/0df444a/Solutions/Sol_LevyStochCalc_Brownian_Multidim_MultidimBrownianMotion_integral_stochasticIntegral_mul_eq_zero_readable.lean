-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:27:15.404303+00:00
-- url     : https://prove2.me/submissions/d0eab055-9455-432a-9d17-983466c0a4b5

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_mul_eq_zero_of_tendsto_eLpNorm_readable
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_integral_simpleIntegral_mul_eq_zero_readable
import Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_memLp_simpleIntegral_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
section L2Limit
open LevyStochCalc.Brownian.Ito
/-- **Orthogonality of Itô integrals against distinct Brownian coordinates.** -/
theorem solution (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
    {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hcoord i) H hHm hHp hHs t ω
      * LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hcoord j) K hKm hKp hKs t ω ∂P = 0 := by
  have hui : MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hcoord i) H hHm hHp hHs t) 2 P :=
    (MeasureTheory.Lp.memLp _).ae_eq (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq (W.W i)
      ℱ (hcoord i) H hHm hHp hHs t).symm
  have huj : MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hcoord j) K hKm hKp hKs t) 2 P :=
    (MeasureTheory.Lp.memLp _).ae_eq (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_eq (W.W j)
      ℱ (hcoord j) K hKm hKp hKs t).symm
  refine LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_eq_zero_of_tendsto_eLpNorm_readable
    (un := fun n ω => LevyStochCalc.Brownian.Ito.simpleIntegral (W.W i) (LevyStochCalc.Brownian.Ito.masterApprox ℱ H hHm hHp hHs n) t ω)
    (vn := fun n ω => LevyStochCalc.Brownian.Ito.simpleIntegral (W.W j) (LevyStochCalc.Brownian.Ito.masterApprox ℱ K hKm hKp hKs n) t ω)
    hui huj (fun n => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral_readable _ _ t) (fun n => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral_readable _ _ t)
    (fun n => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_simpleIntegral_mul_eq_zero_readable W hij hcoord _ _
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ H hHm hHp hHs n)
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ K hKm hKp hKs n) t t)
    (LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 (W.W i) ℱ (hcoord i) H hHm hHp hHs ht)
    (LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 (W.W j) ℱ (hcoord j) K hKm hKp hKs ht)
