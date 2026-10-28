-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eval_simple_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:03.210922+00:00
-- url     : https://prove2.me/submissions/90404d06-b04a-455b-a481-b17c6f73f9e1

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand
import Theorems.Thm_LevyStochCalc_Brownian_Ito_simpleIntegral_diff_isometry_of_adapted_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section EvalSimple
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (hm : Measurable (Function.uncurry fun ω s => G.eval s ω))
  (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
include hℱ h_adapt in
/-- **The `L²` Itô integral of a simple integrand is its elementary integral.** -/
theorem solution {t : ℝ} (ht : 0 ≤ t) :
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t
      =ᵐ[P] LevyStochCalc.Brownian.Ito.simpleIntegral W G t := by
  classical
  have hIn : ∀ n : ℕ, Measurable
      (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t) := by
    intro n
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIG : Measurable (LevyStochCalc.Brownian.Ito.simpleIntegral W G t) := by
    unfold LevyStochCalc.Brownian.Ito.simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      (G.ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hSI : Measurable
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t) :=
    ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ (fun ω s => G.eval s ω) hm
      hp hq t).mono (ℱ.le t)).measurable
  -- the master integrals converge to the elementary integral of `G`
  have hA : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
        - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    refine (LevyStochCalc.Brownian.Ito.masterApprox_eval_tendsto (t := t) ℱ (fun ω s => G.eval s ω) hm hp hq).congr
      fun n => ?_
    rw [LevyStochCalc.Brownian.Ito.simpleIntegral_diff_isometry_of_adapted_readable W ℱ hℱ _ G
      (LevyStochCalc.Brownian.Ito.masterApprox_adapt ℱ (fun ω s => G.eval s ω) hm hp hq n) h_adapt ht]
    refine lintegral_congr fun ω =>
      MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    rw [← nnnorm_neg, neg_sub]
  -- and to the `L²` Itô integral
  have hconv : ∀ g : Ω → ℝ, MeasureTheory.eLpNorm g 2 P * MeasureTheory.eLpNorm g 2 P
      = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro g
    rw [← LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  have hB : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    have h := LevyStochCalc.Brownian.Ito.masterApprox_tendsto_L2 W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq ht
    have h2 := ENNReal.Tendsto.mul h (Or.inr (by simp)) h (Or.inr (by simp))
    simpa [hconv] using h2
  -- squeeze
  have hle : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
      hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ 0 := by
    have hlim : Filter.Tendsto (fun n => 2 * ((∫⁻ ω,
        (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
            hq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
            hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P))
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := 2) (hB.add hA) (Or.inr (by simp))
      simpa using this
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    calc ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
          hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * ((‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm
              hp hq n) t ω - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => G.eval s ω) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2
            + (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
              hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hrw : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
                hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω
              = -(LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
                  hq n) t ω - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω)
                  hm hp hq t ω)
                + (LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
                  hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω) := by ring
          rw [hrw]
          refine le_trans (LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul_brownian _ _) ?_
          rw [nnnorm_neg]
      _ = 2 * ((∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm
              hp hq n) t ω - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => G.eval s ω) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
            + ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ (fun ω s => G.eval s ω) hm hp
              hq n) t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
          have hm2 : AEMeasurable (fun ω => (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (LevyStochCalc.Brownian.Ito.masterApprox ℱ
              (fun ω s => G.eval s ω) hm hp hq n) t ω
                - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
                  hq t ω‖₊ : ℝ≥0∞) ^ 2) P :=
            ((((hIn n).sub hSI).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.aemeasurable
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hm2]
  have hzero : ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm
      hp hq t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 :=
    le_antisymm hle bot_le
  have hmeas : Measurable fun ω => (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => G.eval s ω) hm hp hq t ω
        - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((hSI.sub hIG).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hzero] with ω hω
  have h0 : (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t ω
      - LevyStochCalc.Brownian.Ito.simpleIntegral W G t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  simpa [sub_eq_zero] using h0
