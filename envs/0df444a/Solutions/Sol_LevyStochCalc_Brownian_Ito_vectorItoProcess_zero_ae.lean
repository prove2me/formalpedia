-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.vectorItoProcess_zero_ae
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:10:32.007933+00:00
-- url     : https://prove2.me/submissions/dd46aaaf-7aa8-49de-b6d3-50ceb93ae775
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_ae_zero_of_nonpos
import Definitions.Def_LevyStochCalc_Brownian_ItoOptionalStopping_F001
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a vector Itô process

Cutting the coefficients of a vector Itô process off at a stopping time of finite range leaves a
vector Itô process, whose version is the original one evaluated at the clipped time.

## Main statements

* `LevyStochCalc.Brownian.Ito.clipTime` — the horizon clipped at a stopping time.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip` — the Itô integral of a
  stopped integrand is the integral evaluated at the clipped horizon.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` — the stopped version.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Clip

variable {Ω : Type u}

variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}

end Clip

section StoppedIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsBrownianFiltration W ℱ) (τ : Ω → WithTop ℝ)

end StoppedIntegral

section StoppedDrift

variable {Ω : Type u}

end StoppedDrift

section StoppedVersion

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)


include hcoord in

theorem _root_.solution
    (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ) :
    vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift 0 =ᵐ[P] X₀ := by
  have hzero (i : Fin n) (k : Fin d) :
      coordItoIntegral W ℱ hcoord H hHm hHp hHs i k 0 =ᵐ[P] 0 := by
    unfold coordItoIntegral
    first
    | exact stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hcoord k)
        (H i k) (hHm i k) (hHp i k) (hHs i k) le_rfl
    | exact?
  have hcoord0 : ∀ᵐ ω ∂P, ∀ (i : Fin n) (k : Fin d),
      coordItoIntegral W ℱ hcoord H hHm hHp hHs i k 0 ω = 0 := by
    exact ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun k => hzero i k))
  filter_upwards [hcoord0] with ω hω
  funext i
  simp [vectorItoProcess, vectorItoMartingale, hω, Set.Icc_self]
