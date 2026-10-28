-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.simpleIntegral_diff_isometry_of_adapted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:16.401325+00:00
-- url     : https://prove2.me/submissions/e097cfcc-8430-4768-82b2-c5c100bb134e

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand

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
/-- Difference isometry at an intermediate time for two adapted simple integrands whose
horizons need not agree. -/
theorem solution
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {T₁ T₂ : ℝ} (G₁ : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₁) (G₂ : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T₂)
    (h₁ : ∀ i : Fin G₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G₁.partition i.castSucc)) (G₁.ξ i))
    (h₂ : ∀ i : Fin G₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G₂.partition i.castSucc)) (G₂.ξ i))
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω,
        (‖LevyStochCalc.Brownian.Ito.simpleIntegral W G₁ t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G₁.eval s ω - G₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set K : ℝ :=
    max (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N)) + 1 with hK
  have hK₁ : G₁.partition (Fin.last G₁.N) < K := by
    have := le_max_left (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N))
    rw [hK]; linarith
  have hK₂ : G₂.partition (Fin.last G₂.N) < K := by
    have := le_max_right (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N))
    rw [hK]; linarith
  have h_eq : (G₁.appendInterval hK₁).partition (Fin.last (G₁.appendInterval hK₁).N)
      = (G₂.appendInterval hK₂).partition (Fin.last (G₂.appendInterval hK₂).N) :=
    (G₁.appendInterval_partition_last hK₁).trans (G₂.appendInterval_partition_last hK₂).symm
  have hiso := LevyStochCalc.Brownian.Ito.simpleIntegral_intermediate_diff_isometry W ℱ hℱ (G₁.appendInterval hK₁)
    (G₂.appendInterval hK₂) h_eq (G₁.appendInterval_adapt ℱ hK₁ h₁)
    (G₂.appendInterval_adapt ℱ hK₂ h₂) ht
  have hL : ∫⁻ ω,
        (‖LevyStochCalc.Brownian.Ito.simpleIntegral W G₁ t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W G₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W (G₁.appendInterval hK₁) t ω
          - LevyStochCalc.Brownian.Ito.simpleIntegral W (G₂.appendInterval hK₂) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    lintegral_congr fun ω => by
      rw [G₁.appendInterval_simpleIntegral W hK₁ t ω,
        G₂.appendInterval_simpleIntegral W hK₂ t ω]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖G₁.eval s ω - G₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(G₁.appendInterval hK₁).eval s ω
          - (G₂.appendInterval hK₂).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    lintegral_congr fun ω => MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun s _ => by
      rw [G₁.appendInterval_eval hK₁ s ω, G₂.appendInterval_eval hK₂ s ω]
  rw [hL, hR]; exact hiso
