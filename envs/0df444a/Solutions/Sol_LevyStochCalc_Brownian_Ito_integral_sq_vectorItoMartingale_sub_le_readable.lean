-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_sq_vectorItoMartingale_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:26:44.401994+00:00
-- url     : https://prove2.me/submissions/b9253261-19fa-4188-8a38-0bf994809248

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_sq_sum_and_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sub_sq_le_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorProcess
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
/-- Each entry's Itô integral is measurable for the σ-algebra at its time. -/
theorem LevyStochCalc.Brownian.Ito.stronglyMeasurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    StronglyMeasurable[ℱ t] (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
    (hHs m k) t
/-- Each entry's Itô integral is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    Measurable (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  ((stronglyMeasurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t).mono (ℱ.le t)).measurable
/-- The increment of the martingale part is the sum of the entries' increments. -/
theorem LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub (m : Fin n) (u v : ℝ) (ω : Ω) :
    vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω
      = ∑ k : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) := by
  simp only [vectorItoMartingale, Finset.sum_sub_distrib]
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
include hC0 hCH in
/-- **Second moment of the martingale part's increment.** -/
theorem solution (m : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) ^ 2) P
      ∧ ∫ ω, (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) ^ 2 ∂P
        ≤ (d : ℝ) ^ 2 * (C ^ 2 * (v - u)) := by
  have hk : ∀ k : Fin d,
      Integrable (fun ω => (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2) P
        ∧ ∫ ω, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P ≤ C ^ 2 * (v - u) :=
    fun k => LevyStochCalc.Brownian.Ito.integral_sub_sq_le_readable (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k) (hHs m k)
      hC0 (hCH m k) hu huv
  obtain ⟨hint, hle⟩ := LevyStochCalc.Brownian.Ito.integrable_sq_sum_and_le_readable (P := P)
    (f := fun (k : Fin d) ω => LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
      - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω)
    (fun k => (LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v).sub
      (LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u))
    (fun k => (hk k).1)
  simp_rw [LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs m u v]
  refine ⟨hint, ?_⟩
  have hsum : ∑ k : Fin d, ∫ ω, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P
      ≤ (d : ℝ) * (C ^ 2 * (v - u)) := by
    calc ∑ k : Fin d, ∫ ω, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P
        ≤ ∑ _k : Fin d, C ^ 2 * (v - u) := Finset.sum_le_sum fun k _ => (hk k).2
      _ = (d : ℝ) * (C ^ 2 * (v - u)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcard : (Fintype.card (Fin d) : ℝ) = (d : ℝ) := by simp
  calc ∫ ω, (∑ k : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω)) ^ 2 ∂P
      ≤ (Fintype.card (Fin d) : ℝ) * ∑ k : Fin d,
          ∫ ω, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P := hle
    _ = (d : ℝ) * ∑ k : Fin d, ∫ ω, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P := by rw [hcard]
    _ ≤ (d : ℝ) * ((d : ℝ) * (C ^ 2 * (v - u))) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)
    _ = (d : ℝ) ^ 2 * (C ^ 2 * (v - u)) := by ring
