-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.sq_enorm_finsetSum_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:14.575571+00:00
-- url     : https://prove2.me/submissions/46f24591-dba7-469f-9f7d-8d9a25565f21

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoTruncate

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoTruncate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
section Difference
open LevyStochCalc.Brownian.Multidim
variable {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
/-- The squared norm of a finite sum of reals is at most the number of summands times the sum of
their squared norms, in `ℝ≥0∞`. -/
theorem solution {m : ℕ} (x : Fin m → ℝ) :
    (‖∑ k, x k‖₊ : ℝ≥0∞) ^ 2 ≤ (m : ℝ≥0∞) * ∑ k, (‖x k‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (∑ k, |x k|) ^ 2 ≤ (m : ℝ) * ∑ k, |x k| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m))) (f := fun k => |x k|)
    simpa using this
  have habs : |∑ k, x k| ≤ ∑ k, |x k| := Finset.abs_sum_le_sum_abs _ _
  have hnn : ‖∑ k, x k‖₊ ^ 2 ≤ (m : ℝ≥0) * ∑ k, ‖x k‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have h1 : |∑ k, x k| ^ 2 ≤ (∑ k, |x k|) ^ 2 := by
      have h0 : (0 : ℝ) ≤ |∑ k, x k| := abs_nonneg _
      nlinarith [habs, h0]
    calc |∑ k, x k| ^ 2 ≤ (∑ k, |x k|) ^ 2 := h1
      _ ≤ (m : ℝ) * ∑ k, |x k| ^ 2 := hreal
      _ = (m : ℝ) * ∑ k, |x k| ^ 2 := rfl
  calc (‖∑ k, x k‖₊ : ℝ≥0∞) ^ 2 = ((‖∑ k, x k‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ (((m : ℝ≥0) * ∑ k, ‖x k‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hnn
    _ = (m : ℝ≥0∞) * ∑ k, (‖x k‖₊ : ℝ≥0∞) ^ 2 := by push_cast; ring
