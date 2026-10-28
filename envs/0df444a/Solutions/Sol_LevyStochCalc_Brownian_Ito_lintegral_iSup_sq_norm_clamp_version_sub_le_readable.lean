-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_clamp_version_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:30:48.148318+00:00
-- url     : https://prove2.me/submissions/a63579a3-3a92-47c6-aa45-4d169fc5663d

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp
import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionUnbounded
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_energy_sub_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_iSup_sq_norm_version_sub_le_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
section Clamped
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
theorem LevyStochCalc.Brownian.Ito.measurable_clampDrift {b : Fin n → Ω → ℝ → ℝ}
    (hm : ∀ p, Measurable (Function.uncurry (b p))) (j : ℕ) (p : Fin n) :
    Measurable (Function.uncurry (clampDrift b j p)) :=
  (continuous_clampAt (j : ℝ)).measurable.comp (hm p)
omit [MeasurableSpace Ω] in
theorem LevyStochCalc.Brownian.Ito.abs_clampDrift_le (b : Fin n → Ω → ℝ → ℝ) (j : ℕ) (p : Fin n) (ω : Ω) (s : ℝ) :
    |clampDrift b j p ω s| ≤ (j : ℝ) :=
  abs_clampAt_le (Nat.cast_nonneg j) _
theorem LevyStochCalc.Brownian.Ito.energy_clampDrift_lt_top {b : Fin n → Ω → ℝ → ℝ}
    (j : ℕ) (p : Fin n) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampDrift b j p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  energy_lt_top_of_bounded (fun ω s => abs_clampDrift_le b j p ω s) T hT
end Clamped
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionUnbounded.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal
universe u
section ClampSup
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
include hcoord in
/-- **The window supremum of the difference of two clamped versions**, in terms of the clamping
mesh at the two levels. -/
theorem solution
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H p k)}
    {X₀ : Ω → Fin n → ℝ} {b : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {j j' : ℕ} {Xj Xj' : ℝ → Ω → Fin n → ℝ}
    (hXj : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j)
      (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hm j p k)
      (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j p k T' hT')
      X₀ (LevyStochCalc.Brownian.Ito.clampDrift b j) Xj)
    (hXj' : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j')
      (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hm j' p k)
      (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hpg j' p k)
      (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j' p k T' hT')
      X₀ (LevyStochCalc.Brownian.Ito.clampDrift b j') Xj')
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖Xj' (t : ℝ) ω - Xj (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
      ≤ 32 * (n : ℝ≥0∞) ^ 2 * (LevyStochCalc.Brownian.Ito.clampMesh P H b T j + LevyStochCalc.Brownian.Ito.clampMesh P H b T j') := by
  classical
  set A : Fin n → ℝ≥0∞ := fun p => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖LevyStochCalc.Brownian.Ito.clampDrift b j' p ω s - LevyStochCalc.Brownian.Ito.clampDrift b j p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hAdef
  set a : Fin n → ℝ≥0∞ := fun p => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖LevyStochCalc.Brownian.Ito.clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hadef
  set a' : Fin n → ℝ≥0∞ := fun p => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖LevyStochCalc.Brownian.Ito.clampDrift b j' p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with ha'def
  set B : Fin n → Fin d → ℝ≥0∞ := fun p k => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖LevyStochCalc.Brownian.Ito.clampCoeff H j' p k ω s - LevyStochCalc.Brownian.Ito.clampCoeff H j p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hBdef
  set bb : Fin n → Fin d → ℝ≥0∞ := fun p k => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖LevyStochCalc.Brownian.Ito.clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hbbdef
  set bb' : Fin n → Fin d → ℝ≥0∞ := fun p k => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖LevyStochCalc.Brownian.Ito.clampCoeff H j' p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hbb'def
  have hA : ∀ p : Fin n, A p ≤ 2 * (a' p + a p) := fun p =>
    LevyStochCalc.Brownian.Ito.lintegral_energy_sub_le_readable (LevyStochCalc.Brownian.Ito.measurable_clampDrift hbm j' p) (LevyStochCalc.Brownian.Ito.measurable_clampDrift hbm j p)
      (hbm p) T
  have hB : ∀ (p : Fin n) (k : Fin d), B p k ≤ 2 * (bb' p k + bb p k) := fun p k =>
    LevyStochCalc.Brownian.Ito.lintegral_energy_sub_le_readable (LevyStochCalc.Brownian.Ito.measurable_clampCoeff hm j' p k) (LevyStochCalc.Brownian.Ito.measurable_clampCoeff hm j p k)
      (hm p k) T
  have hper : ∀ p : Fin n,
      4 * (ENNReal.ofReal T * A p) + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, B p k))
        ≤ 32 * ((2 * (ENNReal.ofReal T * a p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb p k))
          + (2 * (ENNReal.ofReal T * a' p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb' p k))) := by
    intro p
    have h2 : ∑ k : Fin d, B p k ≤ 2 * ((∑ k : Fin d, bb' p k) + ∑ k : Fin d, bb p k) := by
      refine (Finset.sum_le_sum fun k _ => hB p k).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    calc 4 * (ENNReal.ofReal T * A p) + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, B p k))
        ≤ 4 * (ENNReal.ofReal T * (2 * (a' p + a p)))
          + 4 * (4 * ((d : ℝ≥0∞) * (2 * ((∑ k : Fin d, bb' p k) + ∑ k : Fin d, bb p k)))) :=
          add_le_add (mul_le_mul' le_rfl (mul_le_mul' le_rfl (hA p)))
            (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl h2)))
      _ = 8 * (ENNReal.ofReal T * (a' p + a p))
          + 32 * ((d : ℝ≥0∞) * ((∑ k : Fin d, bb' p k) + ∑ k : Fin d, bb p k)) := by ring
      _ ≤ 64 * (ENNReal.ofReal T * (a' p + a p))
          + 64 * ((d : ℝ≥0∞) * ((∑ k : Fin d, bb' p k) + ∑ k : Fin d, bb p k)) :=
          add_le_add (mul_le_mul' (by norm_num) le_rfl) (mul_le_mul' (by norm_num) le_rfl)
      _ = 32 * ((2 * (ENNReal.ofReal T * a p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb p k))
          + (2 * (ENNReal.ofReal T * a' p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb' p k))) := by
          ring
  have hgen := LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_version_sub_le_readable W ℱ hcoord
    (hbm₁ := fun p => LevyStochCalc.Brownian.Ito.measurable_clampDrift hbm j p)
    (hbm₂ := fun p => LevyStochCalc.Brownian.Ito.measurable_clampDrift hbm j' p)
    (hbq₁ := fun p T' hT' => LevyStochCalc.Brownian.Ito.energy_clampDrift_lt_top j p T' hT')
    (hbq₂ := fun p T' hT' => LevyStochCalc.Brownian.Ito.energy_clampDrift_lt_top j' p T' hT')
    hXj hXj' hT
  refine hgen.trans ?_
  have hmesh : LevyStochCalc.Brownian.Ito.clampMesh P H b T j + LevyStochCalc.Brownian.Ito.clampMesh P H b T j'
      = ∑ p : Fin n, ((2 * (ENNReal.ofReal T * a p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb p k))
        + (2 * (ENNReal.ofReal T * a' p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb' p k))) := by
    unfold LevyStochCalc.Brownian.Ito.clampMesh
    rw [← Finset.sum_add_distrib]
  rw [hmesh]
  calc (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
        (4 * (ENNReal.ofReal T * A p) + 4 * (4 * ((d : ℝ≥0∞) * ∑ k : Fin d, B p k)))
      ≤ (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
        32 * ((2 * (ENNReal.ofReal T * a p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb p k))
          + (2 * (ENNReal.ofReal T * a' p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb' p k))) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun p _ => hper p)
    _ = 32 * (n : ℝ≥0∞) ^ 2 * ∑ p : Fin n,
        ((2 * (ENNReal.ofReal T * a p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb p k))
          + (2 * (ENNReal.ofReal T * a' p) + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, bb' p k))) := by
        rw [← Finset.mul_sum]
        ring
