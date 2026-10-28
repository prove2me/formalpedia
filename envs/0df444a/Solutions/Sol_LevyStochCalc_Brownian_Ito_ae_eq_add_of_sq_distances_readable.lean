-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.ae_eq_add_of_sq_distances_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:43.574952+00:00
-- url     : https://prove2.me/submissions/2fed93ef-e494-48de-b2ea-f49a5a115043

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- The squared extended norm of a real number is the extended real of its square. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq (z : ℝ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := by
  rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
omit [IsProbabilityMeasure P] in
/-- The Bochner integral of a square as the extended integral of the squared norm. -/
theorem LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal {X : Ω → ℝ} (hX : AEStronglyMeasurable X P) :
    ∫ ω, X ω ^ 2 ∂P = (∫⁻ ω, (‖X ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω))
    ((hX.mul hX).congr (Filter.Eventually.of_forall fun ω => (pow_two (X ω)).symm))]
  congr 1
  exact lintegral_congr fun ω => (sq_nnnorm_eq_ofReal_sq (X ω)).symm
omit [IsProbabilityMeasure P] in
/-- The square of a square-integrable function is integrable. -/
theorem LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp {X : Ω → ℝ} (hX : MemLp X 2 P) :
    Integrable (fun ω => X ω ^ 2) P := by
  have h := hX.integrable_mul hX
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact (pow_two (X ω)).symm
section Parallelogram
omit [IsProbabilityMeasure P] in
/-- **A parallelogram of squared distances forces additivity.** If the squared `L²`-distances
among `u`, `v` and `w` are those of the sides and diagonals of a parallelogram, then `w` is the
sum of `u` and `v`. -/
theorem solution {u v w : Ω → ℝ}
    (hu : MemLp u 2 P) (hv : MemLp v 2 P) (hw : MemLp w 2 P) {A B C D : ℝ≥0∞}
    (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hC : C ≠ ⊤) (hD : D ≠ ⊤)
    (hSu : ∫⁻ ω, (‖u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = A)
    (hSv : ∫⁻ ω, (‖v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = B)
    (hSw : ∫⁻ ω, (‖w ω‖₊ : ℝ≥0∞) ^ 2 ∂P = C)
    (hSwu : ∫⁻ ω, (‖w ω - u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = B)
    (hSwv : ∫⁻ ω, (‖w ω - v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = A)
    (hSuv : ∫⁻ ω, (‖u ω - v ω‖₊ : ℝ≥0∞) ^ 2 ∂P = D)
    (hpar : C + D = 2 * A + 2 * B) :
    w =ᵐ[P] fun ω => u ω + v ω := by
  have eu : ∫ ω, u ω ^ 2 ∂P = A.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hu.aestronglyMeasurable, hSu]
  have ev : ∫ ω, v ω ^ 2 ∂P = B.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hv.aestronglyMeasurable, hSv]
  have ew : ∫ ω, w ω ^ 2 ∂P = C.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hw.aestronglyMeasurable, hSw]
  have ewu : ∫ ω, (w ω - u ω) ^ 2 ∂P = B.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal (X := fun ω => w ω - u ω)
      (hw.aestronglyMeasurable.sub hu.aestronglyMeasurable), hSwu]
  have ewv : ∫ ω, (w ω - v ω) ^ 2 ∂P = A.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal (X := fun ω => w ω - v ω)
      (hw.aestronglyMeasurable.sub hv.aestronglyMeasurable), hSwv]
  have euv : ∫ ω, (u ω - v ω) ^ 2 ∂P = D.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal (X := fun ω => u ω - v ω)
      (hu.aestronglyMeasurable.sub hv.aestronglyMeasurable), hSuv]
  have hreal : C.toReal + D.toReal = 2 * A.toReal + 2 * B.toReal := by
    have h := congrArg ENNReal.toReal hpar
    rwa [ENNReal.toReal_add hC hD,
      ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) hA) (ENNReal.mul_ne_top (by simp) hB),
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      show ((2 : ℝ≥0∞)).toReal = (2 : ℝ) by simp] at h
  have hF : Integrable (fun ω => (w ω - u ω - v ω) ^ 2) P :=
    LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp ((hw.sub hu).sub hv)
  have hW : Integrable (fun ω => w ω ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hw
  have hUV : Integrable (fun ω => (u ω - v ω) ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp (hu.sub hv)
  have hU : Integrable (fun ω => u ω ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hu
  have hV : Integrable (fun ω => v ω ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hv
  have hWU : Integrable (fun ω => (w ω - u ω) ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp (hw.sub hu)
  have hWV : Integrable (fun ω => (w ω - v ω) ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp (hw.sub hv)
  have hkey : ∫ ω, (w ω - u ω - v ω) ^ 2 ∂P = 0 := by
    have hid : ∀ ω : Ω, (w ω - u ω - v ω) ^ 2 + w ω ^ 2 + (u ω - v ω) ^ 2
        = u ω ^ 2 + v ω ^ 2 + (w ω - u ω) ^ 2 + (w ω - v ω) ^ 2 := fun ω => by ring
    have heq : ∫ ω, ((w ω - u ω - v ω) ^ 2 + w ω ^ 2 + (u ω - v ω) ^ 2) ∂P
        = ∫ ω, (u ω ^ 2 + v ω ^ 2 + (w ω - u ω) ^ 2 + (w ω - v ω) ^ 2) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    have hFW : Integrable (fun ω => (w ω - u ω - v ω) ^ 2 + w ω ^ 2) P := hF.add hW
    have hUV2 : Integrable (fun ω => u ω ^ 2 + v ω ^ 2) P := hU.add hV
    have hUV3 : Integrable (fun ω => u ω ^ 2 + v ω ^ 2 + (w ω - u ω) ^ 2) P := hUV2.add hWU
    rw [integral_add hFW hUV, integral_add hF hW,
      integral_add hUV3 hWV, integral_add hUV2 hWU,
      integral_add hU hV, eu, ev, ew, ewu, ewv, euv] at heq
    linarith
  have hzero : (fun ω => (w ω - u ω - v ω) ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hF).mp hkey
  filter_upwards [hzero] with ω hω
  have h2 : (w ω - u ω - v ω) ^ 2 = 0 := by simpa using hω
  have h0 : w ω - u ω - v ω = 0 := by nlinarith [h2, sq_nonneg (w ω - u ω - v ω)]
  linarith
