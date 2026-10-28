-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.ae_eq_const_mul_of_sq_distances_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:07.386265+00:00
-- url     : https://prove2.me/submissions/25905040-ee8f-4d5b-bac0-19c4a5b020c1

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
section Scaling
omit [IsProbabilityMeasure P] in
/-- **Squared distances of a scalar multiple force the scalar relation.** -/
theorem solution {x y : Ω → ℝ} (hx : MemLp x 2 P) (hy : MemLp y 2 P)
    {c : ℝ} {X Y Z : ℝ≥0∞}
    (hSx : ∫⁻ ω, (‖x ω‖₊ : ℝ≥0∞) ^ 2 ∂P = X)
    (hSy : ∫⁻ ω, (‖y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Y)
    (hSxy : ∫⁻ ω, (‖x ω - y ω‖₊ : ℝ≥0∞) ^ 2 ∂P = Z)
    (hXY : X.toReal = c ^ 2 * Y.toReal) (hZY : Z.toReal = (c - 1) ^ 2 * Y.toReal) :
    x =ᵐ[P] fun ω => c * y ω := by
  have ex : ∫ ω, x ω ^ 2 ∂P = X.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hx.aestronglyMeasurable, hSx]
  have ey : ∫ ω, y ω ^ 2 ∂P = Y.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal hy.aestronglyMeasurable, hSy]
  have exy : ∫ ω, (x ω - y ω) ^ 2 ∂P = Z.toReal := by
    rw [LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal (X := fun ω => x ω - y ω)
      (hx.aestronglyMeasurable.sub hy.aestronglyMeasurable), hSxy]
  have hsub : Integrable (fun ω => (x ω - y ω) ^ 2) P := LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp (hx.sub hy)
  have hX2 : Integrable (fun ω => (1 - c) * x ω ^ 2) P :=
    (LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hx).const_mul _
  have hY2 : Integrable (fun ω => (c ^ 2 - c) * y ω ^ 2) P :=
    (LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp hy).const_mul _
  have hZ2 : Integrable (fun ω => c * (x ω - y ω) ^ 2) P := hsub.const_mul _
  have hF : Integrable (fun ω => (x ω - c * y ω) ^ 2) P := by
    have : MemLp (fun ω => x ω - c * y ω) 2 P := hx.sub (hy.const_mul c)
    exact LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp this
  have hkey : ∫ ω, (x ω - c * y ω) ^ 2 ∂P = 0 := by
    have hid : ∀ ω : Ω, (x ω - c * y ω) ^ 2
        = (1 - c) * x ω ^ 2 + ((c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2) := fun ω => by ring
    have h1 : ∫ ω, (x ω - c * y ω) ^ 2 ∂P
        = ∫ ω, ((1 - c) * x ω ^ 2 + ((c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2)) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hid)
    have hYZ : Integrable (fun ω => (c ^ 2 - c) * y ω ^ 2 + c * (x ω - y ω) ^ 2) P :=
      hY2.add hZ2
    rw [h1, integral_add hX2 hYZ, integral_add hY2 hZ2,
      integral_const_mul, integral_const_mul, integral_const_mul, ex, ey, exy, hXY, hZY]
    ring
  have hzero : (fun ω => (x ω - c * y ω) ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hF).mp hkey
  filter_upwards [hzero] with ω hω
  have h2 : (x ω - c * y ω) ^ 2 = 0 := by simpa using hω
  nlinarith [h2, sq_nonneg (x ω - c * y ω)]
