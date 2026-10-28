-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.ae_tendsto_drift_clamp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:35.181655+00:00
-- url     : https://prove2.me/submissions/d0b41dea-fb33-4c90-92d5-0671f6a50aa4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoTruncate
import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoProcessDiff
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
section Energy
variable {H₁ H₂ : Ω → ℝ → ℝ}
/-- The energy density of an integrand is measurable in the sample point. -/
theorem LevyStochCalc.Brownian.Ito.measurable_energyDensity (hm : Measurable (Function.uncurry H₁)) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
  have hf : Measurable fun p : Ω × ℝ => (‖H₁ p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2)
  exact hf.lintegral_prod_right'
end Energy
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoTruncate.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
open scoped NNReal ENNReal Topology
section Clamp
theorem LevyStochCalc.abs_clampAt_le_abs {j : ℝ} (hj : 0 ≤ j) (x : ℝ) : |clampAt j x| ≤ |x| := by
  unfold clampAt
  rcases le_or_gt x (-j) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ j), max_eq_left hx, abs_neg, abs_of_nonneg hj,
      abs_of_nonpos (by linarith : x ≤ 0)]
    linarith
  · rcases le_or_gt x j with hx' | hx'
    · rw [min_eq_right hx', max_eq_right hx.le]
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -j ≤ j), abs_of_nonneg hj,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
      linarith
theorem LevyStochCalc.clampAt_eq_self {j x : ℝ} (hx : |x| ≤ j) : clampAt j x = x := by
  rw [abs_le] at hx
  unfold clampAt
  rw [min_eq_right hx.2, max_eq_right hx.1]
end Clamp
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoProcessDiff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
section Diff
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
omit [IsProbabilityMeasure P] in
/-- A path with finite energy on a window is integrable there, almost surely. -/
theorem LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top {b : Ω → ℝ → ℝ}
    (hbm : Measurable (Function.uncurry b)) {t : ℝ}
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, IntegrableOn (b ω) (Set.Icc (0 : ℝ) t) volume := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  filter_upwards [MeasureTheory.ae_lt_top (measurable_energyDensity hbm t) hbq.ne] with ω hω
  exact (LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
    (Measurable.of_uncurry_left hbm) hω).integrable (by norm_num)
end Diff
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ContinuousLinearMap
variable {n : ℕ}
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
/-- A partial derivative is bounded by the operator norm of the Fréchet derivative. -/
theorem LevyStochCalc.abs_coordDeriv_le {K₁ : ℝ} (h : ∀ x, ‖f' x‖ ≤ K₁) (p : Fin n) (x : Fin n → ℝ) :
    |coordDeriv f' p x| ≤ K₁ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  calc |coordDeriv f' p x| = ‖f' x (Pi.single p 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖f' x‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ := (f' x).le_opNorm _
    _ = ‖f' x‖ := by rw [hnorm, mul_one]
    _ ≤ K₁ := h x
/-- Continuity of a partial derivative. -/
theorem LevyStochCalc.continuous_coordDeriv (hf'c : Continuous f') (p : Fin n) :
    Continuous (coordDeriv f' p) :=
  hf'c.clm_apply continuous_const
end Coord
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedIntegrands.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
section Clamped
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
section Limits
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
omit [IsProbabilityMeasure P] in
/-- Clamping at a level that grows to infinity converges to the identity. -/
theorem LevyStochCalc.Brownian.Ito.tendsto_clampAt_comp {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i) (x : ℝ) :
    Filter.Tendsto (fun i => clampAt ((ns i : ℕ) : ℝ) x) Filter.atTop (𝓝 x) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop N] with i hi
  refine (clampAt_eq_self ?_).symm
  have hle : (N : ℝ) ≤ ((ns i : ℕ) : ℝ) := by exact_mod_cast le_trans hi (hge i)
  linarith [hN]
omit [IsProbabilityMeasure P] in
/-- **The drift integrals of the clamped approximation converge, pathwise.** -/
theorem solution
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {T : ℝ}
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
    ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampDrift b (ns i) p ω s ∂volume) Filter.atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) T, LevyStochCalc.coordDeriv f' p (X s ω) * b p ω s ∂volume)) := by
  have hK₁0 : (0 : ℝ) ≤ K₁ := le_trans (norm_nonneg _) (hf'bd 0)
  have hint : ∀ p : Fin n, ∀ᵐ ω ∂P,
      IntegrableOn (b p ω) (Set.Icc (0 : ℝ) T) volume :=
    fun p => LevyStochCalc.Brownian.Ito.ae_integrableOn_of_energy_lt_top (hbm p) (hbq p)
  have hintall : ∀ᵐ ω ∂P, ∀ p : Fin n, IntegrableOn (b p ω) (Set.Icc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    exact hint
  filter_upwards [hae, hintall] with ω hω hbint
  intro p
  have haeIoc : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hω
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun s => K₁ * |b p ω s|) (fun i => ?_) ?_ (fun i => ?_) ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    exact (((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp
      (Measurable.of_uncurry_left (hYm i))).mul
      ((LevyStochCalc.continuous_clampAt (((ns i : ℕ) : ℝ))).measurable.comp
        (Measurable.of_uncurry_left (hbm p))))
  · exact ((hbint p).mono_set Set.Ioc_subset_Icc_self).abs.const_mul K₁
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (LevyStochCalc.abs_coordDeriv_le hf'bd p _)
      (LevyStochCalc.abs_clampAt_le_abs (Nat.cast_nonneg _) _) (abs_nonneg _) hK₁0
  · filter_upwards [haeIoc] with s hs
    exact ((LevyStochCalc.continuous_coordDeriv hf'c p).continuousAt.tendsto.comp hs).mul
      (LevyStochCalc.Brownian.Ito.tendsto_clampAt_comp hge (b p ω s))
