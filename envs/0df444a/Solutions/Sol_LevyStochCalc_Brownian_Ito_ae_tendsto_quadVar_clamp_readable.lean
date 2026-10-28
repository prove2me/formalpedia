-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.ae_tendsto_quadVar_clamp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:19:42.518543+00:00
-- url     : https://prove2.me/submissions/44ca2e54-5525-4b5a-953d-f69fd59cccb4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoTruncate
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ContinuousLinearMap
variable {n : ℕ}
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
/-- A second partial derivative is bounded by the operator norm of the second Fréchet
derivative. -/
theorem LevyStochCalc.abs_coordDeriv₂_le {K₂ : ℝ} (h : ∀ x, ‖f'' x‖ ≤ K₂) (p q : Fin n) (x : Fin n → ℝ) :
    |coordDeriv₂ f'' p q x| ≤ K₂ := by
  have hnorm : ‖(Pi.single p 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  have hnormq : ‖(Pi.single q 1 : Fin n → ℝ)‖ = 1 := by rw [Pi.norm_single, norm_one]
  calc |coordDeriv₂ f'' p q x| = ‖f'' x (Pi.single p 1) (Pi.single q 1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖f'' x‖ * ‖(Pi.single p 1 : Fin n → ℝ)‖ * ‖(Pi.single q 1 : Fin n → ℝ)‖ :=
        (f'' x).le_opNorm₂ _ _
    _ = ‖f'' x‖ := by rw [hnorm, hnormq, mul_one, mul_one]
    _ ≤ K₂ := h x
/-- Continuity of a second partial derivative. -/
theorem LevyStochCalc.continuous_coordDeriv₂ (hf''c : Continuous f'') (p q : Fin n) :
    Continuous (coordDeriv₂ f'' p q) :=
  (hf''c.clm_apply continuous_const).clm_apply continuous_const
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
/-- For almost every path, an integrand with finite energy is square integrable on the window. -/
theorem LevyStochCalc.Brownian.Ito.ae_memLp_two_window {G : Ω → ℝ → ℝ} (hmG : Measurable (Function.uncurry G)) {T : ℝ}
    (hqG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, MeasureTheory.MemLp (G ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  filter_upwards [MeasureTheory.ae_lt_top (measurable_energyDensity hmG T) hqG.ne] with ω hω
  exact LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
    (Measurable.of_uncurry_left hmG) hω
omit [IsProbabilityMeasure P] in
/-- **The quadratic-variation integrals of the clamped approximation converge, pathwise.** -/
theorem solution
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} (hf''c : Continuous f'')
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
    ∀ᵐ ω ∂P, ∀ p q : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.coordDeriv₂ f'' p q (Y i s ω)
          * ∑ k : Fin d, LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) q k ω s ∂volume)
      Filter.atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) := by
  have hmemall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      MeasureTheory.MemLp (H p k ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact LevyStochCalc.Brownian.Ito.ae_memLp_two_window (hm p k) (hq p k)
  filter_upwards [hae, hmemall] with ω hω hmem
  intro p q
  have haeIoc : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hω
  have hprodint : ∀ k : Fin d,
      IntegrableOn (fun s => |H p k ω s * H q k ω s|) (Set.Ioc (0 : ℝ) T) volume := by
    intro k
    have h0 : IntegrableOn (fun s => |H p k ω s * H q k ω s|) (Set.Icc (0 : ℝ) T) volume :=
      (MeasureTheory.MemLp.integrable_mul (p := 2) (q := 2) (hmem p k) (hmem q k)).abs
    exact h0.mono_set Set.Ioc_subset_Icc_self
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun s => K₂ * ∑ k : Fin d, |H p k ω s * H q k ω s|) (fun i => ?_) ?_ (fun i => ?_) ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    refine ((LevyStochCalc.continuous_coordDeriv₂ hf''c p q).measurable.comp
      (Measurable.of_uncurry_left (hYm i))).mul ?_
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((LevyStochCalc.continuous_clampAt (((ns i : ℕ) : ℝ))).measurable.comp
      (Measurable.of_uncurry_left (hm p k))).mul
      ((LevyStochCalc.continuous_clampAt (((ns i : ℕ) : ℝ))).measurable.comp
        (Measurable.of_uncurry_left (hm q k)))
  · exact (MeasureTheory.integrable_finsetSum _ fun k _ => hprodint k).const_mul K₂
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (LevyStochCalc.abs_coordDeriv₂_le hf''bd p q _) ?_ (abs_nonneg _) hK₂0
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (LevyStochCalc.abs_clampAt_le_abs (Nat.cast_nonneg _) _)
      (LevyStochCalc.abs_clampAt_le_abs (Nat.cast_nonneg _) _) (abs_nonneg _) (abs_nonneg _)
  · filter_upwards [haeIoc] with s hs
    refine ((LevyStochCalc.continuous_coordDeriv₂ hf''c p q).continuousAt.tendsto.comp hs).mul ?_
    exact tendsto_finsetSum _ fun k _ =>
      (LevyStochCalc.Brownian.Ito.tendsto_clampAt_comp hge (H p k ω s)).mul (LevyStochCalc.Brownian.Ito.tendsto_clampAt_comp hge (H q k ω s))
