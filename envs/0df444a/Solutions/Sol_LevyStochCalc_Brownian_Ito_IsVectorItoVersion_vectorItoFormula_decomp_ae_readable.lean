-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.IsVectorItoVersion.vectorItoFormula_decomp_ae_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:40.525981+00:00
-- url     : https://prove2.me/submissions/ee59c7a1-5427-4851-b57e-7ba8b8d8fee4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormulaDecomp
import Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_apply_fderiv_eq_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_sum_apply_fderiv_two_eq_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section Decomposition
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
/-- **The grid decomposition of Itô's formula in the vector case.** The defect of the formula on
`[0, T]` equals the second-order Taylor remainder along the uniform grid plus the errors of the
drift, martingale and quadratic-variation Riemann sums. -/
theorem solution
    (h : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ}
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume))
      =ᵐ[P] fun ω : Ω =>
        LevyStochCalc.taylorRemainderNormed f f' f'' (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m
        + (∑ p : Fin n, ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume))
        + (∑ p : Fin n, ∑ k : Fin d,
            ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
                * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                  - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                  (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
                  (hmg p k) (hpg p k) (hqg p k) T ω))
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
                * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
                  * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
              - ∫ s in Set.Ioc (0 : ℝ) T,
                  LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) := by
  filter_upwards [LevyStochCalc.Brownian.Ito.sum_apply_fderiv_eq_readable h hbm hB f' hT hm0] with ω hω1
  have hsecond := LevyStochCalc.Brownian.Ito.sum_apply_fderiv_two_eq_readable f'' (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m
  have htay : LevyStochCalc.taylorRemainderNormed f f' f'' (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m
      = f (X T ω) - f (X 0 ω)
        - ((∑ i ∈ Finset.range m, f' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
          + ∑ i ∈ Finset.range m, f'' (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) / 2) := by
    simp only [LevyStochCalc.taylorRemainderNormed, LevyStochCalc.Brownian.Ito.unifGrid_self hm0, LevyStochCalc.Brownian.Ito.unifGrid_zero]
  rw [htay, hω1, hsecond]
  simp only [Finset.sum_sub_distrib]
  ring
