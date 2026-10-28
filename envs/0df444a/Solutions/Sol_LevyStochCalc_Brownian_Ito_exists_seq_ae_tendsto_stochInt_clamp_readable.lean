-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_clamp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:28:13.668562+00:00
-- url     : https://prove2.me/submissions/18d67298-9d50-4dfe-90fb-1f6ec4e34094

import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedLimit
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_seq_ae_tendsto_of_tendsto_lintegral_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_energy_diffusionIntegrand_clamp_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
section Clamped
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
section Limits
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ')
/-- **The stochastic integrals of the clamped approximation converge in `L²`.** -/
theorem LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_norm_stochInt_clamp
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ} (hT : 0 < T)
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (hmY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s))
    (hpY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
    (hqY : ∀ (i : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmX : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpX : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqX : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p : Fin n) (k : Fin d) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω,
        (‖stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
              (hmY i p k) (hpY i p k) (hqY i p k) T ω
            - stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmX p k) (hpX p k) (hqX p k) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (𝓝 0) := by
  refine Filter.Tendsto.congr (fun i => ?_)
    (tendsto_energy_diffusionIntegrand_clamp_readable hf'c hK₁0 hf'bd hm hq hYm hXm hge hae p k)
  exact (isometry_diff_stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
    (fun ω s => coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s)
    (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hmY i p k) (hmX p k) (hpY i p k) (hpX p k) (hqY i p k) (hqX p k) hT).symm
/-- **Along a further subsequence the stochastic integrals of the clamped approximation converge
almost surely.** -/
theorem solution
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ} (hT : 0 < T)
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (hmY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s))
    (hpY : ∀ (i : ℕ) (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      fun ω s => LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s)
    (hqY : ∀ (i : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmX : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s))
    (hpX : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ'
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
    (hqX : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧ ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      Filter.Tendsto (fun i : ℕ => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => LevyStochCalc.coordDeriv f' p (Y (ms i) s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns (ms i)) p k ω s)
          (hmY (ms i) p k) (hpY (ms i) p k) (hqY (ms i) p k) T ω) Filter.atTop
        (𝓝 (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
          (hmX p k) (hpX p k) (hqX p k) T ω)) := by
  classical
  obtain ⟨ms, hmsge, hms⟩ := LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral_readable (μ := P)
    (ι := Fin n × Fin d)
    (u := fun i c ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
      (fun ω s => LevyStochCalc.coordDeriv f' c.1 (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) c.1 c.2 ω s)
      (hmY i c.1 c.2) (hpY i c.1 c.2) (hqY i c.1 c.2) T ω)
    (v := fun c ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
      (fun ω s => LevyStochCalc.coordDeriv f' c.1 (X s ω) * H c.1 c.2 ω s)
      (hmX c.1 c.2) (hpX c.1 c.2) (hqX c.1 c.2) T ω)
    (fun i c => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W c.2) ℱ' (hcoord c.2) _
      (hmY i c.1 c.2) (hpY i c.1 c.2) (hqY i c.1 c.2) T).mono (ℱ'.le T)).measurable)
    (fun c => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W c.2) ℱ' (hcoord c.2) _
      (hmX c.1 c.2) (hpX c.1 c.2) (hqX c.1 c.2) T).mono (ℱ'.le T)).measurable)
    (fun c => LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_norm_stochInt_clamp W ℱ' hcoord hf'c hK₁0 hf'bd hm hT hq
      hYm hXm hge hae hmY hpY hqY hmX hpX hqX c.1 c.2)
  refine ⟨ms, hmsge, ?_⟩
  filter_upwards [hms] with ω hω
  intro p k
  exact hω (p, k)
