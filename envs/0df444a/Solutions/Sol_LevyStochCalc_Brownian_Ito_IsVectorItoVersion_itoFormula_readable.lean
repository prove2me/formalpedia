-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:44:17.39839+00:00
-- url     : https://prove2.me/submissions/7059b6cc-505a-4134-ad71-41eab562bf81

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormula
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_integral_abs_vectorItoFormula_le_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormula.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
@[simp] theorem LevyStochCalc.Brownian.Ito.vectorItoGridError_zero (nR dR B C T A K K₂ : ℝ) :
    vectorItoGridError nR dR B C T A K K₂ 0 = A * vectorItoGridResidue nR dR C T := by
  simp only [vectorItoGridError, vectorItoGridResidue]
  norm_num
  ring
theorem LevyStochCalc.Brownian.Ito.continuous_vectorItoGridError (nR dR B C T A K K₂ : ℝ) :
    Continuous (vectorItoGridError nR dR B C T A K K₂) := by
  unfold vectorItoGridError
  fun_prop
theorem LevyStochCalc.Brownian.Ito.tendsto_vectorItoGridError (nR dR B C T A K K₂ : ℝ) :
    Filter.Tendsto (fun m : ℕ => vectorItoGridError nR dR B C T A K K₂ (T / (m : ℝ)))
      Filter.atTop (𝓝 (A * vectorItoGridResidue nR dR C T)) := by
  have hx : Filter.Tendsto (fun m : ℕ => T / (m : ℝ)) Filter.atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hcomp := ((continuous_vectorItoGridError nR dR B C T A K K₂).tendsto 0).comp hx
  rwa [vectorItoGridError_zero] at hcomp
section Formula
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
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)
include hC0 hCH in
/-- **Itô's formula for a vector Itô process.** For a continuous adapted version `X` of
`X₀ + ∫ b ds + ∑ₖ ∫ H^{·,k} dWᵏ` with bounded coefficients, and `f` twice Fréchet differentiable
with bounded derivatives and uniformly continuous second derivative,

  `f(X_T) − f(X_0) = ∑_p ∫_0^T ∂_p f(X_s) b^p_s ds + ∑_{p,k} ∫_0^T ∂_p f(X_s) H^{p,k}_s dWᵏ_s
      + ½ ∑_{p,q} ∫_0^T ∂²_{pq} f(X_s) (∑ₖ H^{p,k}_s H^{q,k}_s) ds`

almost surely. -/
theorem solution
    (h : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    (hf''c : Continuous f'')
    (hf''unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖f'' z - f'' w‖ ≤ ε)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
  have haff : ∀ ε : ℝ, 0 < ε →
      ∃ Kε : ℝ, 0 ≤ Kε ∧ ∀ z w, ‖f'' z - f'' w‖ ≤ ε + Kε * ‖z - w‖ := by
    intro ε hε
    obtain ⟨δ, hδ0, hδ⟩ := hf''unif ε hε
    refine ⟨2 * K₂ / δ, by positivity, fun z w => ?_⟩
    have hnn : (0 : ℝ) ≤ 2 * K₂ / δ * ‖z - w‖ := by positivity
    rcases lt_or_ge ‖z - w‖ δ with hlt | hge
    · have hle : ‖f'' z - f'' w‖ ≤ ε := hδ z w hlt
      linarith
    · have h1 : ‖f'' z - f'' w‖ ≤ 2 * K₂ := by
        refine (norm_sub_le (f'' z) (f'' w)).trans ?_
        linarith [hf''bd z, hf''bd w]
      have h2 : 2 * K₂ / δ * δ ≤ 2 * K₂ / δ * ‖z - w‖ :=
        mul_le_mul_of_nonneg_left hge (by positivity)
      rw [div_mul_cancel₀ _ (ne_of_gt hδ0)] at h2
      linarith
  obtain ⟨K₁ε, hK₁ε0, haff1⟩ := haff 1 one_pos
  obtain ⟨hZint, -⟩ := h.integral_abs_vectorItoFormula_le_readable hC0 hCH hX₀ hbm hB0 hB hma hpa hqa
    hf hf' hf'bd hK₂0 hf''bd zero_le_one hK₁ε0 hf''c haff1 hmg hpg hqg hT one_ne_zero
  have hkey : ∀ ε : ℝ, 0 < ε →
      ∫ ω, |f (X T ω) - f (X 0 ω)
          - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
        ≤ ε * LevyStochCalc.Brownian.Ito.vectorItoGridResidue (n : ℝ) (d : ℝ) C T := by
    intro ε hε
    obtain ⟨Kε, hKε0, haffε⟩ := haff ε hε
    have hgrid := fun (m : ℕ) (hm0 : m ≠ 0) =>
      h.integral_abs_vectorItoFormula_le_readable hC0 hCH hX₀ hbm hB0 hB hma hpa hqa hf hf' hf'bd
        hK₂0 hf''bd hε.le hKε0 hf''c haffε hmg hpg hqg hT hm0
    exact ge_of_tendsto (LevyStochCalc.Brownian.Ito.tendsto_vectorItoGridError (n : ℝ) (d : ℝ) B C T ε Kε K₂)
      ((Filter.eventually_gt_atTop 0).mono fun m hmpos => (hgrid m hmpos.ne').2)
  have htend : Filter.Tendsto
      (fun j : ℕ => (1 / ((j : ℝ) + 1)) * LevyStochCalc.Brownian.Ito.vectorItoGridResidue (n : ℝ) (d : ℝ) C T)
      Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using h1.mul_const (LevyStochCalc.Brownian.Ito.vectorItoGridResidue (n : ℝ) (d : ℝ) C T)
  have hzero := ge_of_tendsto htend (Filter.Eventually.of_forall fun j : ℕ =>
    hkey (1 / ((j : ℝ) + 1)) (by positivity))
  have hae := (MeasureTheory.integral_eq_zero_iff_of_nonneg
    (fun ω => abs_nonneg _) hZint.abs).mp
    (le_antisymm hzero (MeasureTheory.integral_nonneg fun ω => abs_nonneg _))
  filter_upwards [hae] with ω hω
  have hz := abs_eq_zero.mp hω
  linarith
