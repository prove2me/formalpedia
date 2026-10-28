-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.tendsto_energy_diffusionIntegrand_clamp_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:23:46.688448+00:00
-- url     : https://prove2.me/submissions/9de5aba7-aabe-42a9-8616-0d59a79b5bb4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoCutoff
import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedIntegrands
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_energy_clampAt_sub_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_energy_coordDeriv_diff_readable

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
/-- The squared extended norm of a real number is the extended real of its square. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq (z : ℝ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := by
  rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
section Energy
variable {H₁ H₂ : Ω → ℝ → ℝ}
/-- The squared extended norm of a sum is dominated by twice the sum of the squares. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  rw [sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])
end Energy
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
end Coord
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoCutoff.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open scoped Topology
section
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u
section Bounded
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- A pointwise bound `|u| ≤ c|v|` squares into a bound on the extended norms. -/
theorem LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le {c : ℝ} (hc : 0 ≤ c) {u v : ℝ} (h : |u| ≤ c * |v|) :
    (‖u‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (c ^ 2) * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have h1 : ‖u‖₊ ≤ Real.toNNReal c * ‖v‖₊ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [Real.coe_toNNReal c hc]
    simpa [Real.norm_eq_abs] using h
  calc (‖u‖₊ : ℝ≥0∞) ^ 2 ≤ ((Real.toNNReal c * ‖v‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 := by
        exact pow_le_pow_left' (by exact_mod_cast h1) 2
    _ = ENNReal.ofReal (c ^ 2) * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.coe_mul, mul_pow, ← ENNReal.coe_pow, ← Real.toNNReal_pow hc]
        rfl
end Bounded
end
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
/-- Additivity of the window energy. -/
theorem LevyStochCalc.Brownian.Ito.lintegral_window_add {f g : Ω → ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (f ω s + g ω s) ∂volume ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, g ω s ∂volume ∂P := by
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (f ω s + g ω s) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, g ω s ∂volume :=
    fun ω => MeasureTheory.lintegral_add_left (Measurable.of_uncurry_left hf) _
  simp_rw [hinner]
  exact MeasureTheory.lintegral_add_left hf.lintegral_prod_right' _
omit [IsProbabilityMeasure P] in
/-- Constants come out of the window energy. -/
theorem LevyStochCalc.Brownian.Ito.lintegral_window_const_mul {f : Ω → ℝ → ℝ≥0∞}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, c * f ω s ∂volume ∂P
      = c * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume ∂P := by
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, c * f ω s ∂volume
      = c * ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume :=
    fun ω => MeasureTheory.lintegral_const_mul' _ _ hc
  simp_rw [hinner]
  exact MeasureTheory.lintegral_const_mul' _ _ hc
/-- **The energies of the differences of the diffusion integrands vanish.** -/
theorem solution
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (p : Fin n) (k : Fin d) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s
          - LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (𝓝 0) := by
  have hnsTop : Filter.Tendsto ns Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hge Filter.tendsto_id
  have hclamp : Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (𝓝 0) :=
    (LevyStochCalc.Brownian.Ito.tendsto_energy_clampAt_sub_readable (hm p k) (hq p k).ne).comp hnsTop
  have hderiv := LevyStochCalc.Brownian.Ito.tendsto_energy_coordDeriv_diff_readable hf'c hK₁0 hf'bd (hm p k) (hq p k)
    hYm hXm hae p
  have hbound : ∀ (i : ℕ) (ω : Ω) (s : ℝ),
      (‖LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s
        - LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (ENNReal.ofReal (K₁ ^ 2)
          * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
        + 2 * (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
      := by
    intro i ω s
    have hsplit : LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s
        - LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s
        = LevyStochCalc.coordDeriv f' p (Y i s ω) * (LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s)
          + (LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * H p k ω s := by ring
    rw [hsplit]
    set A : ℝ := LevyStochCalc.coordDeriv f' p (Y i s ω) * (LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s) with hA
    set B : ℝ := (LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * H p k ω s with hB
    have hAle : (‖A‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (K₁ ^ 2)
          * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 := by
      rw [hA]
      refine LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le hK₁0 ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (LevyStochCalc.abs_coordDeriv_le hf'bd p _) (abs_nonneg _)
    calc (‖A + B‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖A‖₊ : ℝ≥0∞) ^ 2 + (‖B‖₊ : ℝ≥0∞) ^ 2) := LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul A B
      _ = 2 * (‖A‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖B‖₊ : ℝ≥0∞) ^ 2 := by rw [mul_add]
      _ ≤ 2 * (ENNReal.ofReal (K₁ ^ 2)
            * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
          + 2 * (‖B‖₊ : ℝ≥0∞) ^ 2 := by
          exact add_le_add (mul_le_mul' le_rfl hAle) le_rfl
  have hlimbound : Filter.Tendsto (fun i : ℕ =>
      2 * (ENNReal.ofReal (K₁ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun i : ℕ =>
        2 * (ENNReal.ofReal (K₁ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        Filter.atTop (𝓝 0) := by
      have hc := ENNReal.Tendsto.const_mul (a := 2 * ENNReal.ofReal (K₁ ^ 2)) hclamp
        (Or.inr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))
      rw [mul_zero] at hc
      exact hc.congr fun i => by rw [mul_assoc]
    have h2 : Filter.Tendsto (fun i : ℕ =>
        2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P) Filter.atTop (𝓝 0) := by
      have hc := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hderiv (Or.inr (by simp))
      rw [mul_zero] at hc
      exact hc
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimbound
    (fun i => zero_le) (fun i => ?_)
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖LevyStochCalc.coordDeriv f' p (Y i s ω) * LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s
          - LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (2 * (ENNReal.ofReal (K₁ ^ 2)
              * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            + 2 * (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω))
                * H p k ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω =>
          MeasureTheory.lintegral_mono fun s => hbound i ω s
    _ = _ := by
        have hAm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
            ENNReal.ofReal (K₁ ^ 2)
              * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2) :=
          ((((LevyStochCalc.Brownian.Ito.measurable_clampCoeff hm (ns i) p k).sub
            (hm p k)).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.const_mul _
        rw [LevyStochCalc.Brownian.Ito.lintegral_window_add
            (g := fun ω s => 2 * (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω))
                * H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            (hAm.const_mul _) T,
          LevyStochCalc.Brownian.Ito.lintegral_window_const_mul
            (f := fun ω s => ENNReal.ofReal (K₁ ^ 2)
                * (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            (by simp) T,
          LevyStochCalc.Brownian.Ito.lintegral_window_const_mul
            (f := fun ω s => (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω))
                * H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            (by simp) T,
          LevyStochCalc.Brownian.Ito.lintegral_window_const_mul
            (f := fun ω s => (‖LevyStochCalc.Brownian.Ito.clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            (by simp : ENNReal.ofReal (K₁ ^ 2) ≠ ⊤) T]
