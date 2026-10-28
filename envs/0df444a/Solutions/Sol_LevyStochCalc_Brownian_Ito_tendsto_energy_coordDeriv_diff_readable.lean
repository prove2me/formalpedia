-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.tendsto_energy_coordDeriv_diff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:37.287575+00:00
-- url     : https://prove2.me/submissions/34ff0efd-d293-4dff-ba79-39a18876c57c

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoTimeRiemann
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoCutoff
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

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoTimeRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The absolute value of a difference is at most the sum of the absolute values. -/
theorem LevyStochCalc.Brownian.Ito.abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  simpa using abs_add_le a (-b)
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
/-- **The energies of the perturbed diffusion integrands vanish.** -/
theorem solution
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {G : Ω → ℝ → ℝ} (hmG : Measurable (Function.uncurry G)) {T : ℝ}
    (hqG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (p : Fin n) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P) Filter.atTop (𝓝 0) := by
  set c : ℝ := 2 * K₁ with hc
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hbnd : ∀ (i : ℕ) (ω : Ω) (s : ℝ),
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (c ^ 2) * (‖G ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro i ω s
    refine LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le hc0 ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    calc |LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)|
        ≤ |LevyStochCalc.coordDeriv f' p (Y i s ω)| + |LevyStochCalc.coordDeriv f' p (X s ω)| :=
          LevyStochCalc.Brownian.Ito.abs_sub_le_abs_add_abs _ _
      _ ≤ K₁ + K₁ := add_le_add (LevyStochCalc.abs_coordDeriv_le hf'bd p _) (LevyStochCalc.abs_coordDeriv_le hf'bd p _)
      _ = c := by rw [hc]; ring
  have hjoint : ∀ i : ℕ, Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      (LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s) := by
    intro i
    exact (((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp (hYm i)).sub
      ((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp hXm)).mul hmG
  have hFmeas : ∀ i : ℕ, Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun i => LevyStochCalc.Brownian.Ito.measurable_energyDensity (hjoint i) T
  have hGmeas : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := LevyStochCalc.Brownian.Ito.measurable_energyDensity hmG T
  -- inner limit, for almost every path
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun i : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (𝓝 0) := by
    filter_upwards [hae, MeasureTheory.ae_lt_top hGmeas hqG.ne] with ω hω hfin
    have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (F := fun (i : ℕ) (s : ℝ) =>
        (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2)
      (f := fun _s : ℝ => (0 : ℝ≥0∞))
      (bound := fun s => ENNReal.ofReal (c ^ 2) * (‖G ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun i => (((Measurable.of_uncurry_left (hjoint i)).nnnorm).coe_nnreal_ennreal).pow_const 2)
      (fun i => Filter.Eventually.of_forall fun s => hbnd i ω s) ?_ ?_
    · simpa using hlim
    · rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne
    · filter_upwards [hω] with s hs
      have hcd : Filter.Tendsto (fun i : ℕ => LevyStochCalc.coordDeriv f' p (Y i s ω)) Filter.atTop
          (𝓝 (LevyStochCalc.coordDeriv f' p (X s ω))) :=
        (LevyStochCalc.continuous_coordDeriv hf'c p).continuousAt.tendsto.comp hs
      have hconstX : Filter.Tendsto (fun _ : ℕ => LevyStochCalc.coordDeriv f' p (X s ω)) Filter.atTop
          (𝓝 (LevyStochCalc.coordDeriv f' p (X s ω))) := tendsto_const_nhds
      have hconstG : Filter.Tendsto (fun _ : ℕ => G ω s) Filter.atTop (𝓝 (G ω s)) :=
        tendsto_const_nhds
      have hzero : Filter.Tendsto (fun i : ℕ =>
          (LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s) Filter.atTop (𝓝 0) := by
        have hs2 := (hcd.sub hconstX).mul hconstG
        simpa using hs2
      have hcont : Continuous fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2 := by
        have h1 : Continuous fun x : ℝ => (‖x‖₊ ^ 2 : ℝ≥0) := continuous_nnnorm.pow 2
        have h2 := ENNReal.continuous_coe.comp h1
        simp only [Function.comp_def, ENNReal.coe_pow] at h2
        exact h2
      have hres := (hcont.tendsto (0 : ℝ)).comp hzero
      simp only [Function.comp_def] at hres
      have hz0 : ((‖(0 : ℝ)‖₊ : ℝ≥0∞)) ^ 2 = 0 := by simp
      rw [hz0] at hres
      exact hres
  have hdom : ∀ (i : ℕ) (ω : Ω), (∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      ≤ ENNReal.ofReal (c ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro i ω
    rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
    exact MeasureTheory.lintegral_mono fun s => hbnd i ω s
  -- outer limit
  have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (μ := P)
    (F := fun (i : ℕ) (ω : Ω) => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(LevyStochCalc.coordDeriv f' p (Y i s ω) - LevyStochCalc.coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    (f := fun _ω : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ENNReal.ofReal (c ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas
    (fun i => Filter.Eventually.of_forall fun ω => hdom i ω) ?_ hinner
  · simpa using hlim
  · rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hqG).ne
