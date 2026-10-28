-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_frozenRiemann_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:34:53.577849+00:00
-- url     : https://prove2.me/submissions/a67c0caf-d063-4b54-86bc-e662632adb29

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentBounds
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaGrid
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoTimeRiemann
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoTimeRiemann
import Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_lintegral_window_norm_sub_le_readable
import Theorems.Thm_LevyStochCalc_abs_setIntegral_Ioc_le_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
/-- A bounded measurable function is integrable on any set of finite measure. -/
theorem LevyStochCalc.integrableOn_of_bounded_of_measurable {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn f s volume := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := B) hs hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB u
/-- The integral of a jointly measurable function over a fixed set is measurable in the
parameter. -/
theorem LevyStochCalc.measurable_setIntegral {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (s : Set ℝ) :
    Measurable fun ω => ∫ t in s, f ω t ∂volume :=
  (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict s) hf.stronglyMeasurable).measurable
/-- The integral of a jointly measurable function over a fixed window is measurable in the
parameter. -/
theorem LevyStochCalc.measurable_setIntegral_Ioc {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (a b : ℝ) :
    Measurable fun ω => ∫ s in Set.Ioc a b, f ω s ∂volume :=
  measurable_setIntegral hf (Set.Ioc a b)
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentBounds.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A pointwise-nonnegative integrand is bounded through its `lintegral`. -/
theorem LevyStochCalc.Brownian.Ito.integral_le_of_lintegral_ofReal_le {P : Measure Ω} {f : Ω → ℝ}
    (hint : MeasureTheory.Integrable f P) (hnn : ∀ ω, 0 ≤ f ω) {K : ℝ} (hK : 0 ≤ K)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal K) : ∫ ω, f ω ∂P ≤ K := by
  rw [← ENNReal.ofReal_le_ofReal_iff hK,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  exact h
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessVersion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorVersion
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}
/-- A version's time slices are measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable
/-- A version's paths are jointly measurable in the sample point and the time. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    Measurable (Function.uncurry fun ω s => X s ω) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable h.continuous_path h.measurable
  exact hjoint.comp measurable_swap
/-- A measurable function of a version is jointly measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry_comp
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Measurable φ) : Measurable (Function.uncurry fun ω s => φ (X s ω)) :=
  hφ.comp h.measurable_uncurry
end VectorVersion
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaGrid.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.unifGrid_nonneg {T : ℝ} (hT : 0 ≤ T) (m i : ℕ) : 0 ≤ unifGrid T m i := by
  rw [unifGrid]
  positivity
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
/-- A bounded measurable function is interval integrable on every interval. -/
theorem LevyStochCalc.Brownian.Ito.intervalIntegrable_of_bounded {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hgM : ∀ s, |g s| ≤ M) (a b : ℝ) : IntervalIntegrable g volume a b :=
  intervalIntegrable_iff.mpr
    (integrableOn_of_bounded_of_measurable hg hgM (by simp [Set.uIoc_eq_union]))
/-- **The uniform grid partitions the time integral.** -/
theorem LevyStochCalc.Brownian.Ito.sum_setIntegral_unifGrid {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) {g : ℝ → ℝ}
    (hg : Measurable g) {M : ℝ} (hgM : ∀ s, |g s| ≤ M) :
    ∑ i ∈ Finset.range m, ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
        g s ∂volume
      = ∫ s in Set.Ioc (0 : ℝ) T, g s ∂volume := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := unifGrid T m) (f := g) (μ := volume) (n := m)
    (fun k _ => intervalIntegrable_of_bounded hg hgM _ _)
  rw [unifGrid_zero, unifGrid_self hm0] at hsum
  rw [← intervalIntegral.integral_of_le hT.le, ← hsum]
  exact Finset.sum_congr rfl fun i _ =>
    (intervalIntegral.integral_of_le (unifGrid_lt_succ hT hm0 i).le).symm
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoTimeRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorRiemann
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
include hC0 hCH in
/-- **A frozen-weight Riemann sum converges in `L¹` at rate `√(T/m)`.** For a bounded
`L`-Lipschitz `φ` on the state space and a bounded time density `wgt`, the sum of `φ(X_{tᵢ})`
against the cell integrals of `wgt` approximates `∫_0^T φ(X_s)·wgt_s ds`. -/
theorem solution
    (h : LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    (wgt : Ω → ℝ → ℝ) (hwm : Measurable (Function.uncurry wgt))
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ (ω : Ω) (s : ℝ), |wgt ω s| ≤ A)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {Mφ L : ℝ} (hMφ0 : 0 ≤ Mφ) (hL0 : 0 ≤ L)
    (hφaff : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ Mφ + L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω =>
        (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| ∂P
        ≤ Mφ * A * T + L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hKφ0 : 0 ≤ Kφ := le_trans (abs_nonneg _) (hφbd 0)
  have hLA0 : (0 : ℝ) ≤ L * A := mul_nonneg hL0 hA0
  have hcellT : ∀ i : ℕ, volume (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) ≠ ⊤ :=
    fun i => (measure_Ioc_lt_top).ne
  have hXmeas : ∀ ω : Ω, Measurable fun s => X s ω := fun ω => (h.continuous_path ω).measurable
  have hwmeas : ∀ ω : Ω, Measurable (wgt ω) := fun ω => Measurable.of_uncurry_left hwm
  have hgmeas : ∀ ω : Ω, Measurable fun s => φ (X s ω) * wgt ω s := fun ω =>
    (hφc.measurable.comp (hXmeas ω)).mul (hwmeas ω)
  have hgbd : ∀ (ω : Ω) (s : ℝ), |φ (X s ω) * wgt ω s| ≤ Kφ * A := by
    intro ω s
    rw [abs_mul]
    exact mul_le_mul (hφbd _) (hA ω s) (abs_nonneg _) hKφ0
  have hcellb : ∀ (ω : Ω) (i : ℕ), IntegrableOn (wgt ω)
      (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := fun ω i =>
    LevyStochCalc.integrableOn_of_bounded_of_measurable (hwmeas ω) (hA ω) (hcellT i)
  have hcellg : ∀ (ω : Ω) (i : ℕ),
      IntegrableOn (fun s => φ (X s ω) * wgt ω s)
        (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := fun ω i =>
    LevyStochCalc.integrableOn_of_bounded_of_measurable (hgmeas ω) (hgbd ω) (hcellT i)
  have hcelld : ∀ (ω : Ω) (i : ℕ),
      IntegrableOn (fun s => (φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) * wgt ω s)
        (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := by
    intro ω i
    refine LevyStochCalc.integrableOn_of_bounded_of_measurable (B := (Kφ + Kφ) * A)
      (f := fun s => (φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) * wgt ω s)
      (((measurable_const).sub (hφc.measurable.comp (hXmeas ω))).mul (hwmeas ω))
      (fun s => ?_) (hcellT i)
    rw [abs_mul]
    exact mul_le_mul ((LevyStochCalc.Brownian.Ito.abs_sub_le_abs_add_abs _ _).trans (add_le_add (hφbd _) (hφbd _)))
      (hA ω s) (abs_nonneg _) (by linarith)
  have hcellL : ∀ (ω : Ω) (i : ℕ),
      IntegrableOn (fun s => L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖)
        (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := by
    intro ω i
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
    exact Continuous.integrableOn_Icc
      (continuous_const.mul ((continuous_const.sub (h.continuous_path ω)).norm))
  have hcellC : ∀ i : ℕ, IntegrableOn (fun _ : ℝ => Mφ * A)
      (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := by
    intro i
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
    exact Continuous.integrableOn_Icc continuous_const
  have hcellLM : ∀ (ω : Ω) (i : ℕ),
      IntegrableOn (fun s => Mφ * A + L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖)
        (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := fun ω i =>
    (hcellC i).add (hcellL ω i)
  have hpart : ∀ ω : Ω,
      ∑ i ∈ Finset.range m, ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          φ (X s ω) * wgt ω s ∂volume
        = ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume := fun ω =>
    LevyStochCalc.Brownian.Ito.sum_setIntegral_unifGrid hT hm0 (hgmeas ω) (hgbd ω)
  have hcell : ∀ (ω : Ω) (i : ℕ),
      φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
        - ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), φ (X s ω) * wgt ω s ∂volume
      = ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          (φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) * wgt ω s ∂volume := by
    intro ω i
    rw [← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub ((hcellb ω i).const_mul _) (hcellg ω i)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    ring
  have hcellvol : ∀ i : ℕ,
      (volume : Measure ℝ).real (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)))
        = T / (m : ℝ) := by
    intro i
    rw [Real.volume_real_Ioc_of_le (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le, LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i]
  have hcellle : ∀ (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          (φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) * wgt ω s ∂volume|
      ≤ Mφ * A * (T / (m : ℝ))
        + ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
            L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume := by
    intro ω i
    refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
    have hstep : ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
        |(φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) * wgt ω s| ∂volume
        ≤ ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
            (Mφ * A + L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖) ∂volume := by
      refine MeasureTheory.integral_mono (hcelld ω i).abs (hcellLM ω i) fun s => ?_
      rw [abs_mul]
      calc |φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)| * |wgt ω s|
          ≤ (Mφ + L * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖) * A :=
            mul_le_mul (hφaff _ _) (hA ω s) (abs_nonneg _)
              (by positivity)
        _ = Mφ * A + L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ := by ring
    refine hstep.trans (le_of_eq ?_)
    rw [MeasureTheory.integral_add (hcellC i) (hcellL ω i),
      MeasureTheory.setIntegral_const, hcellvol i, smul_eq_mul]
    ring
  have hZ : ∀ ω : Ω,
      |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume|
      ≤ Mφ * A * T
        + ∑ i ∈ Finset.range m, ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
            L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume := by
    intro ω
    rw [← hpart ω, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hsum : ∑ i ∈ Finset.range m,
        |φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
            - ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                φ (X s ω) * wgt ω s ∂volume|
        ≤ ∑ i ∈ Finset.range m, (Mφ * A * (T / (m : ℝ))
            + ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hcell ω i]
      exact hcellle ω i
    refine hsum.trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
    have : (m : ℝ) * (Mφ * A * (T / (m : ℝ))) = Mφ * A * ((m : ℝ) * (T / (m : ℝ))) := by ring
    rw [this, hTm]
  have hjointg : Measurable (Function.uncurry fun ω s => φ (X s ω) * wgt ω s) :=
    (h.measurable_uncurry_comp hφc.measurable).mul hwm
  have hZmeas : Measurable fun ω : Ω =>
      (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume := by
    refine Measurable.sub ?_ (LevyStochCalc.measurable_setIntegral hjointg _)
    exact Finset.measurable_sum _ fun i _ =>
      (hφc.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m i))).mul
        (LevyStochCalc.measurable_setIntegral_Ioc hwm _ _)
  have hZbd : ∀ ω : Ω,
      |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume|
      ≤ 2 * (Kφ * A * T) := by
    intro ω
    have h1 : |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume|
        ≤ Kφ * A * T := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ i ∈ Finset.range m, |φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume|
          ≤ Kφ * (A * (T / (m : ℝ))) := by
        intro i _
        rw [abs_mul]
        refine mul_le_mul (hφbd _) ?_ (abs_nonneg _) hKφ0
        have := LevyStochCalc.abs_setIntegral_Ioc_le_readable (Measurable.of_uncurry_left hwm) (hA ω)
          (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le
        rwa [LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i] at this
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
      calc (m : ℝ) * (Kφ * (A * (T / (m : ℝ))))
          = Kφ * A * ((m : ℝ) * (T / (m : ℝ))) := by ring
        _ = Kφ * A * T := by rw [hTm]
        _ ≤ Kφ * A * T := le_rfl
    have h2 : |∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| ≤ Kφ * A * T := by
      have := LevyStochCalc.abs_setIntegral_Ioc_le_readable (hgmeas ω) (hgbd ω) hT.le
      simpa using this
    calc |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume|
        ≤ |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume|
          + |∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| :=
          LevyStochCalc.Brownian.Ito.abs_sub_le_abs_add_abs _ _
      _ ≤ 2 * (Kφ * A * T) := by linarith
  have hZint : Integrable (fun ω : Ω =>
      (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume) P := by
    refine (MeasureTheory.integrable_const (2 * (Kφ * A * T))).mono
      hZmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (abs_nonneg _) (hZbd ω))]
    exact hZbd ω
  have hRHS0 : (0 : ℝ) ≤ Mφ * A * T + L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
      + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
    have hT0 : (0 : ℝ) ≤ T := hT.le
    positivity
  refine ⟨hZint, LevyStochCalc.Brownian.Ito.integral_le_of_lintegral_ofReal_le hZint.abs (fun ω => abs_nonneg _)
    hRHS0 ?_⟩
  have hwin : ∀ i : ℕ, ∫⁻ ω, ∫⁻ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
        ENNReal.ofReal ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume ∂P
      ≤ ENNReal.ofReal ((T / (m : ℝ)) * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
    intro i
    have hsym : ∀ (ω : Ω) (s : ℝ), ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖
        = ‖X s ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ := fun ω s => norm_sub_rev _ _
    simp_rw [hsym]
    have := h.lintegral_window_norm_sub_le_readable hC0 hCH hbm hB0 hB
      (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le
    rwa [LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i] at this
  have hmeasCell : ∀ i : ℕ, Measurable fun ω : Ω =>
      ENNReal.ofReal (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
        L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) := by
    intro i
    refine ENNReal.measurable_ofReal.comp (LevyStochCalc.measurable_setIntegral ?_ _)
    exact measurable_const.mul
      ((((h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m i)).comp measurable_fst).sub h.measurable_uncurry).norm)
  have hYle : ∫⁻ ω, ∑ i ∈ Finset.range m, ENNReal.ofReal
        (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) ∂P
      ≤ ENNReal.ofReal (L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
        + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
    calc ∫⁻ ω, ∑ i ∈ Finset.range m, ENNReal.ofReal
            (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
            L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) ∂P
        = ∑ i ∈ Finset.range m, ∫⁻ ω, ENNReal.ofReal
            (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) ∂P :=
        MeasureTheory.lintegral_finsetSum _ fun i _ => hmeasCell i
    _ = ∑ i ∈ Finset.range m, ENNReal.ofReal (L * A)
          * ∫⁻ ω, ∫⁻ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              ENNReal.ofReal ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume ∂P := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (L * A) ≠ ⊤)]
        refine lintegral_congr fun ω => ?_
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hcellL ω i)
          (Filter.Eventually.of_forall fun s => by positivity),
          ← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (L * A) ≠ ⊤)]
        refine lintegral_congr fun s => ?_
        rw [← ENNReal.ofReal_mul hLA0]
    _ ≤ ∑ i ∈ Finset.range m, ENNReal.ofReal (L * A)
          * ENNReal.ofReal ((T / (m : ℝ)) * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) :=
        Finset.sum_le_sum fun i _ => by gcongr; exact hwin i
    _ = ENNReal.ofReal (L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
        have hwnn : (0 : ℝ) ≤ (T / (m : ℝ)) * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))) := by positivity
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← ENNReal.ofReal_mul hLA0]
        rw [show ((m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m : ℝ)) from
          (ENNReal.ofReal_natCast m).symm, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
        congr 1
        field_simp
  have hMAT0 : (0 : ℝ) ≤ Mφ * A * T := by positivity
  have hLAT0 : (0 : ℝ) ≤ L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
      + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
    have hT0 : (0 : ℝ) ≤ T := hT.le
    positivity
  calc ∫⁻ ω, ENNReal.ofReal
        |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| ∂P
      ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (Mφ * A * T) ∂P
        + ∫⁻ ω, ∑ i ∈ Finset.range m, ENNReal.ofReal
            (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) ∂P := by
        rw [← MeasureTheory.lintegral_add_left measurable_const]
        refine lintegral_mono fun ω => ?_
        refine (ENNReal.ofReal_le_ofReal (hZ ω)).trans ?_
        rw [ENNReal.ofReal_add hMAT0 (Finset.sum_nonneg fun i _ =>
          MeasureTheory.integral_nonneg fun s => by positivity)]
        gcongr
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact MeasureTheory.integral_nonneg fun s => by positivity
    _ ≤ ENNReal.ofReal (Mφ * A * T)
        + ENNReal.ofReal (L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
        rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
        exact add_le_add le_rfl hYle
    _ = ENNReal.ofReal (Mφ * A * T + L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := (ENNReal.ofReal_add hMAT0 hLAT0).symm
