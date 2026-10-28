-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:35:11.890867+00:00
-- url     : https://prove2.me/submissions/6a7bea91-3f30-4ff8-94f7-b1d2fd6f456b

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLSModular_LevyStochCalc_Ito_ItoFormulaUnboundedClamp
import Definitions.Def_KLSModular_LevyStochCalc_Ito_VectorItoVersionLimit
import Theorems.Thm_LevyStochCalc_Brownian_Ito_clampMesh_mono_window_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_isVectorItoVersion_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_seq_clampMesh_window_lt_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_le_add_inv_mul_sq_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_iSup_sq_norm_clamp_version_sub_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_lintegral_sq_norm_clampProcess_sub_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_of_tendsto_sq_enorm_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_vectorItoProcess_ae_eq_zero_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_version_ae_eq_zero_readable
import Theorems.Thm_LevyStochCalc_Probability_enorm_dyadicRunMax_readable
import Theorems.Thm_LevyStochCalc_Probability_iSup_enorm_eq_iSup_dyadicRunMax_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {M : ℝ → Ω → ℝ} {T : ℝ}
/-- Each sampled running maximum is measurable when the sampled slices are. -/
theorem LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hM : ∀ t : ℝ, Measurable (M t)) (T : ℝ) (n : ℕ) :
    Measurable fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞) := by
  have heq : (fun ω => (‖dyadicRunMax M T n ω‖₊ : ℝ≥0∞))
      = fun ω => ⨆ k : Fin (2 ^ n + 1), (‖M (dyadicTime T n (k : ℕ)) ω‖₊ : ℝ≥0∞) :=
    funext fun ω => enorm_dyadicRunMax_readable M T n ω
  rw [heq]
  exact Measurable.iSup fun k =>
    ENNReal.continuous_coe.measurable.comp (hM (dyadicTime T n (k : ℕ))).nnnorm
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
/-- The integral of a jointly measurable function over a fixed set is measurable in the
parameter. -/
theorem LevyStochCalc.measurable_setIntegral {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (s : Set ℝ) :
    Measurable fun ω => ∫ t in s, f ω t ∂volume :=
  (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict s) hf.stronglyMeasurable).measurable
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorProcess
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
/-- Each entry's Itô integral is measurable for the σ-algebra at its time. -/
theorem LevyStochCalc.Brownian.Ito.stronglyMeasurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    StronglyMeasurable[ℱ t] (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
    (hHs m k) t
/-- Each entry's Itô integral is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    Measurable (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  ((stronglyMeasurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t).mono (ℱ.le t)).measurable
/-- The martingale part of a coordinate is measurable. -/
theorem LevyStochCalc.Brownian.Ito.measurable_vectorItoMartingale (m : Fin n) (t : ℝ) :
    Measurable (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t) :=
  Finset.measurable_sum _ fun k _ => measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t
/-- A vector Itô process is measurable in the sample point at each time. -/
theorem LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess {X₀ : Ω → Fin n → ℝ}
    (hX₀ : ∀ m, Measurable fun ω => X₀ ω m) {bdrift : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) (t : ℝ) :
    Measurable (vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t) := by
  refine measurable_pi_lambda _ fun m => ?_
  exact ((hX₀ m).add (measurable_setIntegral (hbm m) _)).add
    (measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t)
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
end VectorProcess
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
end VectorVersion
end
end

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/ItoFormulaUnboundedClamp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology
universe u
section Clamped
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
theorem LevyStochCalc.Brownian.Ito.measurable_clampDrift {b : Fin n → Ω → ℝ → ℝ}
    (hm : ∀ p, Measurable (Function.uncurry (b p))) (j : ℕ) (p : Fin n) :
    Measurable (Function.uncurry (clampDrift b j p)) :=
  (continuous_clampAt (j : ℝ)).measurable.comp (hm p)
theorem LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampDrift {b : Fin n → Ω → ℝ → ℝ}
    (hp : ∀ p, Probability.ProgressivelyMeasurable ℱ (b p)) (j : ℕ) (p : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (clampDrift b j p) :=
  Probability.ProgressivelyMeasurable.comp_continuous (continuous_clampAt (j : ℝ))
    (clampAt_zero (Nat.cast_nonneg j)) (hp p)
omit [MeasurableSpace Ω] in
theorem LevyStochCalc.Brownian.Ito.abs_clampDrift_le (b : Fin n → Ω → ℝ → ℝ) (j : ℕ) (p : Fin n) (ω : Ω) (s : ℝ) :
    |clampDrift b j p ω s| ≤ (j : ℝ) :=
  abs_clampAt_le (Nat.cast_nonneg j) _
section ClampProcess
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ')
/-- If the integrals of a sequence of nonnegative functions are summable, their sum is finite
almost everywhere. -/
theorem LevyStochCalc.Brownian.Ito.ae_tsum_ne_top_of_lintegral_summable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) : ∀ᵐ a ∂μ, ∑' i : ℕ, g i a ≠ ⊤ := by
  have h1 : ∫⁻ a, ∑' i : ℕ, g i a ∂μ ≠ ⊤ := by
    rw [MeasureTheory.lintegral_tsum fun i => (hg i).aemeasurable]
    exact hsum
  filter_upwards [MeasureTheory.ae_lt_top (Measurable.tsum hg) h1] with a ha
  exact ha.ne
/-- If the integrals of a sequence of nonnegative functions are summable, the functions tend to
zero almost everywhere. -/
theorem LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) :
    ∀ᵐ a ∂μ, Filter.Tendsto (fun i => g i a) Filter.atTop (𝓝 0) := by
  filter_upwards [ae_tsum_ne_top_of_lintegral_summable hg hsum] with a ha
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha
/-- The geometric bound the summability argument uses. -/
theorem LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    ∑' i : ℕ, c * ((2 : ℝ≥0∞)⁻¹) ^ i ≠ ⊤ := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ne_of_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) ?_)
  have hne : (1 : ℝ≥0∞) - 2⁻¹ ≠ 0 := by
    rw [Ne, tsub_eq_zero_iff_le]
    exact not_le.mpr (ENNReal.inv_lt_one.mpr (by norm_num))
  exact lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hne)
end ClampProcess
end Clamped
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/VectorItoVersionLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal Topology
universe u
section Elementary
/-- Powers of `2⁻¹` decrease with the exponent. -/
theorem LevyStochCalc.Brownian.Ito.pow_inv_two_antitone {i j : ℕ} (h : i ≤ j) :
    ((2 : ℝ≥0∞)⁻¹) ^ j ≤ ((2 : ℝ≥0∞)⁻¹) ^ i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have hk : ((2 : ℝ≥0∞)⁻¹) ^ k ≤ (1 : ℝ≥0∞) ^ k :=
    pow_le_pow_left' (ENNReal.inv_lt_one.mpr (by norm_num)).le k
  rw [one_pow] at hk
  calc ((2 : ℝ≥0∞)⁻¹) ^ i * ((2 : ℝ≥0∞)⁻¹) ^ k
      ≤ ((2 : ℝ≥0∞)⁻¹) ^ i * 1 := mul_le_mul' le_rfl hk
    _ = ((2 : ℝ≥0∞)⁻¹) ^ i := mul_one _
/-- A tail of a uniformly convergent family converges uniformly. -/
theorem LevyStochCalc.Brownian.Ito.tendstoUniformlyOn_of_shift {β E : Type*} [UniformSpace E] (A : ℕ → β → E)
    {a : β → E} {s : Set β} (m : ℕ)
    (h : TendstoUniformlyOn (fun N => A (N + m)) a Filter.atTop s) :
    TendstoUniformlyOn A a Filter.atTop s := by
  intro u hu
  rw [← Filter.map_add_atTop_eq_nat m, Filter.eventually_map]
  exact h u hu
/-- Adding a fixed function to a uniformly convergent family preserves uniform convergence. -/
theorem LevyStochCalc.Brownian.Ito.tendstoUniformlyOn_of_sub_const {β E : Type*} [NormedAddCommGroup E] (A : ℕ → β → E)
    (c : β → E) {a : β → E} {s : Set β}
    (h : TendstoUniformlyOn (fun N x => A N x - c x) a Filter.atTop s) :
    TendstoUniformlyOn A (fun x => c x + a x) Filter.atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN x hx
  have heq : c x + a x - A N x = a x - (A N x - c x) := by abel
  rw [dist_eq_norm, heq, ← dist_eq_norm]
  exact hN x hx
end Elementary
section Mesh
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
/-- On a probability space an integral is controlled by `ε` plus a scaled bound on the integral
of the square. -/
theorem LevyStochCalc.Brownian.Ito.lintegral_le_add_inv_mul_of_sq_le (f : Ω → ℝ≥0∞) {ε C : ℝ≥0∞}
    (h0 : ε ≠ 0) (htop : ε ≠ ⊤) (hsq : ∫⁻ ω, f ω ^ 2 ∂P ≤ C) :
    ∫⁻ ω, f ω ∂P ≤ ε + ε⁻¹ * C := by
  calc ∫⁻ ω, f ω ∂P ≤ ∫⁻ ω, (ε + ε⁻¹ * f ω ^ 2) ∂P :=
        MeasureTheory.lintegral_mono fun ω => le_add_inv_mul_sq_readable h0 htop (f ω)
    _ = ε + ε⁻¹ * ∫⁻ ω, f ω ^ 2 ∂P := by
        rw [MeasureTheory.lintegral_add_left measurable_const,
          MeasureTheory.lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr h0),
          MeasureTheory.lintegral_const, measure_univ, mul_one]
    _ ≤ ε + ε⁻¹ * C := by gcongr
end Mesh
section Limit
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
/-- **A continuous adapted version of a vector Itô process exists** when the coefficients have
finite energy on every bounded window, the filtration is constant before time `0` and contains
the measurable null sets. -/
theorem solution
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
    (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (bdrift p))
    (hbq : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X := by
  classical
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  have hX₀' : ∀ p : Fin n, Measurable fun ω => X₀ ω p := fun p => (hX₀ p).mono (ℱ.le 0) le_rfl
  obtain ⟨ms, hmsge, hmslt⟩ := LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_window_lt_readable (P := P) hHm hbm hHs hbq
  have hex : ∀ j : ℕ, ∃ Z : ℝ → Ω → Fin n → ℝ,
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j)
        (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm j p k)
        (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp j p k)
        (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j p k T' hT')
        X₀ (LevyStochCalc.Brownian.Ito.clampDrift bdrift j) Z := fun j =>
    LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_readable W ℱ hcoord (LevyStochCalc.Brownian.Ito.clampCoeff H j)
      (fun p k => LevyStochCalc.Brownian.Ito.measurable_clampCoeff hHm j p k)
      (fun p k => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampCoeff hHp j p k)
      (fun p k T' hT' => LevyStochCalc.Brownian.Ito.energy_clampCoeff_lt_top j p k T' hT')
      (Nat.cast_nonneg j) (LevyStochCalc.Brownian.Ito.abs_clampCoeff_le H j) hℱ0 hnull hX₀ (LevyStochCalc.Brownian.Ito.clampDrift bdrift j)
      (fun p => LevyStochCalc.Brownian.Ito.measurable_clampDrift hbm j p)
      (fun p => LevyStochCalc.Brownian.Ito.progressivelyMeasurable_clampDrift hbp j p)
      (Nat.cast_nonneg j) (LevyStochCalc.Brownian.Ito.abs_clampDrift_le bdrift j)
  choose Xj hXj using hex
  -- the window suprema of consecutive differences, in dyadic form
  obtain ⟨Sraw, hSraw⟩ : ∃ Sraw : ℕ → ℕ → Ω → ℝ≥0∞,
      Sraw = fun (m i : ℕ) (ω : Ω) => ⨆ q : ℕ,
      (‖LevyStochCalc.Probability.dyadicRunMax (fun t ω => ‖Xj (ms (i + 1)) t ω - Xj (ms i) t ω‖)
        ((m : ℝ) + 1) q ω‖₊ : ℝ≥0∞) := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → ℕ → Ω → ℝ≥0∞,
      S = fun (m i : ℕ) (ω : Ω) => if m ≤ i then Sraw m i ω else 0 := ⟨_, rfl⟩
  have hArm : ∀ (i : ℕ) (t : ℝ),
      Measurable fun ω => ‖Xj (ms (i + 1)) t ω - Xj (ms i) t ω‖ :=
    fun i t => (((hXj (ms (i + 1))).measurable t).sub ((hXj (ms i)).measurable t)).norm
  have hSrawm : ∀ m i : ℕ, Measurable (Sraw m i) := by
    intro m i
    simp only [hSraw]
    exact Measurable.iSup fun q => LevyStochCalc.Probability.measurable_enorm_dyadicRunMax (hArm i) ((m : ℝ) + 1) q
  have hSm : ∀ m i : ℕ, Measurable (S m i) := by
    intro m i
    by_cases h : m ≤ i
    · simpa [hSdef, h] using hSrawm m i
    · simp [hSdef, h]
  have hSrawEq : ∀ (m i : ℕ) (ω : Ω), Sraw m i ω
      = ⨆ t : Set.Icc (0 : ℝ) ((m : ℝ) + 1),
        (‖Xj (ms (i + 1)) (t : ℝ) ω - Xj (ms i) (t : ℝ) ω‖₊ : ℝ≥0∞) := by
    intro m i ω
    have hcont : Continuous fun t : ℝ => ‖Xj (ms (i + 1)) t ω - Xj (ms i) t ω‖ :=
      (((hXj (ms (i + 1))).continuous_path ω).sub ((hXj (ms i)).continuous_path ω)).norm
    have hcad : ∀ t : ℝ, Filter.Tendsto
        (fun s => ‖Xj (ms (i + 1)) s ω - Xj (ms i) s ω‖) (nhdsWithin t (Set.Ioi t))
        (nhds ‖Xj (ms (i + 1)) t ω - Xj (ms i) t ω‖) :=
      fun t => (hcont.tendsto t).mono_left nhdsWithin_le_nhds
    simp only [hSraw]
    rw [← LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax_readable
      (M := fun t ω => ‖Xj (ms (i + 1)) t ω - Xj (ms i) t ω‖) (T := (m : ℝ) + 1) (ω := ω)
      (by positivity) hcad]
    exact iSup_congr fun t => by rw [nnnorm_norm]
  -- the geometric decay of the window energies
  have hSsq : ∀ m i : ℕ, m ≤ i →
      ∫⁻ ω, (S m i ω) ^ 2 ∂P ≤ 64 * (n : ℝ≥0∞) ^ 2 * ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
    intro m i hmi
    have hTpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hkey := LevyStochCalc.Brownian.Ito.lintegral_iSup_sq_norm_clamp_version_sub_le_readable W ℱ hcoord (H := H)
      (hm := hHm) (hpg := hHp) hbm (hXj (ms i)) (hXj (ms (i + 1))) hTpos
    have hmr : (m : ℝ) ≤ (i : ℝ) := by exact_mod_cast hmi
    have hmle : ((m : ℝ) + 1) ≤ (i : ℝ) + 1 := by linarith
    have hle1 : LevyStochCalc.Brownian.Ito.clampMesh P H bdrift ((m : ℝ) + 1) (ms i) ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) :=
      le_trans (LevyStochCalc.Brownian.Ito.clampMesh_mono_window_readable P H bdrift hmle (ms i)) (hmslt i).le
    have hmle2 : ((m : ℝ) + 1) ≤ ((i + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    have hle2 : LevyStochCalc.Brownian.Ito.clampMesh P H bdrift ((m : ℝ) + 1) (ms (i + 1))
        ≤ ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
      refine le_trans (LevyStochCalc.Brownian.Ito.clampMesh_mono_window_readable P H bdrift hmle2 (ms (i + 1))) ?_
      exact le_trans (hmslt (i + 1)).le (LevyStochCalc.Brownian.Ito.pow_inv_two_antitone (by omega))
    have hrw : ∀ ω : Ω, S m i ω
        = ⨆ t : Set.Icc (0 : ℝ) ((m : ℝ) + 1),
          (‖Xj (ms (i + 1)) (t : ℝ) ω - Xj (ms i) (t : ℝ) ω‖₊ : ℝ≥0∞) := by
      intro ω
      simp only [hSdef]
      rw [if_pos hmi]
      exact hSrawEq m i ω
    calc ∫⁻ ω, (S m i ω) ^ 2 ∂P
        = ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) ((m : ℝ) + 1),
            (‖Xj (ms (i + 1)) (t : ℝ) ω - Xj (ms i) (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
          exact MeasureTheory.lintegral_congr fun ω => by rw [hrw ω]
      _ ≤ 32 * (n : ℝ≥0∞) ^ 2 * (LevyStochCalc.Brownian.Ito.clampMesh P H bdrift ((m : ℝ) + 1) (ms i)
            + LevyStochCalc.Brownian.Ito.clampMesh P H bdrift ((m : ℝ) + 1) (ms (i + 1))) := hkey
      _ ≤ 32 * (n : ℝ≥0∞) ^ 2 * (((2 : ℝ≥0∞)⁻¹) ^ (2 * i) + ((2 : ℝ≥0∞)⁻¹) ^ (2 * i)) := by
          gcongr
      _ = 64 * (n : ℝ≥0∞) ^ 2 * ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by ring
  have hSint : ∀ m i : ℕ, m ≤ i →
      ∫⁻ ω, S m i ω ∂P ≤ (1 + 64 * (n : ℝ≥0∞) ^ 2) * ((2 : ℝ≥0∞)⁻¹) ^ i := by
    intro m i hmi
    have h2 : ((2 : ℝ≥0∞)⁻¹) ≠ 0 := by simp
    have h2t : ((2 : ℝ≥0∞)⁻¹) ≠ ⊤ := by simp
    have hε0 : ((2 : ℝ≥0∞)⁻¹) ^ i ≠ 0 := pow_ne_zero i h2
    have hεt : ((2 : ℝ≥0∞)⁻¹) ^ i ≠ ⊤ := ENNReal.pow_ne_top h2t
    have hsq : ∫⁻ ω, (S m i ω) ^ 2 ∂P
        ≤ 64 * (n : ℝ≥0∞) ^ 2 * (((2 : ℝ≥0∞)⁻¹) ^ i) ^ 2 := by
      have h := hSsq m i hmi
      rwa [show ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) = (((2 : ℝ≥0∞)⁻¹) ^ i) ^ 2 by
        rw [two_mul, pow_add, sq]] at h
    refine (LevyStochCalc.Brownian.Ito.lintegral_le_add_inv_mul_of_sq_le (S m i) hε0 hεt hsq).trans (le_of_eq ?_)
    have hcancel : (((2 : ℝ≥0∞)⁻¹) ^ i)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ i = 1 :=
      ENNReal.inv_mul_cancel hε0 hεt
    calc ((2 : ℝ≥0∞)⁻¹) ^ i
          + (((2 : ℝ≥0∞)⁻¹) ^ i)⁻¹ * (64 * (n : ℝ≥0∞) ^ 2 * (((2 : ℝ≥0∞)⁻¹) ^ i) ^ 2)
        = ((2 : ℝ≥0∞)⁻¹) ^ i + 64 * (n : ℝ≥0∞) ^ 2
            * ((((2 : ℝ≥0∞)⁻¹) ^ i)⁻¹ * ((2 : ℝ≥0∞)⁻¹) ^ i * ((2 : ℝ≥0∞)⁻¹) ^ i) := by ring
      _ = (1 + 64 * (n : ℝ≥0∞) ^ 2) * ((2 : ℝ≥0∞)⁻¹) ^ i := by rw [hcancel]; ring
  have htsum : ∀ m : ℕ, ∑' i : ℕ, ∫⁻ ω, S m i ω ∂P ≠ ⊤ := by
    intro m
    have hC : (1 + 64 * (n : ℝ≥0∞) ^ 2) ≠ ⊤ := by finiteness
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_)
      (lt_top_iff_ne_top.mpr (LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top _ hC)))
    by_cases hmi : m ≤ i
    · exact hSint m i hmi
    · have hz : ∫⁻ ω, S m i ω ∂P = 0 := by simp [hSdef, hmi]
      rw [hz]
      exact zero_le
  have hae : ∀ᵐ ω ∂P, ∀ m : ℕ, ∑' i : ℕ, S m i ω ≠ ⊤ := by
    rw [MeasureTheory.ae_all_iff]
    intro m
    exact LevyStochCalc.Brownian.Ito.ae_tsum_ne_top_of_lintegral_summable (μ := P) (hSm m) (htsum m)
  -- the almost sure event of uniform convergence
  obtain ⟨G, hGdef⟩ : ∃ G : Set Ω, G = {ω | ∀ m : ℕ, ∑' i : ℕ, S m i ω ≠ ⊤} := ⟨_, rfl⟩
  have hGmeas : MeasurableSet G := by
    have hGeq : G = ⋂ m : ℕ, (fun ω => ∑' i : ℕ, S m i ω) ⁻¹' {(⊤ : ℝ≥0∞)}ᶜ := by
      ext ω
      simp [hGdef]
    rw [hGeq]
    refine MeasurableSet.iInter fun m => ?_
    exact (Measurable.tsum fun i => hSm m i) (measurableSet_singleton _).compl
  have hGnull : P Gᶜ = 0 := by
    have h1 : ∀ᵐ ω ∂P, ω ∈ G := by
      filter_upwards [hae] with ω hω
      rw [hGdef]
      exact hω
    exact MeasureTheory.ae_iff.mp h1
  have hG0 : MeasurableSet[ℱ 0] G := by
    have h := hnull Gᶜ hGmeas.compl hGnull
    simpa using h.compl
  -- uniform convergence of the clamped versions on every bounded window
  have hUnif : ∀ ω : Ω, ω ∈ G → ∀ m : ℕ, ∃ L : ℝ → Fin n → ℝ,
      TendstoUniformlyOn (fun N (t : ℝ) => Xj (ms N) (max t 0) ω) L Filter.atTop
        (Set.Iic ((m : ℝ) + 1)) := by
    intro ω hωG m
    have hω : ∀ m' : ℕ, ∑' i : ℕ, S m' i ω ≠ ⊤ := by rw [hGdef] at hωG; exact hωG
    have hsum0 : Summable fun i : ℕ => (S m i ω).toReal := ENNReal.summable_toReal (hω m)
    have hsum1 : Summable fun i : ℕ => (S m (i + m) ω).toReal :=
      (summable_nat_add_iff m).mpr hsum0
    have hne : ∀ i : ℕ, S m i ω ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top (hω m)
    have hbnd : ∀ (i : ℕ) (x : ℝ), x ∈ Set.Iic ((m : ℝ) + 1) →
        ‖Xj (ms (i + 1 + m)) (max x 0) ω - Xj (ms (i + m)) (max x 0) ω‖
          ≤ (S m (i + m) ω).toReal := by
      intro i x hx
      have hmem : max x 0 ∈ Set.Icc (0 : ℝ) ((m : ℝ) + 1) :=
        ⟨le_max_right x 0, max_le (Set.mem_Iic.mp hx) (by positivity)⟩
      rw [show i + 1 + m = i + m + 1 from by omega]
      have hle : (‖Xj (ms (i + m + 1)) (max x 0) ω
          - Xj (ms (i + m)) (max x 0) ω‖₊ : ℝ≥0∞) ≤ S m (i + m) ω := by
        simp only [hSdef]
        rw [if_pos (Nat.le_add_left m i), hSrawEq]
        exact le_iSup (fun t : Set.Icc (0 : ℝ) ((m : ℝ) + 1) =>
          (‖Xj (ms (i + m + 1)) (t : ℝ) ω - Xj (ms (i + m)) (t : ℝ) ω‖₊ : ℝ≥0∞))
          ⟨max x 0, hmem⟩
      have := ENNReal.toReal_mono (hne (i + m)) hle
      simpa using this
    have hMT := tendstoUniformlyOn_tsum_nat (u := fun i : ℕ => (S m (i + m) ω).toReal) hsum1
      (s := Set.Iic ((m : ℝ) + 1))
      (f := fun (i : ℕ) (x : ℝ) =>
        Xj (ms (i + 1 + m)) (max x 0) ω - Xj (ms (i + m)) (max x 0) ω) hbnd
    have heq : (fun (N : ℕ) (x : ℝ) => ∑ i ∈ Finset.range N,
          (Xj (ms (i + 1 + m)) (max x 0) ω - Xj (ms (i + m)) (max x 0) ω))
        = fun (N : ℕ) (x : ℝ) =>
          Xj (ms (N + m)) (max x 0) ω - Xj (ms (0 + m)) (max x 0) ω := by
      funext N x
      exact Finset.sum_range_sub (fun i => Xj (ms (i + m)) (max x 0) ω) N
    rw [heq] at hMT
    refine ⟨_, LevyStochCalc.Brownian.Ito.tendstoUniformlyOn_of_shift (fun N (t : ℝ) => Xj (ms N) (max t 0) ω) m
      (LevyStochCalc.Brownian.Ito.tendstoUniformlyOn_of_sub_const (fun N (t : ℝ) => Xj (ms (N + m)) (max t 0) ω)
        (fun t : ℝ => Xj (ms (0 + m)) (max t 0) ω) hMT)⟩
  -- the limit process
  obtain ⟨Xlim, hXlim⟩ : ∃ f : ℝ → Ω → Fin n → ℝ, f = fun t ω =>
      if ω ∈ G then Filter.limUnder Filter.atTop (fun N => Xj (ms N) (max t 0) ω)
      else 0 := ⟨_, rfl⟩
  have hPt : ∀ ω : Ω, ω ∈ G → ∀ t : ℝ,
      Filter.Tendsto (fun N => Xj (ms N) (max t 0) ω) Filter.atTop (𝓝 (Xlim t ω)) := by
    intro ω hωG t
    obtain ⟨L, hL⟩ := hUnif ω hωG ⌈t⌉₊
    have hmem : t ∈ Set.Iic ((⌈t⌉₊ : ℝ) + 1) := by
      have := Nat.le_ceil t
      simp only [Set.mem_Iic]
      linarith
    have hLt := hL.tendsto_at hmem
    have hval : Xlim t ω = L t := by
      simp only [hXlim]
      rw [if_pos hωG, hLt.limUnder_eq]
    rw [hval]
    exact hLt
  -- continuity of the limit paths
  have hcont : ∀ ω : Ω, Continuous fun t => Xlim t ω := by
    intro ω
    by_cases hωG : ω ∈ G
    · rw [continuous_iff_continuousAt]
      intro t
      obtain ⟨L, hL⟩ := hUnif ω hωG ⌈|t|⌉₊
      have hEq : Set.EqOn L (fun s => Xlim s ω) (Set.Iic ((⌈|t|⌉₊ : ℝ) + 1)) := by
        intro s hs
        exact tendsto_nhds_unique (hL.tendsto_at hs) (hPt ω hωG s)
      have hL' : TendstoUniformlyOn (fun N (s : ℝ) => Xj (ms N) (max s 0) ω)
          (fun s => Xlim s ω) Filter.atTop (Set.Iic ((⌈|t|⌉₊ : ℝ) + 1)) := hL.congr_right hEq
      have hCon : ContinuousOn (fun s => Xlim s ω) (Set.Iic ((⌈|t|⌉₊ : ℝ) + 1)) := by
        refine hL'.continuousOn (Filter.Eventually.frequently
          (Filter.Eventually.of_forall fun N => ?_))
        have hmax : Continuous fun s : ℝ => max s 0 := continuous_id.max continuous_const
        exact (((hXj (ms N)).continuous_path ω).comp hmax).continuousOn
      refine hCon.continuousAt (Iic_mem_nhds ?_)
      have h1 : |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : t ≤ |t| := le_abs_self t
      linarith
    · have hz : (fun t => Xlim t ω) = fun _ => (0 : Fin n → ℝ) := by
        funext t
        simp only [hXlim]
        exact if_neg hωG
      rw [hz]
      exact continuous_const
  -- adaptedness of the limit
  have hadapt : ∀ t : ℝ, StronglyMeasurable[ℱ t] (Xlim t) := by
    intro t
    have hmaxle : ℱ (max t 0) ≤ ℱ t := by
      rcases le_or_gt 0 t with ht | ht
      · rw [max_eq_left ht]
      · rw [max_eq_right ht.le]
        exact hle0 t
    have hGt : MeasurableSet[ℱ t] G := hle0 t _ hG0
    have hFN : ∀ N : ℕ,
        Measurable[ℱ t] (Set.indicator G fun ω => Xj (ms N) (max t 0) ω) := by
      intro N
      refine Measurable.indicator ?_ hGt
      exact ((hXj (ms N)).adapted (max t 0)).measurable.mono hmaxle le_rfl
    refine Measurable.stronglyMeasurable ?_
    letI : MeasurableSpace Ω := ℱ t
    refine measurable_of_tendsto_metrizable' Filter.atTop hFN ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hωG : ω ∈ G
    · simpa [Set.indicator_of_mem hωG] using hPt ω hωG t
    · simp only [Set.indicator_of_notMem hωG]
      simp only [hXlim]
      rw [if_neg hωG]
      exact tendsto_const_nhds
  refine ⟨Xlim, hcont, hadapt, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht with h0 | htpos
  · -- the initial time
    have hzero : ∀ᵐ ω ∂P, ∀ j : ℕ, Xj j 0 ω = X₀ ω := by
      rw [MeasureTheory.ae_all_iff]
      intro j
      exact LevyStochCalc.Brownian.Ito.version_ae_eq_zero_readable W ℱ hcoord (hXj j)
    have hvip := LevyStochCalc.Brownian.Ito.vectorItoProcess_ae_eq_zero_readable W ℱ hcoord hHm hHp hHs X₀ bdrift
    filter_upwards [hzero, hvip, hae] with ω hz hv hωG
    have hωG' : ω ∈ G := by rw [hGdef]; exact hωG
    have hlim := hPt ω hωG' t
    rw [← h0] at hlim ⊢
    simp only [max_self] at hlim
    have hconst : Filter.Tendsto (fun N => Xj (ms N) (0 : ℝ) ω) Filter.atTop (𝓝 (X₀ ω)) := by
      refine Filter.Tendsto.congr (fun N => (hz (ms N)).symm) tendsto_const_nhds
    rw [tendsto_nhds_unique hlim hconst, hv]
  · -- positive times
    have hN : ∀ i : ℕ, t ≤ ((i + ⌈t⌉₊ : ℕ) : ℝ) + 1 := by
      intro i
      have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
      have h2 : ((⌈t⌉₊ : ℕ) : ℝ) ≤ ((i + ⌈t⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_left ⌈t⌉₊ i
      linarith
    have hbound : ∀ i : ℕ, ∫⁻ ω, (‖Xj (ms (i + ⌈t⌉₊)) t ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          ≤ ((2 : ℝ≥0∞)⁻¹) ^ i := by
      intro i
      refine le_trans (le_of_eq ?_) (le_trans (LevyStochCalc.Brownian.Ito.lintegral_sq_norm_clampProcess_sub_le_readable W ℱ hcoord
        hHm hHp hHs hX₀' hbm hbq (ms (i + ⌈t⌉₊)) htpos (hN i)) ?_)
      · refine MeasureTheory.lintegral_congr_ae ?_
        filter_upwards [(hXj (ms (i + ⌈t⌉₊))).ae_eq t htpos.le] with ω hω
        rw [hω]
      · exact le_trans (hmslt (i + ⌈t⌉₊)).le (LevyStochCalc.Brownian.Ito.pow_inv_two_antitone (by omega))
    have hmeas : ∀ i : ℕ, Measurable fun ω => (‖Xj (ms (i + ⌈t⌉₊)) t ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro i
      have h1 : Measurable fun ω => Xj (ms (i + ⌈t⌉₊)) t ω := (hXj (ms (i + ⌈t⌉₊))).measurable t
      have h2 : Measurable (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t) :=
        LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess W ℱ hcoord H hHm hHp hHs hX₀' hbm t
      exact (((h1.sub h2).nnnorm).coe_nnreal_ennreal).pow_const 2
    have hsum : ∑' i : ℕ, ∫⁻ ω, (‖Xj (ms (i + ⌈t⌉₊)) t ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ := by
      have hgeom := LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (1 : ℝ≥0∞) (by simp)
      refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) ?_)
      refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.mpr hgeom)
      exact tsum_congr fun i => (one_mul _).symm
    filter_upwards [LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable (μ := P) hmeas hsum, hae]
      with ω hω hωG
    have hωG' : ω ∈ G := by rw [hGdef]; exact hωG
    have h1 : Filter.Tendsto (fun i => Xj (ms (i + ⌈t⌉₊)) t ω) Filter.atTop
        (𝓝 (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t ω)) :=
      LevyStochCalc.Brownian.Ito.tendsto_of_tendsto_sq_enorm_readable hω
    have h2 : Filter.Tendsto (fun i => Xj (ms (i + ⌈t⌉₊)) t ω) Filter.atTop (𝓝 (Xlim t ω)) := by
      have h3 := hPt ω hωG' t
      rw [max_eq_left ht] at h3
      exact h3.comp (Filter.tendsto_add_atTop_nat ⌈t⌉₊)
    exact tendsto_nhds_unique h2 h1
