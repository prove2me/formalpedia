-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:31:24.212305+00:00
-- url     : https://prove2.me/submissions/8c7f3ad3-daeb-40fb-afb7-bf720a4b0913

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoProcess
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_abs_add_and_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integrable_abs_drift_pow_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_vectorItoMartingale_sub_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_measurable_vectorItoProcess_sub_readable
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
/-- The increment of `t ↦ ∫_{[0,t]} f` across `(a, b]` is the integral over `(a, b]`. -/
theorem LevyStochCalc.setIntegral_Icc_sub_Icc {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in Set.Icc (0 : ℝ) b, f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) a, f s ∂volume
      = ∫ s in Set.Ioc a b, f s ∂volume := by
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a ∪ Set.Ioc a b := by
    rw [Set.Icc_union_Ioc_eq_Icc ha hab]
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  have hint1 : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) a) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  have hint2 : MeasureTheory.IntegrableOn f (Set.Ioc a b) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2,
    add_sub_cancel_left]
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
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Drift
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- The absolute increment of a bounded drift's integral is integrable. -/
theorem LevyStochCalc.Brownian.Ito.integrable_abs_drift
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    MeasureTheory.Integrable
      (fun ω : Ω => |∫ s in Set.Ioc u v, bdrift ω s ∂volume|) P := by
  simpa only [pow_one] using integrable_abs_drift_pow_readable (P := P) bdrift hbm hB0 hB huv 1
/-- The first absolute moment of a bounded drift's increment is at most `B·(v − u)`. -/
theorem LevyStochCalc.Brownian.Ito.integral_abs_drift_le
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (huv : u ≤ v) :
    ∫ ω, |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ∂P ≤ B * (v - u) := by
  calc ∫ ω, |∫ s in Set.Ioc u v, bdrift ω s ∂volume| ∂P
      ≤ ∫ _ω : Ω, B * (v - u) ∂P :=
        MeasureTheory.integral_mono (integrable_abs_drift (P := P) bdrift hbm hB0 hB huv)
          (MeasureTheory.integrable_const _)
          (fun ω => abs_setIntegral_Ioc_le_readable (Measurable.of_uncurry_left hbm) (hB ω) huv)
    _ = B * (v - u) := by simp
end Drift
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section PiNorm
variable {n : ℕ}
/-- The supremum norm on `Fin n → ℝ` is at most the sum of the absolute coordinates. -/
theorem LevyStochCalc.Brownian.Ito.norm_pi_le_sum_abs (x : Fin n → ℝ) : ‖x‖ ≤ ∑ m, |x m| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg (x j))).2 fun m => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ m)
end PiNorm
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
/-- The increment of a coordinate of a vector Itô process is the drift's increment plus the
martingale part's. -/
theorem LevyStochCalc.Brownian.Ito.vectorItoProcess_sub (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (m : Fin n) (ω : Ω) :
    vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m
      = (∫ s in Set.Ioc u v, bdrift m ω s ∂volume)
        + (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) := by
  simp only [vectorItoProcess]
  rw [← setIntegral_Icc_sub_Icc (Measurable.of_uncurry_left (hbm m)) (hB m ω) hu huv]
  ring
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)
section VectorMoments
variable (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
  (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
include hbm hC0 hCH hB0 hB in
/-- **First absolute moment of a coordinate of a vector Itô process's increment.** -/
theorem LevyStochCalc.Brownian.Ito.integral_abs_vectorItoProcess_sub_le (m : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => |vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m|) P
      ∧ ∫ ω, |vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m| ∂P
        ≤ B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u)) := by
  simp_rw [vectorItoProcess_sub W ℱ hcoord H hHm hHp hHs X₀ bdrift hbm hB hu huv.le m]
  obtain ⟨hMint, hMle⟩ :=
    integral_abs_vectorItoMartingale_sub_le_readable W ℱ hcoord H hHm hHp hHs hC0 hCH m hu huv
  exact integrable_abs_add_and_le_readable (measurable_setIntegral_Ioc (hbm m) _ _)
    ((measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v).sub
      (measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u))
    (integrable_abs_drift (P := P) (bdrift m) (hbm m) hB0 (hB m) huv.le) hMint
    (integral_abs_drift_le (P := P) (bdrift m) (hbm m) hB0 (hB m) huv.le) hMle
include hbm hC0 hCH hB0 hB in
/-- **First moment of the norm of a vector Itô process's increment.** -/
theorem solution {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖) P
      ∧ ∫ ω, ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ∂P
        ≤ (n : ℝ) * (B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u))) := by
  have hcm : ∀ m : Fin n,
      Integrable (fun ω => |LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m|) P
        ∧ ∫ ω, |LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
            - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m| ∂P
          ≤ B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u)) := fun m =>
    LevyStochCalc.Brownian.Ito.integral_abs_vectorItoProcess_sub_le W ℱ hcoord H hHm hHp hHs hC0 hCH X₀ bdrift hbm
      hB0 hB m hu huv
  have hdom : Integrable (fun ω => ∑ m : Fin n,
      |LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m|) P :=
    MeasureTheory.integrable_finsetSum _ fun m _ => (hcm m).1
  have hpt : ∀ ω, ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖
      ≤ ∑ m : Fin n, |LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m| := fun ω => by
    simpa using LevyStochCalc.Brownian.Ito.norm_pi_le_sum_abs (LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
      - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω)
  have hmeas : Measurable fun ω => ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
      - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ :=
    (LevyStochCalc.Brownian.Ito.measurable_vectorItoProcess_sub_readable W ℱ hcoord H hHm hHp hHs X₀ bdrift hbm hB hu huv.le).norm
  have hint : Integrable (fun ω => ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
      - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖) P := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω‖ ∂P
      ≤ ∫ ω, ∑ m : Fin n, |LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m| ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = ∑ m : Fin n, ∫ ω, |LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
          - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m| ∂P :=
        MeasureTheory.integral_finsetSum _ fun m _ => (hcm m).1
    _ ≤ ∑ _m : Fin n, (B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u))) :=
        Finset.sum_le_sum fun m _ => (hcm m).2
    _ = (n : ℝ) * (B * (v - u) + (d : ℝ) * (C * Real.sqrt (v - u))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
