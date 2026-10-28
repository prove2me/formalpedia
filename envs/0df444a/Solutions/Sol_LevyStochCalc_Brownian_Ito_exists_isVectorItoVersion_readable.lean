-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:33:29.940248+00:00
-- url     : https://prove2.me/submissions/fcd953e2-b94d-4f23-9b6b-776451caac17

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoVersionExists
import Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_continuousAdapted_modification_readable
import Theorems.Thm_LevyStochCalc_abs_setIntegral_Icc_sub_le_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
/-- The integral of a bounded measurable function over `[0, t]` is continuous in `t`. -/
theorem LevyStochCalc.continuous_setIntegral_Icc {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s, |f s| ≤ B) :
    Continuous fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by
  have hlip : LipschitzWith (Real.toNNReal B)
      fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by
    refine LipschitzWith.of_dist_le_mul fun t t' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal B hB0]
    exact abs_setIntegral_Icc_sub_le_readable hf hB0 hB t' t
  exact hlip.continuous
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoVersionExists.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section Exists
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
  (hHp : ∀ p k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H p k))
  (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)
include hC0 hCH in
/-- **A continuous adapted version of a vector Itô process exists** when the filtration is
constant before time `0` and contains the measurable null sets. -/
theorem solution
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable[ℱ 0] fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (bdrift p))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B) :
    ∃ X : ℝ → Ω → Fin n → ℝ,
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X := by
  classical
  choose Y hYcont hYadapt hYmod using fun (p : Fin n) (k : Fin d) =>
    LevyStochCalc.Brownian.Ito.exists_continuousAdapted_modification_readable (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
      (hHs p k) hC0 (hCH p k) hℱ0 hnull
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  refine ⟨fun t ω p => X₀ ω p + (∫ s in Set.Icc (0 : ℝ) t, bdrift p ω s ∂volume)
      + ∑ k : Fin d, Y p k t ω, ?_, ?_, ?_⟩
  · intro ω
    refine continuous_pi fun p => (continuous_const.add
      (LevyStochCalc.continuous_setIntegral_Icc (Measurable.of_uncurry_left (hbm p)) hB0 (hB p ω))).add ?_
    exact continuous_finsetSum _ fun k _ => hYcont p k ω
  · intro t
    have hcoordm : ∀ p : Fin n, Measurable[ℱ t] fun ω =>
        X₀ ω p + (∫ s in Set.Icc (0 : ℝ) t, bdrift p ω s ∂volume) + ∑ k : Fin d, Y p k t ω := by
      intro p
      refine Measurable.add (Measurable.add (fun A hA => hle0 t _ (hX₀ p hA)) ?_)
        (Finset.measurable_sum _ fun k _ => hYadapt p k t)
      exact (((hbp p).stronglyMeasurable_setIntegral measurableSet_Icc
        Set.Icc_subset_Iic_self volume).mono le_rfl).measurable
    refine Measurable.stronglyMeasurable ?_
    letI : MeasurableSpace Ω := ℱ t
    exact measurable_pi_lambda _ hcoordm
  · intro t ht
    have hall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
        Y p k t ω = LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k t ω :=
      MeasureTheory.ae_all_iff.mpr fun p =>
        MeasureTheory.ae_all_iff.mpr fun k => hYmod p k t ht
    filter_upwards [hall] with ω hω
    funext p
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess, LevyStochCalc.Brownian.Ito.vectorItoMartingale]
    congr 1
    exact Finset.sum_congr rfl fun k _ => hω p k
