-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_pow_four_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:18.454791+00:00
-- url     : https://prove2.me/submissions/954c77ff-e602-4099-aab6-48a8193087c1

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentIncrements
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFourthMomentLintegral

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentIncrements.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Increments
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
/-- A Brownian increment has moments of every order. -/
theorem LevyStochCalc.Brownian.Ito.memLp_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => W.W b ω - W.W a ω) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (μ := P)
    (f := fun ω => W.W b ω - W.W a ω) (p := p)
    (by fun_prop) hmeas.aemeasurable).1
  rw [W.increment_gaussian ha hab] at h
  exact h (memLp_id_gaussianReal' p hp)
/-- A bounded random variable times a Brownian increment has moments of every order. -/
theorem LevyStochCalc.Brownian.Ito.memLp_mul_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤)
    {Y : Ω → ℝ} (hYm : Measurable Y) {C : ℝ} (hC : ∀ ω, |Y ω| ≤ C) :
    MemLp (fun ω => Y ω * (W.W b ω - W.W a ω)) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  refine MemLp.mono ((memLp_increment W ha hab p hp).const_mul C)
    (hYm.mul hmeas).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have hC0 : 0 ≤ C := (abs_nonneg (Y ω)).trans (hC ω)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC ω) (abs_nonneg _)
end Increments
section
variable {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
  {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.partialSum_card (ω : Ω) : G.partialSum W G.N ω = simpleIntegral W G T ω := by
  rw [simpleIntegral_eq_sum, partialSum, ← Fin.sum_univ_eq_sum_range
    (fun i => G.term W i ω) G.N]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term, dif_pos i.isLt]
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.memLp_term {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (i : ℕ) : MemLp (G.term W i) p P := by
  by_cases h : i < G.N
  · have hterm : G.term W i = fun ω => G.ξ ⟨i, h⟩ ω
        * (W.W (G.partition (⟨i, h⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨i, h⟩ : Fin G.N).castSucc) ω) := by
      funext ω; rw [term, dif_pos h]
    rw [hterm]
    exact memLp_mul_increment W (G.partition_nonneg _)
      (G.partition_strictMono Fin.castSucc_lt_succ) p hp (G.ξ_measurable _) (hC ⟨i, h⟩)
  · have hterm : G.term W i = fun _ => (0 : ℝ) := by funext ω; rw [term, dif_neg h]
    rw [hterm]; exact memLp_const 0
theorem LevyStochCalc.Brownian.Ito.SimplePredictable.memLp_partialSum {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (k : ℕ) : MemLp (G.partialSum W k) p P :=
  memLp_finsetSum _ fun i _ => G.memLp_term W hC p hp i
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFourthMomentLintegral.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section LintegralForm
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
open LevyStochCalc.Brownian.Ito in
/-- The fourth `lintegral` of an elementary integral as the `ofReal` of its fourth moment. -/
theorem solution {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
    {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C) :
    ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      = ENNReal.ofReal (∫ ω, (LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω) ^ 4 ∂P) := by
  have hmem : MemLp (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω) 4 P := by
    have h := G.memLp_partialSum W hC 4 (by simp) G.N
    have hfun : G.partialSum W G.N = fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω := by
      funext ω; exact G.partialSum_card W ω
    rwa [hfun] at h
  have hmem' : MemLp (fun ω => LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω) ((4 : ℕ) : ℝ≥0∞) P := by
    simpa using hmem
  have hint : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω) ^ 4) P := by
    refine (hmem'.integrable_norm_pow (by norm_num)).mono
      ((continuous_pow 4).comp_aestronglyMeasurable hmem.1)
      (Filter.Eventually.of_forall fun ω => by simp)
  have hpt : ∀ ω, (‖LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4
      = ENNReal.ofReal ((LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω) ^ 4) := by
    intro ω
    have h1 : (‖LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal |LevyStochCalc.Brownian.Ito.simpleIntegral W G T ω| := by
      rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
      exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
    rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ simpleIntegral W G T ω ^ 4)]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => by positivity)]
  exact lintegral_congr hpt
