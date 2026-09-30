-- Prove2me | solution 1 for MixFlex.Reliable.expectedUtility_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:20:14.294742+00:00
-- url     : https://prove2.me/submissions/e24cb410-7370-4d80-996a-e5a718c9ac87

import Mathlib
import Definitions.Def_MixFlex_Reliable_Model
set_option autoImplicit false
open MeasureTheory MixFlex.Reliable

private theorem int_mono_comp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Ω → ℝ) (hW : Measurable W) (L U : ℝ)
    (hb : ∀ᵐ ω ∂μ, L ≤ W ω ∧ W ω ≤ U) (u : ℝ → ℝ) (hu : Monotone u) :
    Integrable (fun ω => u (W ω)) μ := by
  apply Integrable.of_bound (hu.measurable.comp hW).aestronglyMeasurable (max |u L| |u U|)
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_le]
  dsimp only [Function.comp_apply]
  have hl := hu hω.1
  have hr := hu hω.2
  have h1 := le_max_left |u L| |u U|
  have h2 := le_max_right |u L| |u U|
  have h3 := neg_abs_le (u L)
  have h4 := le_abs_self (u U)
  constructor <;> linarith

private theorem wealth_facts (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (hS : Setting μ X)
    (K : Fin N → ℝ) (hK : ∀ n, 0 ≤ K n) (cF : ℝ) :
    Measurable (wealthSD P X K) ∧ Measurable (wealthSF P X cF (∑ n, K n)) ∧
    (∀ᵐ ω ∂μ, P.w0 - P.c * ∑ n, K n ≤ wealthSD P X K ω ∧
       wealthSD P X K ω ≤ P.w0 + P.p * ∑ n, K n - P.c * ∑ n, K n) ∧
    (∀ᵐ ω ∂μ, P.w0 - cF * ∑ n, K n ≤ wealthSF P X cF (∑ n, K n) ω ∧
       wealthSF P X cF (∑ n, K n) ω ≤ P.w0 + P.p * ∑ n, K n - cF * ∑ n, K n) := by
  have hm (n : Fin N) : Measurable (fun ω => X ω n) := (measurable_pi_apply n).comp hS.meas
  have hx : ∀ᵐ ω ∂μ, ∀ n, 0 ≤ X ω n := ae_all_iff.mpr hS.demand_nonneg
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold wealthSD
    fun_prop
  · unfold wealthSF
    fun_prop
  · filter_upwards [hx] with ω hω
    have hlo : 0 ≤ ∑ n, min (X ω n) (K n) :=
      Finset.sum_nonneg fun n _ => le_min (hω n) (hK n)
    have hhi : (∑ n, min (X ω n) (K n)) ≤ ∑ n, K n :=
      Finset.sum_le_sum fun n _ => min_le_right _ _
    dsimp [wealthSD]
    have h1 := mul_nonneg hP.p_pos.le hlo
    have h2 := mul_le_mul_of_nonneg_left hhi hP.p_pos.le
    constructor <;> linarith
  · filter_upwards [hx] with ω hω
    have hlo : 0 ≤ min (∑ n, X ω n) (∑ n, K n) :=
      le_min (Finset.sum_nonneg fun n _ => hω n) (Finset.sum_nonneg fun n _ => hK n)
    have hhi := min_le_right (∑ n, X ω n) (∑ n, K n)
    dsimp [wealthSF]
    have h1 := mul_nonneg hP.p_pos.le hlo
    have h2 := mul_le_mul_of_nonneg_left hhi hP.p_pos.le
    constructor <;> linarith

private theorem wealth_comparison (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    (X : Ω → Fin N → ℝ) (K : Fin N → ℝ) (hK : ∀ n, 0 ≤ K n) (cF : ℝ)
    (hcF : cF ≤ P.c) (ω : Ω) : wealthSD P X K ω ≤ wealthSF P X cF (∑ n, K n) ω := by
  have hm : (∑ n, min (X ω n) (K n)) ≤ min (∑ n, X ω n) (∑ n, K n) :=
    le_min (Finset.sum_le_sum fun n _ => min_le_left _ _)
      (Finset.sum_le_sum fun n _ => min_le_right _ _)
  have hp := mul_le_mul_of_nonneg_left hm hP.p_pos.le
  have hks : 0 ≤ ∑ n, K n := Finset.sum_nonneg fun n _ => hK n
  have hc := mul_le_mul_of_nonneg_right hcF hks
  dsimp [wealthSD, wealthSF]
  linarith

private theorem utility_le (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (hS : Setting μ X)
    (u : ℝ → ℝ) (hu : Monotone u) (K : Fin N → ℝ) (hK : ∀ n, 0 ≤ K n)
    (cF : ℝ) (hcF : cF ≤ P.c) :
    expectedUtility μ u (wealthSD P X K) ≤ expectedUtility μ u (wealthSF P X cF (∑ n, K n)) := by
  letI := hS.prob
  obtain ⟨hm1, hm2, hb1, hb2⟩ := wealth_facts P hP μ X hS K hK cF
  exact integral_mono (int_mono_comp μ _ hm1 _ _ hb1 u hu)
    (int_mono_comp μ _ hm2 _ _ hb2 u hu)
    (fun ω => hu (wealth_comparison P hP X K hK cF hcF ω))

theorem solution (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (hS : Setting μ X)
    (u : ℝ → ℝ) (hu : Monotone u) (K : Fin N → ℝ) (hK : ∀ n, 0 ≤ K n) :
    expectedUtility μ u (wealthSD P X K) ≤
      expectedUtility μ u (wealthSF P X P.c (∑ n, K n)) :=
  utility_le P hP μ X hS u hu K hK P.c le_rfl
