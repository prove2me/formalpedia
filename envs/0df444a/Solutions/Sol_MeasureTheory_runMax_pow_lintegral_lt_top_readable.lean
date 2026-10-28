-- Prove2me | solution 1 for MeasureTheory.runMax_pow_lintegral_lt_top_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:20.932975+00:00
-- url     : https://prove2.me/submissions/ba4e9ce9-4856-42eb-b0ef-446bfbec7f3b

import Definitions.Def_KLSModular_MathFin_Foundations_DoobLpMaximalInequality
import Theorems.Thm_MeasureTheory_holder_step_truncated_readable

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal
open MeasureTheory
variable {Ω : Type*}
private lemma MeasureTheory.runMax_nonneg {f : ℕ → Ω → ℝ} (hnonneg : ∀ n ω, 0 ≤ f n ω) (n : ℕ) (ω : Ω) :
    0 ≤ MeasureTheory.runMax f n ω :=
  le_trans (hnonneg 0 ω)
    (Finset.le_sup' (f := fun k ↦ f k ω) (Finset.mem_range.mpr (Nat.succ_pos n)))
variable [m0 : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
private lemma MeasureTheory.runMax_measurable {f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ m0}
    (hsub : Submartingale f 𝒢 μ) (n : ℕ) :
    Measurable (MeasureTheory.runMax f n) := by
  unfold MeasureTheory.runMax
  exact Finset.measurable_range_sup''
    (fun k _ ↦ ((hsub.stronglyMeasurable k).mono (𝒢.le k)).measurable)
/-- Auxiliary finiteness lemma: if `∫⁻ (f n)^p ∂μ < ∞` for a non-negative submartingale
`f`, then `∫⁻ (max_{k ≤ n} f_k)^p ∂μ < ∞` as well. Derived from the truncated Hölder
bound by taking the monotone supremum over the truncation level. -/
 lemma solution
    [MeasureTheory.IsFiniteMeasure μ] {𝒢 : MeasureTheory.Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : MeasureTheory.Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω) (hp : 1 < p) (n : ℕ)
    (hB_lt_top : ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ < ⊤) :
    ∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ < ⊤ := by
  set A : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ with hA_def
  set B : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ
  set C : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1)) with hC_def
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  have hp_inv_pos : 0 < 1 / p := by positivity
  have hpm1_p_pos : 0 < (p - 1) / p := div_pos hpm1_pos hp_pos
  have hp_ne_zero : p ≠ 0 := hp_pos.ne'
  have h_sum_inv : (1 : ℝ) / p + (p - 1) / p = 1 := by
    rw [← add_div, show (1 : ℝ) + (p - 1) = p by ring, div_self hp_ne_zero]
  have h_prod_p : (1 : ℝ) / p * p = 1 := by field_simp
  have hC_lt_top : C < ⊤ := by
    rw [hC_def]
    exact ENNReal.ofReal_lt_top
  have hRHS_lt_top : C * B ^ (1 / p) < ⊤ :=
    ENNReal.mul_lt_top hC_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hp_inv_pos.le hB_lt_top.ne)
  have hRHS_p_lt_top : (C * B ^ (1 / p)) ^ p < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg hp_pos.le hRHS_lt_top.ne
  -- For each K > 0: ∫ (min M* K)^p ≤ (C · B^{1/p})^p, finite and independent of K.
  have h_AK_bounded : ∀ (K : ℝ), 0 < K →
      (∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) ∂μ)
        ≤ (C * B ^ (1 / p)) ^ p := by
    intro K hK
    have hAK_bound := MeasureTheory.holder_step_truncated_readable hsub hnonneg hp n K hK
    set A_K : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) ∂μ
        with hAK_def
    have hA_K_lt_top : A_K < ⊤ := by
      rw [hAK_def]
      calc ∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) ∂μ
          ≤ ∫⁻ _ : Ω, ENNReal.ofReal (K ^ p) ∂μ :=
            MeasureTheory.lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal
              (Real.rpow_le_rpow (le_min (MeasureTheory.runMax_nonneg hnonneg n ω) hK.le)
                (min_le_right _ _) hp_pos.le)
        _ = ENNReal.ofReal (K ^ p) * μ Set.univ := MeasureTheory.lintegral_const _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (MeasureTheory.measure_lt_top μ Set.univ)
    have h_inv_bound : A_K ^ (1 / p) ≤ C * B ^ (1 / p) := by
      by_cases hA_K_zero : A_K = 0
      · rw [hA_K_zero, ENNReal.zero_rpow_of_pos hp_inv_pos]
        exact bot_le
      have hAKpm1_ne_zero : A_K ^ ((p - 1) / p) ≠ 0 :=
        fun h ↦ hA_K_zero (ENNReal.rpow_eq_zero_iff_of_pos hpm1_p_pos |>.mp h)
      have hAKpm1_ne_top : A_K ^ ((p - 1) / p) ≠ ⊤ := fun h ↦
        hA_K_lt_top.ne ((ENNReal.rpow_eq_top_iff_of_pos hpm1_p_pos).mp h)
      have h_split : A_K ^ (1 / p) = A_K / A_K ^ ((p - 1) / p) := by
        rw [eq_div_iff hAKpm1_ne_zero hAKpm1_ne_top, mul_comm,
            ← ENNReal.rpow_add_of_nonneg (1/p) ((p-1)/p) hp_inv_pos.le hpm1_p_pos.le,
            h_sum_inv, ENNReal.rpow_one]
      rw [h_split, ENNReal.div_le_iff hAKpm1_ne_zero hAKpm1_ne_top]
      exact hAK_bound
    calc A_K = A_K ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
      _ = (A_K ^ (1 / p)) ^ p := by rw [← ENNReal.rpow_mul, h_prod_p]
      _ ≤ (C * B ^ (1 / p)) ^ p := ENNReal.rpow_le_rpow h_inv_bound hp_pos.le
  -- A = ⨆_K A_K (monotone convergence; min(M*, K+1) ↑ M* as K → ∞).
  have h_iSup : (⨆ K : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) ((K : ℝ) + 1)) ^ p) ∂μ) = A := by
    rw [hA_def, ← MeasureTheory.lintegral_iSup]
    · refine MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall fun ω ↦ le_antisymm ?_ ?_)
      · refine iSup_le fun K ↦ ENNReal.ofReal_le_ofReal ?_
        exact Real.rpow_le_rpow (le_min (MeasureTheory.runMax_nonneg hnonneg n ω) (by positivity))
          (min_le_left _ _) hp_pos.le
      · obtain ⟨K₀, hK₀⟩ := exists_nat_gt (MeasureTheory.runMax f n ω)
        refine le_iSup_of_le K₀ (ENNReal.ofReal_le_ofReal ?_)
        refine Real.rpow_le_rpow (MeasureTheory.runMax_nonneg hnonneg n ω) ?_ hp_pos.le
        exact le_min le_rfl (by linarith)
    · intro K
      exact (((MeasureTheory.runMax_measurable hsub n).min measurable_const).pow_const p).ennreal_ofReal
    · intro a b hab ω
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
        (le_min (MeasureTheory.runMax_nonneg hnonneg n ω) (by positivity)) ?_ hp_pos.le)
      refine min_le_min le_rfl ?_
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
  -- A ≤ (C · B^{1/p})^p < ⊤.
  have h_A_le : A ≤ (C * B ^ (1 / p)) ^ p :=
    h_iSup ▸ iSup_le fun K ↦ h_AK_bounded ((K : ℝ) + 1) (by positivity)
  exact lt_of_le_of_lt h_A_le hRHS_p_lt_top
