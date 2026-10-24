-- Prove2me | solution 1 for MeasureTheory.holder_step_truncated_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:50:45.77241+00:00
-- url     : https://prove2.me/submissions/eb55caea-feaa-4b09-ad20-8e39a9140a1f

import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Martingale.OptionalStopping
import Theorems.Thm_MeasureTheory_A_K_le_layer_integral_408915f
import Theorems.Thm_MeasureTheory_fubini_swap_truncated_408915f

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal
section
namespace MeasureTheory
end MeasureTheory
open MeasureTheory
variable {Ω : Type*}
private lemma MeasureTheory.runMax_nonneg {f : ℕ → Ω → ℝ} (hnonneg : ∀ n ω, 0 ≤ f n ω) (n : ℕ) (ω : Ω) :
    0 ≤ MeasureTheory.runMax f n ω :=
  le_trans (hnonneg 0 ω)
    (Finset.le_sup' (f := fun k ↦ f k ω) (Finset.mem_range.mpr (Nat.succ_pos n)))
variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}
private lemma MeasureTheory.runMax_measurable {f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ m0}
    (hsub : Submartingale f 𝒢 μ) (n : ℕ) :
    Measurable (MeasureTheory.runMax f n) := by
  unfold MeasureTheory.runMax
  exact Finset.measurable_range_sup''
    (fun k _ ↦ ((hsub.stronglyMeasurable k).mono (𝒢.le k)).measurable)
namespace MeasureTheory
end MeasureTheory
open MeasureTheory in
/-- Truncated holder_step: master bound for `A_K = ∫⁻ (min fstar K)^p`. -/
 lemma solution
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    (∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) ∂μ)
      ≤ ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) ∂μ) ^ ((p - 1) / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  -- Step 1: bound A_K via A_K_le_layer_integral.
  have hA := MeasureTheory.A_K_le_layer_integral_408915f hsub hnonneg hp n K hK
  -- Step 2: rewrite the inner Bochner integral as a setLIntegral of ofReal.
  have h_inner_rewrite : ∀ t,
      ENNReal.ofReal (∫ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, f n ω ∂μ)
        = ∫⁻ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ := fun _ ↦
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsub.integrable n).restrict
      (ae_of_all _ (hnonneg n))
  simp_rw [h_inner_rewrite] at hA
  -- Step 3: apply truncated Fubini swap.
  rw [MeasureTheory.fubini_swap_truncated_408915f hsub hnonneg hp n K hK] at hA
  -- Step 4: factor `ofReal((Z_K)^(p-1)/(p-1))` into `ofReal((Z_K)^(p-1)) * ofReal(1/(p-1))`.
  have h_factor : ∀ ω,
      ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1) / (p - 1))
        = ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1)) *
            ENNReal.ofReal (1 / (p - 1)) := by
    intro ω
    have hZK_nn : 0 ≤ min (MeasureTheory.runMax f n ω) K := le_min (runMax_nonneg hnonneg n ω) hK.le
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg hZK_nn _),
        show (p - 1)⁻¹ = 1 / (p - 1) by rw [one_div]]
  simp_rw [h_factor] at hA
  -- Step 5: pull constant ofReal(1/(p-1)) outside.
  have hsubM : Measurable (f n) :=
    ((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl
  have hZKmeas : Measurable (fun ω ↦ min (MeasureTheory.runMax f n ω) K) :=
    (runMax_measurable hsub n).min measurable_const
  have h_mul_const :
      ∫⁻ ω, ENNReal.ofReal (f n ω) *
        (ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1)) *
          ENNReal.ofReal (1 / (p - 1))) ∂μ
      = ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1)) ∂μ := by
    rw [← lintegral_const_mul]
    · congr 1
      funext ω
      ring
    · exact ((ENNReal.measurable_ofReal.comp hsubM).mul
        (ENNReal.measurable_ofReal.comp (hZKmeas.pow_const (p - 1))))
  rw [h_mul_const] at hA
  -- Step 6: combine ofReal(p) * ofReal(1/(p-1)) = ofReal(p/(p-1)).
  have h_const_combine :
      ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) = ENNReal.ofReal (p / (p - 1)) := by
    rw [← ENNReal.ofReal_mul hp_pos.le]
    congr 1
    field_simp
  rw [show ENNReal.ofReal p * (ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1)) ∂μ)
      = ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1)) ∂μ from by ring,
      h_const_combine] at hA
  -- Step 7: apply Hölder to bound the inner integral.
  refine hA.trans ?_
  rw [mul_assoc]
  gcongr
  -- Hölder: ∫⁻ ofReal(f n) * ofReal(Z_K^(p-1))
  --   ≤ (∫⁻ ofReal(f n^p))^(1/p) * (∫⁻ ofReal(Z_K^p))^((p-1)/p)
  set q := p / (p - 1) with hq_def
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hq_pos : 0 < q := by
    simp only [hq_def]
    positivity
  have hpm1_q_eq_p : (p - 1) * q = p := by
    simp only [hq_def]
    field_simp
  have hf_meas : AEMeasurable (fun ω ↦ ENNReal.ofReal (f n ω)) μ :=
    (ENNReal.measurable_ofReal.comp hsubM).aemeasurable
  have hg_meas : AEMeasurable
      (fun ω ↦ ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1))) μ :=
    (ENNReal.measurable_ofReal.comp (hZKmeas.pow_const (p - 1))).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf_meas hg_meas
  have h_f_pow : ∀ ω, (ENNReal.ofReal (f n ω)) ^ p = ENNReal.ofReal ((f n ω) ^ p) :=
    fun ω ↦ ENNReal.ofReal_rpow_of_nonneg (hnonneg n ω) hp_pos.le
  have h_g_pow : ∀ ω,
      (ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1))) ^ q
        = ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) := by
    intro ω
    have hZK_nn : 0 ≤ min (MeasureTheory.runMax f n ω) K := le_min (runMax_nonneg hnonneg n ω) hK.le
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hZK_nn _) hq_pos.le,
        ← Real.rpow_mul hZK_nn (p - 1) q, hpm1_q_eq_p]
  simp_rw [h_f_pow, h_g_pow] at key
  have h_one_div_q : (1 / q : ℝ) = (p - 1) / p := by
    simp only [hq_def, one_div, inv_div]
  rw [h_one_div_q] at key
  have hlhs : ∫⁻ a : Ω, ((fun ω ↦ ENNReal.ofReal (f n ω)) *
              fun ω ↦ ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1))) a ∂μ
            = ∫⁻ ω, ENNReal.ofReal (f n ω) *
                    ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1)) ∂μ := by rfl
  rw [hlhs] at key
  exact key
