-- Prove2me | solution 1 for MeasureTheory.holder_step_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:50:44.308152+00:00
-- url     : https://prove2.me/submissions/31dc4ef3-3b33-4546-83da-9d7d2282ca2b

import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Martingale.OptionalStopping
import Theorems.Thm_MeasureTheory_fubini_swap_408915f

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
/-- Pointwise (in `t > 0`) integrand bound. -/
private lemma MeasureTheory.layer_integrand_bound
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω) (n : ℕ) {p : ℝ}
    {t : ℝ} (ht : 0 < t) :
    μ {ω | t ≤ MeasureTheory.runMax f n ω} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal (t ^ (p - 2)) *
          ENNReal.ofReal (∫ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, f n ω ∂μ) := by
  have ht_pow_pos : (0 : ℝ) ≤ t ^ (p - 2) := Real.rpow_nonneg ht.le _
  have h_decomp : t ^ (p - 1) = t ^ (p - 2) * t := by
    rw [show (p - 1) = (p - 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
  rw [h_decomp, ENNReal.ofReal_mul ht_pow_pos]
  rw [show μ {ω | t ≤ MeasureTheory.runMax f n ω} * (ENNReal.ofReal (t^(p-2)) * ENNReal.ofReal t)
        = ENNReal.ofReal (t^(p-2)) * (ENNReal.ofReal t * μ {ω | t ≤ MeasureTheory.runMax f n ω})
        by ring]
  gcongr
  -- Apply Doob's weak-type maximal inequality at level `t`.
  have key := MeasureTheory.maximal_ineq (μ := μ) (𝒢 := 𝒢)
    (f := f) hsub (fun k ω ↦ hnonneg k ω) (ε := t.toNNReal) n
  rw [show ({ω | t ≤ MeasureTheory.runMax f n ω}) = ({ω | (↑t.toNNReal : ℝ) ≤ MeasureTheory.runMax f n ω}) by
    rw [Real.coe_toNNReal _ ht.le]]
  exact key
/-- Combining steps: A ≤ ofReal p · ∫⁻ t in Ioi 0, ofReal(t^(p-2)) · ofReal(∫_{fstar ≥ t} f_n). -/
private lemma MeasureTheory.A_le_layer_integral
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ
      ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioi (0:ℝ),
            ENNReal.ofReal (t ^ (p - 2)) *
              ENNReal.ofReal (∫ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, f n ω ∂μ) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul μ
        (ae_of_all _ (runMax_nonneg hnonneg n))
        (runMax_measurable hsub n).aemeasurable hp_pos]
  apply mul_le_mul_right _ (ENNReal.ofReal p)
  apply MeasureTheory.setLIntegral_mono_ae'
  · exact measurableSet_Ioi
  refine Filter.Eventually.of_forall (fun t ht ↦ ?_)
  exact layer_integrand_bound hsub hnonneg n ht
/-- Stage 2a: apply Hölder to the post-Fubini integral.

    For non-negative f, g and Hölder conjugates p, q (so 1/p + 1/q = 1):
       `∫⁻ ω, ofReal(f_n) ⋅ ofReal(fstar^(p-1)) ≤ (∫⁻ f_n^p)^(1/p) ⋅ (∫⁻ fstar^p)^(1/q)`.
    Wraps `ENNReal.lintegral_mul_le_Lp_mul_Lq` plus the rpow algebra
    `(x^(p-1))^q = x^p` (using `(p-1)*q = p`). -/
private lemma MeasureTheory.holder_apply
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (f n ω) *
            ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1)) ∂μ)
      ≤ (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ) ^ ((p - 1) / p) := by
  set q := p / (p - 1) with hq_def
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  have hq_pos : 0 < q := by
    simp only [hq_def]
    positivity
  have hpm1_q_eq_p : (p - 1) * q = p := by
    simp only [hq_def]
    field_simp
  have hf_meas : AEMeasurable (fun ω ↦ ENNReal.ofReal (f n ω)) μ :=
    (ENNReal.measurable_ofReal.comp
      (((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl)).aemeasurable
  have hg_meas : AEMeasurable
      (fun ω ↦ ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1))) μ :=
    (ENNReal.measurable_ofReal.comp
      ((runMax_measurable hsub n).pow_const (p - 1))).aemeasurable
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf_meas hg_meas
  -- Rewrite (ofReal f_n)^p = ofReal(f_n^p) using nonneg.
  have h_f_pow : ∀ ω, (ENNReal.ofReal (f n ω)) ^ p = ENNReal.ofReal ((f n ω) ^ p) :=
    fun ω ↦ ENNReal.ofReal_rpow_of_nonneg (hnonneg n ω) hp_pos.le
  -- Rewrite (ofReal fstar^(p-1))^q = ofReal(fstar^p) using (p-1)*q = p.
  have h_g_pow : ∀ ω,
      (ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1))) ^ q
        = ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg
          (Real.rpow_nonneg (runMax_nonneg hnonneg n ω) _) hq_pos.le,
        ← Real.rpow_mul (runMax_nonneg hnonneg n ω) (p - 1) q, hpm1_q_eq_p]
  simp_rw [h_f_pow, h_g_pow] at key
  -- The goal has 1/p and (p-1)/p; key has 1/q (= q⁻¹). Rewrite 1/q = (p-1)/p.
  have h_one_div_q : (1 / q : ℝ) = (p - 1) / p := by
    simp only [hq_def, one_div, inv_div]
  rw [h_one_div_q] at key
  exact key
namespace MeasureTheory
end MeasureTheory
open MeasureTheory in
/-- Stage 2 (Hölder + algebra): combining Fubini's output with Hölder
    yields the master bound on `∫⁻ fstar^p`. -/
 lemma solution
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ)
      ≤ ENNReal.ofReal (p / (p - 1)) *
          (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ) ^ (1 / p) *
          (∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ) ^ ((p - 1) / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hpm1_pos : 0 < p - 1 := by linarith
  have hpm1_inv_pos : 0 < 1 / (p - 1) := by positivity
  -- Step 1: bound A := ∫⁻ fstar^p via A_le_layer_integral.
  have hA := A_le_layer_integral hsub hnonneg hp n
  -- Step 2: rewrite the inner Bochner setIntegral as a setLIntegral.
  have h_inner_rewrite : ∀ t,
      ENNReal.ofReal (∫ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, f n ω ∂μ)
        = ∫⁻ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ := fun _ ↦
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hsub.integrable n).restrict
      (ae_of_all _ (hnonneg n))
  simp_rw [h_inner_rewrite] at hA
  -- Step 3: apply Fubini swap.
  rw [MeasureTheory.fubini_swap_408915f hsub hnonneg hp n] at hA
  -- Step 4: factor `ofReal(fstar^(p-1)/(p-1))` as `ofReal(fstar^(p-1)) * ofReal(1/(p-1))`.
  have h_factor : ∀ ω,
      ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1) / (p - 1))
        = ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1)) * ENNReal.ofReal (1 / (p - 1)) := by
    intro ω
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg (runMax_nonneg hnonneg n ω) _),
        show (p - 1)⁻¹ = 1 / (p - 1) by rw [one_div]]
  simp_rw [h_factor] at hA
  -- Step 5: pull constant ofReal(1/(p-1)) outside the inner integral.
  have h_mul_const :
      ∫⁻ ω, ENNReal.ofReal (f n ω) *
        (ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1)) * ENNReal.ofReal (1 / (p - 1))) ∂μ
      = ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1)) ∂μ := by
    rw [← lintegral_const_mul]
    · congr 1
      funext ω
      ring
    · exact ((ENNReal.measurable_ofReal.comp
          (((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl)).mul
        (ENNReal.measurable_ofReal.comp
          ((runMax_measurable hsub n).pow_const (p - 1))))
  rw [h_mul_const] at hA
  -- Step 6: combine ofReal(p) * ofReal(1/(p-1)) = ofReal(p/(p-1)).
  have h_const_combine :
      ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) = ENNReal.ofReal (p / (p - 1)) := by
    rw [← ENNReal.ofReal_mul hp_pos.le]
    congr 1
    field_simp
  rw [show ENNReal.ofReal p * (ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1)) ∂μ)
      = ENNReal.ofReal p * ENNReal.ofReal (1 / (p - 1)) *
        ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1)) ∂μ from by ring,
      h_const_combine] at hA
  -- Step 7: apply holder_apply to bound the post-Fubini integral.
  refine hA.trans ?_
  rw [mul_assoc]
  gcongr
  exact holder_apply hsub hnonneg hp n
