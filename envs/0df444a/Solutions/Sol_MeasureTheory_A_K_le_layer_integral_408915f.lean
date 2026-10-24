-- Prove2me | solution 1 for MeasureTheory.A_K_le_layer_integral_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:48:19.164922+00:00
-- url     : https://prove2.me/submissions/4424432b-ab6a-44bc-9db6-5b29823a13ca

import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Martingale.OptionalStopping

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
namespace MeasureTheory
end MeasureTheory
open MeasureTheory in
/-- Truncated layer-cake bound: for `Z_K = min (runMax f n) K`,
       `∫⁻ Z_K^p ≤ ofReal(p) * ∫⁻ t in Ioc 0 K, ofReal(t^(p-2)) * ofReal(∫_{fstar ≥ t} f_n)`. -/
 lemma solution
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    ∫⁻ ω, ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ p) ∂μ
      ≤ ENNReal.ofReal p *
          ∫⁻ t in Set.Ioc (0:ℝ) K,
            ENNReal.ofReal (t ^ (p - 2)) *
              ENNReal.ofReal (∫ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, f n ω ∂μ) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  -- Apply layer cake to Z_K = min (runMax f n) K.
  have hZK_nn : ∀ ω, 0 ≤ min (MeasureTheory.runMax f n ω) K :=
    fun ω ↦ le_min (runMax_nonneg hnonneg n ω) hK.le
  have hZK_meas : Measurable (fun ω ↦ min (MeasureTheory.runMax f n ω) K) :=
    (runMax_measurable hsub n).min measurable_const
  have h_layer :=
    MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul μ
      (ae_of_all _ hZK_nn) hZK_meas.aemeasurable hp_pos
  rw [h_layer]
  -- The integrand `μ{Z_K ≥ t} * ofReal(t^(p-1))` equals
  -- `μ{runMax ≥ t} * ofReal(t^(p-1))` for t ∈ Ioc 0 K and 0 for t > K.
  have h_ZK_set : ∀ t > (0:ℝ),
      μ {ω | t ≤ min (MeasureTheory.runMax f n ω) K} =
        if t ≤ K then μ {ω | t ≤ MeasureTheory.runMax f n ω} else 0 := by
    intro t ht
    by_cases hle : t ≤ K
    · simp only [hle, if_true]
      congr 1
      ext ω
      simp [hle]
    · simp only [hle, if_false]
      rw [show {ω | t ≤ min (MeasureTheory.runMax f n ω) K} = ∅ by
        ext ω
        simp [hle]]
      simp
  -- Restrict the outer integral to Ioc 0 K.
  have h_split : ∫⁻ t in Set.Ioi (0:ℝ), μ {ω | t ≤ min (MeasureTheory.runMax f n ω) K} *
                  ENNReal.ofReal (t ^ (p - 1))
              = ∫⁻ t in Set.Ioc (0:ℝ) K, μ {ω | t ≤ MeasureTheory.runMax f n ω} *
                  ENNReal.ofReal (t ^ (p - 1)) := by
    have hIoiSplit : Set.Ioi (0:ℝ) = Set.Ioc 0 K ∪ Set.Ioi K := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h
        by_cases hle : t ≤ K
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr (not_le.mp hle)
      · rintro (⟨h1, _⟩ | h)
        · exact h1
        · exact lt_trans hK h
    rw [hIoiSplit, lintegral_union measurableSet_Ioi
        (by rw [Set.disjoint_iff]
            intro t ⟨h1, h2⟩
            simp only [Set.mem_Ioc, Set.mem_Ioi] at h1 h2
            linarith [h2, h1.2])]
    have h_zero_right : ∫⁻ t in Set.Ioi K, μ {ω | t ≤ min (MeasureTheory.runMax f n ω) K} *
                          ENNReal.ofReal (t ^ (p - 1)) = 0 := by
      apply setLIntegral_eq_zero measurableSet_Ioi
      intro t ht
      have ht_pos : 0 < t := lt_trans hK ht
      have h_eq_zero : μ {ω | t ≤ min (MeasureTheory.runMax f n ω) K} = 0 := by
        rw [h_ZK_set t ht_pos]
        have ht_gt : ¬ t ≤ K := not_le.mpr ht
        simp [ht_gt]
      change μ {ω | t ≤ min (MeasureTheory.runMax f n ω) K} * _ = 0
      rw [h_eq_zero, zero_mul]
    have h_left : ∫⁻ t in Set.Ioc (0:ℝ) K, μ {ω | t ≤ min (MeasureTheory.runMax f n ω) K} *
                    ENNReal.ofReal (t ^ (p - 1))
                = ∫⁻ t in Set.Ioc (0:ℝ) K, μ {ω | t ≤ MeasureTheory.runMax f n ω} *
                    ENNReal.ofReal (t ^ (p - 1)) := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change μ {ω | t ≤ min (MeasureTheory.runMax f n ω) K} * _ =
            μ {ω | t ≤ MeasureTheory.runMax f n ω} * _
      rw [h_ZK_set t ht.1, if_pos ht.2]
    rw [h_left, h_zero_right, add_zero]
  rw [h_split]
  -- Now apply layer_integrand_bound pointwise.
  apply mul_le_mul_right _ (ENNReal.ofReal p)
  apply setLIntegral_mono_ae'
  · exact measurableSet_Ioc
  refine Filter.Eventually.of_forall (fun t ht ↦ ?_)
  exact layer_integrand_bound hsub hnonneg n ht.1
