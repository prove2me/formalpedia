-- Prove2me | solution 1 for HlawkaSchatten.tendsto_scalarRatio_one
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T21:02:55.239624+00:00
-- url     : https://prove2.me/submissions/a2eb41b5-3ea8-4ac9-9037-2210788c64d4

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Definitions.Def_HlawkaSchatten_ScalarRatio
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The scalar Bregman--Mazur ratio

This file starts the compact scalar-reduction layer of the Schatten Hlawka
argument.  The raw quotient has a removable singularity at `t = 1`; the
regularized version installs its second-order limiting value.
-/


open Filter Set
open scoped OnePoint Topology

open HlawkaSchatten

/-- Explicit formula (1) from the audited proof source. -/
theorem scalarRatio_eq_explicit {p : ℝ} (hp : p ≠ 0) (t : ℝ) :
    scalarRatio p t =
      (|t| ^ p - p * t + p - 1) /
        (p * (signedPower (p / 2) t - 1) ^ 2) := by
  unfold scalarRatio scalarBregman powerPotential powerGradient scalarMazur
  simp
  field_simp [hp]
  ring

private noncomputable def positiveRatioDenominator (p t : ℝ) : ℝ :=
  p * (t ^ (p / 2) - 1) ^ 2

private noncomputable def positiveRatioDenominatorDeriv (p t : ℝ) : ℝ :=
  p ^ 2 * (t ^ (p / 2) - 1) * t ^ (p / 2 - 1)

private theorem hasDerivAt_positiveRatioDenominator (p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (positiveRatioDenominator p) (positiveRatioDenominatorDeriv p t) t := by
  have hpow : HasDerivAt (fun x : ℝ ↦ x ^ (p / 2))
      ((p / 2) * t ^ (p / 2 - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht)
  unfold positiveRatioDenominator positiveRatioDenominatorDeriv
  convert! ((hpow.sub_const 1).pow 2).const_mul p using 1; (norm_num; ring)

private noncomputable def positiveRatioDenominatorDeriv2 (p t : ℝ) : ℝ :=
  p ^ 2 * ((p / 2) * t ^ (p / 2 - 1) * t ^ (p / 2 - 1) +
    (t ^ (p / 2) - 1) * (p / 2 - 1) * t ^ (p / 2 - 2))

private theorem hasDerivAt_positiveRatioDenominatorDeriv (p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (positiveRatioDenominatorDeriv p)
      (positiveRatioDenominatorDeriv2 p t) t := by
  unfold positiveRatioDenominatorDeriv positiveRatioDenominatorDeriv2
  have h₁ := (Real.hasDerivAt_rpow_const (p := p / 2) (Or.inl ht)).sub_const 1
  have h₂ := Real.hasDerivAt_rpow_const (p := p / 2 - 1) (Or.inl ht)
  have hfun :
      (fun x : ℝ ↦ p ^ 2 * (x ^ (p / 2) - 1) * x ^ (p / 2 - 1)) =
        fun x ↦ p ^ 2 * ((x ^ (p / 2) - 1) * x ^ (p / 2 - 1)) := by
    funext x
    ring
  rw [hfun]
  convert! (h₁.mul h₂).const_mul (p ^ 2) using 1; ring

private noncomputable def positiveRatioNumerator (p t : ℝ) : ℝ :=
  t ^ p - p * t + (p - 1)

private noncomputable def positiveRatioNumeratorDeriv (p t : ℝ) : ℝ :=
  p * t ^ (p - 1) - p

private theorem hasDerivAt_positiveRatioNumerator (p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (positiveRatioNumerator p) (positiveRatioNumeratorDeriv p t) t := by
  have hpow : HasDerivAt (fun x : ℝ ↦ x ^ p) (p * t ^ (p - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht)
  have hlin : HasDerivAt (fun x : ℝ ↦ p * x) p t := by
    simpa using (hasDerivAt_id t).const_mul p
  unfold positiveRatioNumerator positiveRatioNumeratorDeriv
  convert! (hpow.sub hlin).add_const (p - 1) using 1

private noncomputable def positiveRatioNumeratorDeriv2 (p t : ℝ) : ℝ :=
  p * (p - 1) * t ^ (p - 2)

private theorem hasDerivAt_positiveRatioNumeratorDeriv (p : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (positiveRatioNumeratorDeriv p) (positiveRatioNumeratorDeriv2 p t) t := by
  have hpow : HasDerivAt (fun x : ℝ ↦ x ^ (p - 1))
      ((p - 1) * t ^ (p - 2)) t := by
    convert Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl ht) using 1; ring
  unfold positiveRatioNumeratorDeriv positiveRatioNumeratorDeriv2
  convert! hpow.const_mul p |>.sub_const p using 1; ring

private theorem positiveRatioDenominatorDeriv_ne_zero {p t : ℝ}
    (hp : 0 < p) (ht : 0 < t) (ht1 : t ≠ 1) :
    positiveRatioDenominatorDeriv p t ≠ 0 := by
  unfold positiveRatioDenominatorDeriv
  have hpow : t ^ (p / 2) ≠ 1 := by
    intro heq
    have heq' : t ^ (p / 2) = (1 : ℝ) ^ (p / 2) := by simpa using heq
    exact ht1 ((Real.strictMonoOn_rpow_Ici_of_exponent_pos (half_pos hp)).injOn
      (show t ∈ Set.Ici 0 from ht.le) (by simp) heq')
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hp.ne') (sub_ne_zero.mpr hpow))
    (Real.rpow_pos_of_pos ht _).ne'

theorem solution {p : ℝ} (hp : 1 < p) :
    Tendsto (scalarRatio p) (𝓝[≠] 1) (𝓝 (2 * (p - 1) / p ^ 2)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hN2cont : ContinuousAt (positiveRatioNumeratorDeriv2 p) 1 := by
    unfold positiveRatioNumeratorDeriv2
    fun_prop (disch := norm_num)
  have hD2cont : ContinuousAt (positiveRatioDenominatorDeriv2 p) 1 := by
    unfold positiveRatioDenominatorDeriv2
    fun_prop (disch := norm_num)
  have hD2pos : 0 < positiveRatioDenominatorDeriv2 p 1 := by
    unfold positiveRatioDenominatorDeriv2
    norm_num
    positivity
  have hsecond : Tendsto
      (fun t ↦ positiveRatioNumeratorDeriv2 p t / positiveRatioDenominatorDeriv2 p t)
      (𝓝 1) (𝓝 (2 * (p - 1) / p ^ 2)) := by
    have hcont := hN2cont.div hD2cont hD2pos.ne'
    have hval : positiveRatioNumeratorDeriv2 p 1 /
        positiveRatioDenominatorDeriv2 p 1 = 2 * (p - 1) / p ^ 2 := by
      unfold positiveRatioNumeratorDeriv2 positiveRatioDenominatorDeriv2
      norm_num
      field_simp [hp0]
    rw [← hval]
    exact hcont.tendsto
  have hN1zero : Tendsto (positiveRatioNumeratorDeriv p) (𝓝 1) (𝓝 0) := by
    have hcont := (hasDerivAt_positiveRatioNumeratorDeriv p one_ne_zero).continuousAt
    have hval : positiveRatioNumeratorDeriv p 1 = 0 := by
      simp [positiveRatioNumeratorDeriv]
    rw [← hval]
    exact hcont.tendsto
  have hD1zero : Tendsto (positiveRatioDenominatorDeriv p) (𝓝 1) (𝓝 0) := by
    have hcont := (hasDerivAt_positiveRatioDenominatorDeriv p one_ne_zero).continuousAt
    have hval : positiveRatioDenominatorDeriv p 1 = 0 := by
      simp [positiveRatioDenominatorDeriv]
    rw [← hval]
    exact hcont.tendsto
  have hfirst : Tendsto
      (fun t ↦ positiveRatioNumeratorDeriv p t / positiveRatioDenominatorDeriv p t)
      (𝓝[≠] 1) (𝓝 (2 * (p - 1) / p ^ 2)) := by
    apply HasDerivAt.lhopital_zero_nhdsNE
    · exact ((eventually_ne_nhds one_ne_zero).mono fun _ ht ↦
        hasDerivAt_positiveRatioNumeratorDeriv p ht).filter_mono nhdsWithin_le_nhds
    · exact ((eventually_ne_nhds one_ne_zero).mono fun _ ht ↦
        hasDerivAt_positiveRatioDenominatorDeriv p ht).filter_mono nhdsWithin_le_nhds
    · exact (hD2cont.eventually_ne hD2pos.ne').filter_mono nhdsWithin_le_nhds
    · exact tendsto_nhdsWithin_of_tendsto_nhds hN1zero
    · exact tendsto_nhdsWithin_of_tendsto_nhds hD1zero
    · exact tendsto_nhdsWithin_of_tendsto_nhds hsecond
  have hNzero : Tendsto (positiveRatioNumerator p) (𝓝 1) (𝓝 0) := by
    have hcont := (hasDerivAt_positiveRatioNumerator p one_ne_zero).continuousAt
    have hval : positiveRatioNumerator p 1 = 0 := by simp [positiveRatioNumerator]
    rw [← hval]
    exact hcont.tendsto
  have hDzero : Tendsto (positiveRatioDenominator p) (𝓝 1) (𝓝 0) := by
    have hcont := (hasDerivAt_positiveRatioDenominator p one_ne_zero).continuousAt
    have hval : positiveRatioDenominator p 1 = 0 := by simp [positiveRatioDenominator]
    rw [← hval]
    exact hcont.tendsto
  have hraw : Tendsto
      (fun t ↦ positiveRatioNumerator p t / positiveRatioDenominator p t)
      (𝓝[≠] 1) (𝓝 (2 * (p - 1) / p ^ 2)) := by
    apply HasDerivAt.lhopital_zero_nhdsNE
    · exact ((eventually_ne_nhds one_ne_zero).mono fun _ ht ↦
        hasDerivAt_positiveRatioNumerator p ht).filter_mono nhdsWithin_le_nhds
    · exact ((eventually_ne_nhds one_ne_zero).mono fun _ ht ↦
        hasDerivAt_positiveRatioDenominator p ht).filter_mono nhdsWithin_le_nhds
    · have hpos : ∀ᶠ t : ℝ in 𝓝[≠] 1, 0 < t :=
        (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hpos] with t ht1 ht
      exact positiveRatioDenominatorDeriv_ne_zero (zero_lt_one.trans hp) ht (by simpa using ht1)
    · exact tendsto_nhdsWithin_of_tendsto_nhds hNzero
    · exact tendsto_nhdsWithin_of_tendsto_nhds hDzero
    · exact hfirst
  apply hraw.congr'
  have hpos : ∀ᶠ t : ℝ in 𝓝[≠] 1, 0 < t :=
    (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos] with t ht
  rw [scalarRatio_eq_explicit hp0]
  simp only [abs_of_pos ht, signedPower, sign_pos ht, SignType.coe_one, one_mul]
  unfold positiveRatioNumerator positiveRatioDenominator
  ring
