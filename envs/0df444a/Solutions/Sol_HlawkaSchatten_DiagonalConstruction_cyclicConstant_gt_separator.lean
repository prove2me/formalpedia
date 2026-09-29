-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.cyclicConstant_gt_separator
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-28T21:30:48.309881+00:00
-- url     : https://prove2.me/submissions/bd50d9a9-2471-4d23-af61-2efeab62c2be

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_TailEstimates
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Explicit uniform estimates above the cutoff

Rational logarithm bounds separate the cyclic witness and scalar envelope
at the common intermediate value `939 * p / 2000`.
-/

open HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The cyclic comparison constant

The constant is defined from an explicit scalar formula on a fixed compact
interval. Its denominator is positive, so continuity gives an attained
maximum without presupposing the global Hlawka inequality.
-/

namespace HlawkaSchatten.DiagonalConstruction











theorem cyclicB_nonneg (p t : ℝ) : 0 ≤ cyclicB p t := by
  unfold cyclicB
  positivity



theorem cyclicB_rpow {p : ℝ} (hp : 0 < p) (t : ℝ) :
    cyclicB p t ^ p = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
  rw [cyclicB, ← Real.rpow_mul (by positivity :
    0 ≤ 2 * |1 - t| ^ p + (2 : ℝ) ^ p), one_div_mul_cancel hp.ne', Real.rpow_one]



theorem continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

theorem continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const

theorem continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'



theorem cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)





end HlawkaSchatten.DiagonalConstruction

theorem cutoff_inverse_bounds {p : ℝ} (hp : 256 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1 / 256 := by
  have hp0 : 0 < p := by linarith
  exact ⟨inv_pos.mpr hp0, by simpa using (one_div_le_one_div_of_le (by norm_num) hp)⟩

theorem log_two_bounds : (693 : ℝ) / 1000 < Real.log 2 ∧ Real.log 2 < 347 / 500 := by
  constructor
  · linarith [Real.log_two_gt_d9]
  · linarith [Real.log_two_lt_d9]

theorem log_le_cutoff_tangent {p : ℝ} (hp : 256 ≤ p) :
    Real.log p ≤ p / 256 + 23 / 5 := by
  have hp0 : 0 < p := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < p / 256 by positivity)
  rw [Real.log_div hp0.ne' (by norm_num)] at h
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 8
    norm_num at hh
    exact hh
  rw [h256] at h
  linarith [log_two_bounds.2]

theorem log_mul_inv_bounds {p : ℝ} (hp : 256 ≤ p) :
    0 ≤ Real.log p * p⁻¹ ∧ Real.log p * p⁻¹ ≤ 7 / 320 := by
  have hp0 : 0 < p := by linarith
  have hi := cutoff_inverse_bounds hp
  have hl := Real.log_nonneg (show 1 ≤ p by linarith)
  have hm := mul_le_mul_of_nonneg_right (log_le_cutoff_tangent hp) hi.1.le
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  constructor
  · positivity
  · nlinarith

theorem constructionParameter_bounds {p : ℝ} (hp : 256 ≤ p) :
    1 / 2 ≤ constructionParameter p ∧ constructionParameter p ≤ 1 := by
  have hl := log_mul_inv_bounds hp
  have he := Real.add_one_le_exp (-(Real.log p * p⁻¹))
  constructor
  · dsimp [constructionParameter]
    linarith
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)

theorem constructionParameter_deficit {p : ℝ} :
    1 - constructionParameter p ≤ Real.log p * p⁻¹ := by
  have h := Real.add_one_le_exp (-(Real.log p * p⁻¹))
  dsimp [constructionParameter]
  linarith

theorem constructionParameter_power {p : ℝ} (hp : 0 < p) :
    constructionParameter p ^ p = p⁻¹ := by
  rw [constructionParameter, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : -(Real.log p * p⁻¹) * p = -Real.log p := by field_simp
  rw [he, Real.exp_neg, Real.exp_log hp]

theorem cyclicA_witness_ge_one {p : ℝ} (hp : 256 ≤ p) :
    1 ≤ cyclicA p (constructionParameter p) := by
  have hp0 : 0 < p := by linarith
  rw [cyclicA, constructionParameter_power hp0]
  apply Real.one_le_rpow
  · have h := (cutoff_inverse_bounds hp).1
    linarith
  · positivity

theorem cyclicA_witness_sub_one_le {p : ℝ} (hp : 256 ≤ p) :
    cyclicA p (constructionParameter p) - 1 ≤ (347 / 500 : ℝ) * p⁻¹ + (p⁻¹) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hi := cutoff_inverse_bounds hp
  let a := Real.log (2 + p⁻¹)
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith [hi.1])
  have hlog := Real.log_le_sub_one_of_pos (show 0 < (2 + p⁻¹) / 2 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at hlog
  have ha : a ≤ 347 / 500 + p⁻¹ / 2 := by dsimp [a]; linarith [log_two_bounds.2]
  have ha7 : a ≤ 7 / 10 := by linarith [hi.2]
  have haSq : a ^ 2 ≤ 1 / 2 := by nlinarith
  have har : 0 ≤ a * p⁻¹ := mul_nonneg ha0 hi.1.le
  have har1 : a * p⁻¹ ≤ 1 := by nlinarith [hi.2]
  have he := Real.norm_exp_sub_one_sub_id_le (x := a * p⁻¹)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg har] using har1)
  have he' := (le_abs_self (Real.exp (a * p⁻¹) - 1 - a * p⁻¹)).trans he
  simp only [Real.norm_eq_abs, abs_of_nonneg har] at he'
  have hm := mul_le_mul_of_nonneg_right ha hi.1.le
  have hs := mul_le_mul_of_nonneg_right haSq (sq_nonneg p⁻¹)
  have hA : cyclicA p (constructionParameter p) = Real.exp (a * p⁻¹) := by
    rw [cyclicA, constructionParameter_power hp0, add_comm,
      Real.rpow_def_of_pos (by positivity)]
    simp only [one_div, a]
  rw [hA]
  nlinarith

theorem cyclicB_ge_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  apply (Real.rpow_le_rpow_iff (by norm_num) (cyclicB_nonneg p t) hp).mp
  rw [cyclicB_rpow hp]
  have hn := Real.rpow_nonneg (abs_nonneg (1 - t)) p
  linarith

theorem cyclic_witness_denominator_upper {p : ℝ} (hp : 256 ≤ p) :
    6 * cyclicA p (constructionParameter p) - 3 * cyclicB p (constructionParameter p) ≤
      6 * ((347 / 500 : ℝ) * p⁻¹ + (p⁻¹) ^ 2) := by
  have hA := cyclicA_witness_sub_one_le hp
  have hB := cyclicB_ge_two (t := constructionParameter p) (show 0 < p by linarith)
  linarith

theorem three_root_le {p : ℝ} (hp : 1 ≤ p) :
    (3 : ℝ) ^ (1 / p) ≤ 1 + 2 * p⁻¹ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hi : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have h := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ 2 * p⁻¹ by linarith) hp
  have hpow : ((3 : ℝ) ^ (1 / p)) ^ p = 3 := by
    rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hp0.ne', Real.rpow_one]
  apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) hp0).mp
  rw [hpow]
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  nlinarith

theorem cyclic_witness_numerator_lower {p : ℝ} (hp : 256 ≤ p) :
    2 - (Real.log p + 3) * p⁻¹ ≤
      3 * cyclicA p (constructionParameter p) -
        (3 : ℝ) ^ (1 / p) * |2 - constructionParameter p| := by
  have hi := cutoff_inverse_bounds hp
  have ht := constructionParameter_bounds hp
  have hu := constructionParameter_deficit (p := p)
  have hl := log_mul_inv_bounds hp
  have hA := cyclicA_witness_ge_one hp
  have hc := three_root_le (show 1 ≤ p by linarith)
  have hm := mul_le_mul hc
    (show 2 - constructionParameter p ≤ 1 + Real.log p * p⁻¹ by linarith)
    (show 0 ≤ 2 - constructionParameter p by linarith) (by positivity)
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 - constructionParameter p)]
  have hsmall := mul_le_mul_of_nonneg_right hl.2 hi.1.le
  nlinarith

theorem solution {p : ℝ} (hp : 256 ≤ p) :
    (939 / 2000 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := cutoff_inverse_bounds hp
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hpi2 : p * (p⁻¹) ^ 2 = p⁻¹ := by rw [pow_two, ← mul_assoc, hpi, one_mul]
  have ht := constructionParameter_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith) (by linarith [ht.1])
  have hnum := cyclic_witness_numerator_lower hp
  have hden := cyclic_witness_denominator_upper hp
  have hdenP := mul_le_mul_of_nonneg_left hden hp0.le
  have hlog := mul_le_mul_of_nonneg_right (log_le_cutoff_tangent hp) hi.1.le
  have hratio : (939 / 2000 : ℝ) * p < cyclicRatio p (constructionParameter p) := by
    rw [cyclicRatio, lt_div_iff₀ hD]
    nlinarith
  exact hratio.trans_le (cyclicRatio_le_constant (by linarith)
    ⟨ht.1, by linarith [ht.2]⟩)
