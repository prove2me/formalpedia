-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.scalar_window66
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-10T05:21:40.103873+00:00
-- url     : https://prove2.me/submissions/87ab334c-e283-4147-a0e4-a6d231c69c56

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_maximum_attained
import Mathlib
set_option autoImplicit false

/- Solutions/Sol_Hlawka85_AnalyticScalarBounds.lean -/
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted by Codex from Claude Opus 5.5's accepted cutoff-87 scalar section,
which extends BrunoDCDO's cutoff-90 formalization of Ezzeri Esa's construction.
These are new supporting bounds for the window [85,87], not a cutoff proof.
-/

set_option autoImplicit false

namespace HlawkaSchatten.DiagonalConstruction

/-! Analytic scalar estimates on 85 ≤ p ≤ 87. These extend the
cutoff-87 witness estimates with q0 = 10717/30000; box convexity remains open. -/



lemma codex85Aux_log_ninety : Real.log (90 : ℝ) < 4499810 / 1000000 := by
  have heq : Real.log (90 : ℝ) = Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
    rw [show (90 : ℝ) = 2 * (3 ^ 2) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    ring
  rw [heq]
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]






lemma codex85Aux_exp_cubic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + 2 * x ^ 3 / 9 := by
  have h := Real.exp_bound' hx hx1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith


lemma codex85Aux_exp_neg_cubic {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z + z ^ 2 / 2 - 2 * z ^ 3 / 9 ≤ Real.exp (-z) := by
  have h := Real.exp_bound (x := -z) (n := 3) (by simpa [abs_of_nonneg hz]) (by norm_num)
  have he := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hz] at he
  nlinarith











/- The following continuity and power identities adapt the Apache-2.0 baseline by Ezzeri Esa. -/
theorem codex85Aux_cyclicB_nonneg (p t : ℝ) : 0 ≤ cyclicB p t := by
  unfold cyclicB
  positivity



theorem codex85Aux_cyclicB_rpow {p : ℝ} (hp : 0 < p) (t : ℝ) :
    cyclicB p t ^ p = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
  rw [cyclicB, ← Real.rpow_mul (by positivity :
    0 ≤ 2 * |1 - t| ^ p + (2 : ℝ) ^ p), one_div_mul_cancel hp.ne', Real.rpow_one]



theorem codex85Aux_continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))



theorem codex85Aux_continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const



theorem codex85Aux_continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (codex85Aux_continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (codex85Aux_continuous_cyclicA hp0)).sub
      (continuous_const.mul (codex85Aux_continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'



theorem codex85Aux_cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (codex85Aux_continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)





theorem codex85Aux_cyclicB_ge_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  apply (Real.rpow_le_rpow_iff (by norm_num) (codex85Aux_cyclicB_nonneg p t) hp).mp
  rw [codex85Aux_cyclicB_rpow hp]
  have hn := Real.rpow_nonneg (abs_nonneg (1 - t)) p
  linarith





lemma codex85Aux_log_two_add {x : ℝ} (hx : 0 ≤ x) :
    6931471803 / 10 ^ 10 + x / 2 - x ^ 2 / 4 ≤ Real.log (2 + x) ∧
      Real.log (2 + x) ≤ 6931471808 / 10 ^ 10 + x / 2 := by
  have hsplit : Real.log (2 + x) = Real.log 2 + Real.log ((2 + x) / 2) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    ring
  have hlo := Real.one_sub_inv_le_log_of_pos (show 0 < (2 + x) / 2 by positivity)
  have hhi := Real.log_le_sub_one_of_pos (show 0 < (2 + x) / 2 by positivity)
  have hinv : 1 - ((2 + x) / 2)⁻¹ = x / (2 + x) := by field_simp; ring
  have hfrac : x / 2 - x ^ 2 / 4 ≤ x / (2 + x) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_nonneg hx 3]
  constructor
  · rw [hsplit]; linarith [Real.log_two_gt_d9]
  · rw [hsplit]; linarith [Real.log_two_lt_d9]







lemma codex85Aux_one_sub_exp_neg {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    y - y ^ 2 / 2 ≤ 1 - Real.exp (-y) := by
  have h := Real.exp_bound (x := -y) (n := 4) (by simpa [abs_of_nonneg hy]) (by norm_num)
  have he := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hy] at he
  have h4 : y ^ 4 ≤ y ^ 3 := by nlinarith [mul_nonneg (pow_nonneg hy 3) (sub_nonneg.mpr hy1)]
  nlinarith [pow_nonneg hy 3]





/-- The improved cyclic witness `(3/(4p))^{1/p}`. -/
noncomputable def codex85Witness (p : ℝ) : ℝ :=
  Real.exp (-((Real.log p - Real.log (3 / 4)) * p⁻¹))


lemma codex85_inverse_bounds {p : ℝ} (hp : 85 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1 / 85 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩


lemma codex85_inverse_lower {p : ℝ} (hp' : p ≤ 87) (hp : 85 ≤ p) : 1 / 87 ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hp'


lemma codex85_log_eightyseven : Real.log (87 : ℝ) < 446648 / 100000 := by
  have heq : Real.log (90 : ℝ) = Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
    rw [show (90 : ℝ) = 2 * (3 ^ 2) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    ring
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 87 / 90 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), heq] at h
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]


lemma codex85_log_three_quarters :
    -2876820737 / 10 ^ 10 < Real.log (3 / 4 : ℝ) ∧ Real.log (3 / 4 : ℝ) < 0 := by
  have heq : Real.log (3 / 4 : ℝ) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  exact ⟨by rw [heq]; linarith [Real.log_two_lt_d9, Real.log_three_gt_d9],
    Real.log_neg (by norm_num) (by norm_num)⟩


lemma codex85_scaled {p : ℝ} (hp : 85 ≤ p) (hp' : p ≤ 87) :
    0 ≤ (Real.log p - Real.log (3 / 4)) * p⁻¹ ∧
      (Real.log p - Real.log (3 / 4)) * p⁻¹ ≤ 4754163 / 10 ^ 6 * p⁻¹ ∧
      (Real.log p - Real.log (3 / 4)) * p⁻¹ < 1 / 17 := by
  have hi := codex85_inverse_bounds hp
  have hl := (Real.log_le_log (by linarith) hp').trans_lt codex85_log_eightyseven
  have hl0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hk := codex85_log_three_quarters
  have hZ : Real.log p - Real.log (3 / 4) ≤ 4754163 / 10 ^ 6 := by linarith [hk.1]
  have hZ0 : 0 ≤ Real.log p - Real.log (3 / 4) := by linarith [hk.2]
  refine ⟨mul_nonneg hZ0 hi.1.le, mul_le_mul_of_nonneg_right hZ hi.1.le, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hZ hi.1.le]


lemma codex85_witness_power {p : ℝ} (hp : 0 < p) :
    codex85Witness p ^ p = 3 / 4 * p⁻¹ := by
  rw [codex85Witness, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : -((Real.log p - Real.log (3 / 4)) * p⁻¹) * p = Real.log (3 / 4) - Real.log p := by
    field_simp
    ring
  rw [he, Real.exp_sub, Real.exp_log hp, Real.exp_log (by norm_num)]
  field_simp


lemma codex85_witness_bounds {p : ℝ} (hp : 85 ≤ p) (hp' : p ≤ 87) :
    1 / 2 ≤ codex85Witness p ∧ codex85Witness p ≤ 1 := by
  have hl := codex85_scaled hp hp'
  have he := Real.add_one_le_exp (-((Real.log p - Real.log (3 / 4)) * p⁻¹))
  constructor
  · dsimp [codex85Witness]
    linarith [hl.2.2]
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)


lemma codex85_cyclicA_exp {p : ℝ} (hp : 85 ≤ p) :
    cyclicA p (codex85Witness p) =
      Real.exp (Real.log (2 + 3 / 4 * p⁻¹) * p⁻¹) := by
  rw [cyclicA, codex85_witness_power (by linarith), add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]


/-- Lower bound for the cyclic numerator at the improved witness. -/
noncomputable def codex85Nlo (x : ℝ) : ℝ :=
  3 * (1 + (6931471803 / 10 ^ 10 + 3 / 4 * x / 2 - (3 / 4 * x) ^ 2 / 4) * x +
      ((6931471803 / 10 ^ 10 + 3 / 4 * x / 2 - (3 / 4 * x) ^ 2 / 4) * x) ^ 2 / 2) -
    (1 + 1098612289 / 10 ^ 9 * x + (1098612289 / 10 ^ 9 * x) ^ 2 / 2 +
        2 * (1098612289 / 10 ^ 9 * x) ^ 3 / 9) *
      (1 + 4754163 / 10 ^ 6 * x - (4754163 / 10 ^ 6 * x) ^ 2 / 2 +
        2 * (4754163 / 10 ^ 6 * x) ^ 3 / 9)


/-- Upper bound for the cyclic denominator at the improved witness. -/
noncomputable def codex85Dup (x : ℝ) : ℝ :=
  6 * ((6931471808 / 10 ^ 10 + 3 / 4 * x / 2) * x +
    ((6931471808 / 10 ^ 10 + 3 / 4 * x / 2) * x) ^ 2 / 2 +
    2 * ((6931471808 / 10 ^ 10 + 3 / 4 * x / 2) * x) ^ 3 / 9)


/-- Lower bound for the envelope deficit. -/
noncomputable def codex85Glo (x : ℝ) : ℝ :=
  (6931471803 / 10 ^ 10 - x ^ 2 / 1000) * x - (6931471808 / 10 ^ 10 * x) ^ 2 / 2


set_option maxHeartbeats 4000000 in
lemma codex85_envelope_certificate {x : ℝ} (h1 : 1 / 87 ≤ x) (h2 : x ≤ 1 / 85) :
    (1 - 10717 / 30000 : ℝ) * codex85Dup x < codex85Nlo x * (2 * codex85Glo x) := by
  unfold codex85Dup codex85Nlo codex85Glo
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1 / 87 + s := ⟨x - 1 / 87, by linarith, by ring⟩
  have hs2 : s ≤ 2 / 7395 := by linarith
  nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs, pow_nonneg hs 4, pow_nonneg hs 5,
    pow_nonneg hs 6, pow_nonneg hs 7, pow_nonneg hs 8, pow_nonneg hs 9, pow_nonneg hs 10,
    mul_nonneg hs (sub_nonneg.mpr hs2)]


set_option maxHeartbeats 4000000 in
lemma codex85_linear_certificate {x : ℝ} (h1 : 1 / 87 ≤ x) (h2 : x ≤ 1 / 85) :
    (20 / 43 : ℝ) * codex85Dup x < x * codex85Nlo x := by
  unfold codex85Dup codex85Nlo
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1 / 87 + s := ⟨x - 1 / 87, by linarith, by ring⟩
  have hs2 : s ≤ 2 / 7395 := by linarith
  nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs, pow_nonneg hs 4, pow_nonneg hs 5,
    pow_nonneg hs 6, pow_nonneg hs 7, pow_nonneg hs 8,
    mul_nonneg hs (sub_nonneg.mpr hs2)]


lemma codex85_Nlo_pos {x : ℝ} (h1 : 1 / 87 ≤ x) (h2 : x ≤ 1 / 85) : 0 < codex85Nlo x := by
  have h := codex85_linear_certificate h1 h2
  have hD : 0 < codex85Dup x := by
    unfold codex85Dup
    have hx : 0 < x := by linarith
    positivity
  nlinarith


lemma codex85_Glo_pos {x : ℝ} (h1 : 1 / 87 ≤ x) (h2 : x ≤ 1 / 85) : 0 < codex85Glo x := by
  unfold codex85Glo
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ x by linarith) 3]


lemma codex85_numerator_lower {p : ℝ} (hp : 85 ≤ p) (hp' : p ≤ 87) :
    codex85Nlo p⁻¹ ≤
      3 * cyclicA p (codex85Witness p) -
        (3 : ℝ) ^ (1 / p) * |2 - codex85Witness p| := by
  set x := p⁻¹ with hxdef
  have hi := codex85_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ht := codex85_witness_bounds hp hp'
  have hl := codex85_scaled hp hp'
  have hC0 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hC : Real.log (3 : ℝ) < 1098612289 / 10 ^ 9 := by linarith [Real.log_three_lt_d9]
  have hroot : (3 : ℝ) ^ (1 / p) = Real.exp (Real.log 3 * x) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div]
  have hcx0 : 0 ≤ Real.log 3 * x := mul_nonneg hC0 hx0
  have hcx : Real.log 3 * x ≤ 1098612289 / 10 ^ 9 * x := mul_le_mul_of_nonneg_right hC.le hx0
  have hcx1 : 1098612289 / 10 ^ 9 * x ≤ 1 := by nlinarith
  have hR := codex85Aux_exp_cubic hcx0 (hcx.trans hcx1)
  have hRmono : 1 + Real.log 3 * x + (Real.log 3 * x) ^ 2 / 2 + 2 * (Real.log 3 * x) ^ 3 / 9 ≤
      1 + 1098612289 / 10 ^ 9 * x + (1098612289 / 10 ^ 9 * x) ^ 2 / 2 +
        2 * (1098612289 / 10 ^ 9 * x) ^ 3 / 9 := by
    have h2 := pow_le_pow_left₀ hcx0 hcx 2
    have h3 := pow_le_pow_left₀ hcx0 hcx 3
    linarith
  set z := (Real.log p - Real.log (3 / 4)) * x with hzdef
  have hz0 : 0 ≤ z := hl.1
  have hzZ : z ≤ 4754163 / 10 ^ 6 * x := hl.2.1
  have hz1 : z ≤ 1 := by linarith [hl.2.2]
  have hT := codex85Aux_exp_neg_cubic hz0 hz1
  have htdef : codex85Witness p = Real.exp (-z) := rfl
  have habs : |2 - codex85Witness p| = 2 - codex85Witness p :=
    abs_of_nonneg (by linarith [ht.2])
  have hTmono : 1 + z - z ^ 2 / 2 + 2 * z ^ 3 / 9 ≤
      1 + 4754163 / 10 ^ 6 * x - (4754163 / 10 ^ 6 * x) ^ 2 / 2 +
        2 * (4754163 / 10 ^ 6 * x) ^ 3 / 9 := by
    have hZ1 : 4754163 / 10 ^ 6 * x ≤ 1 / 17 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hzZ) hz0, mul_nonneg (sub_nonneg.mpr hzZ)
      (mul_nonneg hz0 hz0), mul_nonneg (sub_nonneg.mpr hzZ) (sub_nonneg.mpr hzZ)]
  have hTup : 2 - codex85Witness p ≤
      1 + 4754163 / 10 ^ 6 * x - (4754163 / 10 ^ 6 * x) ^ 2 / 2 +
        2 * (4754163 / 10 ^ 6 * x) ^ 3 / 9 := by
    rw [htdef]; linarith
  have hT0 : 0 ≤ 2 - codex85Witness p := by linarith [ht.2]
  have hprod := mul_le_mul (hR.trans hRmono) hTup hT0
    (by positivity : (0 : ℝ) ≤ 1 + 1098612289 / 10 ^ 9 * x + (1098612289 / 10 ^ 9 * x) ^ 2 / 2 +
        2 * (1098612289 / 10 ^ 9 * x) ^ 3 / 9)
  have hkx0 : 0 ≤ 3 / 4 * x := by positivity
  have ha := codex85Aux_log_two_add hkx0
  have hA := Real.quadratic_le_exp_of_nonneg
    (mul_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + 3 / 4 * x)) hx0)
  rw [← codex85_cyclicA_exp hp] at hA
  have hy1 : 0 ≤ (6931471803 / 10 ^ 10 + 3 / 4 * x / 2 - (3 / 4 * x) ^ 2 / 4) * x := by
    apply mul_nonneg _ hx0; nlinarith
  have hyy := mul_le_mul_of_nonneg_right ha.1 hx0
  have hAmono : 1 + (6931471803 / 10 ^ 10 + 3 / 4 * x / 2 - (3 / 4 * x) ^ 2 / 4) * x +
      ((6931471803 / 10 ^ 10 + 3 / 4 * x / 2 - (3 / 4 * x) ^ 2 / 4) * x) ^ 2 / 2 ≤
      1 + Real.log (2 + 3 / 4 * x) * x + (Real.log (2 + 3 / 4 * x) * x) ^ 2 / 2 := by
    have h2 := pow_le_pow_left₀ hy1 hyy 2
    linarith
  rw [hroot, habs]
  unfold codex85Nlo
  linarith


lemma codex85_denominator_upper {p : ℝ} (hp : 85 ≤ p) :
    6 * cyclicA p (codex85Witness p) - 3 * cyclicB p (codex85Witness p) ≤
      codex85Dup p⁻¹ := by
  set x := p⁻¹ with hxdef
  have hi := codex85_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have hkx0 : 0 ≤ 3 / 4 * x := by positivity
  have ha := codex85Aux_log_two_add hkx0
  have ha0 : 0 ≤ Real.log (2 + 3 / 4 * x) := Real.log_nonneg (by linarith)
  have hy0 : 0 ≤ Real.log (2 + 3 / 4 * x) * x := mul_nonneg ha0 hx0
  have hyy := mul_le_mul_of_nonneg_right ha.2 hx0
  have hy1 : (6931471808 / 10 ^ 10 + 3 / 4 * x / 2) * x ≤ 1 := by nlinarith
  have hE := codex85Aux_exp_cubic hy0 (hyy.trans hy1)
  rw [← codex85_cyclicA_exp hp] at hE
  have hB := codex85Aux_cyclicB_ge_two (t := codex85Witness p) (show 0 < p by linarith)
  have h2 := pow_le_pow_left₀ hy0 hyy 2
  have h3 := pow_le_pow_left₀ hy0 hyy 3
  unfold codex85Dup
  linarith


lemma codex85_cyclicConstant_gt_linear {p : ℝ} (hp : 85 ≤ p) (hp' : p ≤ 87) :
    (20 / 43 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := codex85_inverse_bounds hp
  have hi' := codex85_inverse_lower hp' hp
  have ht := codex85_witness_bounds hp hp'
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codex85Witness p by linarith [ht.1])
  have hn := codex85_numerator_lower hp hp'
  have hd := codex85_denominator_upper hp
  have hc := codex85_linear_certificate hi' hi.2
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hr : (20 / 43 : ℝ) * p < cyclicRatio p (codex85Witness p) := by
    rw [cyclicRatio, lt_div_iff₀ hD]
    have hcp := mul_lt_mul_of_pos_left hc hp0
    have hdp := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 20 / 43 * p by positivity)
    have : p * (p⁻¹ * codex85Nlo p⁻¹) = codex85Nlo p⁻¹ := by
      rw [← mul_assoc, hpi, one_mul]
    nlinarith
  exact hr.trans_le (codex85Aux_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)


lemma codex85_power_tail {p : ℝ} (hp : 85 ≤ p) (hp' : p ≤ 87) :
    (10717 / 30000 : ℝ) ^ p < (p⁻¹) ^ 2 / 1000 := by
  have hp0 : 0 < p := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num)
    (show 1 ≤ p - 20 by linarith)
  norm_num at h
  have heq : (2 : ℝ) ^ p = 1048576 * (2 : ℝ) ^ (p - 20) := by
    rw [show p = (p - 20) + 20 by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  have htwo : 1000 * p ^ 2 < (2 : ℝ) ^ p := by rw [heq]; nlinarith
  calc
    (10717 / 30000 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ p :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hp0.le
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, Real.inv_rpow (by norm_num)]
    _ < (1000 * p ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) htwo
    _ = (p⁻¹) ^ 2 / 1000 := by field_simp


lemma codex85_envelope_deficit {p : ℝ} (hp : 85 ≤ p) (hp' : p ≤ 87) :
    codex85Glo p⁻¹ < 1 - scalarEnvelopeRoot p (10717 / 30000) := by
  have hi := codex85_inverse_bounds hp
  set x := p⁻¹ with hxdef
  let a := (10717 / 30000 : ℝ) ^ p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a < x ^ 2 / 1000 := codex85_power_tail hp hp'
  let d := Real.log 2 - Real.log (1 + a)
  have hdLower : Real.log 2 - x ^ 2 / 1000 < d := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + a by positivity)
    dsimp [d]
    linarith
  have hdUpper : d ≤ Real.log 2 := by
    have hh := Real.log_nonneg (show 1 ≤ 1 + a by linarith)
    dsimp [d]
    linarith
  have hL : 6931471803 / 10 ^ 10 < Real.log (2 : ℝ) ∧ Real.log 2 < 6931471808 / 10 ^ 10 := by
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have hx2 : x ^ 2 / 1000 ≤ 1 / 1000 := by nlinarith [hi.1, hi.2]
  have hd0 : 0 ≤ d := by linarith [hL.1]
  have hdx0 : 0 ≤ d * x := mul_nonneg hd0 hi.1.le
  have hdx1 : d * x ≤ 1 := by nlinarith [hL.2]
  have he := codex85Aux_one_sub_exp_neg hdx0 hdx1
  have hdx : d * x ≤ 6931471808 / 10 ^ 10 * x := mul_le_mul_of_nonneg_right (by linarith) hi.1.le
  have hsq := pow_le_pow_left₀ hdx0 hdx 2
  have hm := mul_lt_mul_of_pos_right (show 6931471803 / 10 ^ 10 - x ^ 2 / 1000 < d by linarith) hi.1
  have hg : scalarEnvelopeRoot p (10717 / 30000) = Real.exp (-(d * x)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d, a]
    simp only [one_div, hxdef]
    ring
  rw [hg]
  unfold codex85Glo
  linarith


lemma codex85_envelope_lt {p : ℝ} (hp : 85 ≤ p) (hp' : p ≤ 87) :
    scalarEnvelope p (10717 / 30000) < cyclicConstant p := by
  have hi := codex85_inverse_bounds hp
  have hi' := codex85_inverse_lower hp' hp
  have ht := codex85_witness_bounds hp hp'
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codex85Witness p by linarith [ht.1])
  have hn := codex85_numerator_lower hp hp'
  have hd := codex85_denominator_upper hp
  have hg := codex85_envelope_deficit hp hp'
  have hc := codex85_envelope_certificate hi' hi.2
  have hN0 := codex85_Nlo_pos hi' hi.2
  have hG0 := codex85_Glo_pos hi' hi.2
  have henvD : 0 < 2 * (1 - scalarEnvelopeRoot p (10717 / 30000)) := by linarith
  have hr : scalarEnvelope p (10717 / 30000) < cyclicRatio p (codex85Witness p) := by
    rw [scalarEnvelope, cyclicRatio, div_lt_div_iff₀ henvD hD]
    calc
      _ ≤ (1 - (10717 / 30000 : ℝ)) * codex85Dup p⁻¹ :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ < codex85Nlo p⁻¹ * (2 * codex85Glo p⁻¹) := hc
      _ ≤ (3 * cyclicA p (codex85Witness p) -
          (3 : ℝ) ^ (1 / p) * |2 - codex85Witness p|) *
          (2 * (1 - scalarEnvelopeRoot p (10717 / 30000))) :=
        mul_le_mul hn (by linarith) (by linarith) (hN0.le.trans hn)
  exact hr.trans_le (codex85Aux_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)


end HlawkaSchatten.DiagonalConstruction

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.codex85_scalar_solution : ∀ p : ℝ, 85 ≤ p → p ≤ 87 →
    (20 / 43 : ℝ) * p < cyclicConstant p ∧
      scalarEnvelope p (10717 / 30000) < cyclicConstant p := by
  intro p hp hp'
  exact ⟨codex85_cyclicConstant_gt_linear hp hp', codex85_envelope_lt hp hp'⟩


/- Solutions/Hlawka84_LogTangent.lean -/
set_option autoImplicit false

namespace HlawkaCodex84Scalar

theorem log_seven_eighths : Real.log (7/8 : ℝ) < -(13353139/10^8 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7/8)).mpr
  have h := Real.exp_bound (x := -(13353139/10^8 : ℝ)) (n := 10)
    (by norm_num) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  linarith

theorem log_one_twelve : Real.log (112 : ℝ) < 471849888/10^8 := by
  have he : Real.log (112 : ℝ) = 7*Real.log 2+Real.log (7/8 : ℝ) := by
    rw [show (112 : ℝ) = 2^7*(7/8) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_lt_d9, log_seven_eighths]

/-- Tangent at84, retaining the dependence on p rather than its upper endpoint. -/
theorem witness_log_tangent {p : ℝ} (hp : 0 < p) :
    Real.log p-Real.log (3/4 : ℝ) ≤ 471849888/10^8+(p-84)/84 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < p/84 by positivity)
  rw [Real.log_div hp.ne' (by norm_num)] at h
  have he : Real.log (84 : ℝ)-Real.log (3/4 : ℝ) = Real.log (112 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  linarith [log_one_twelve]

theorem witness_scaled_tangent {p : ℝ} (hp : 0 < p) :
    (Real.log p-Real.log (3/4 : ℝ))*p⁻¹ ≤
      (371849888/10^8 : ℝ)*p⁻¹+1/84 := by
  have h := mul_le_mul_of_nonneg_right (witness_log_tangent hp) (inv_nonneg.mpr hp.le)
  have he : (471849888/10^8+(p-84)/84)*p⁻¹ =
      (371849888/10^8 : ℝ)*p⁻¹+1/84 := by
    field_simp
    ring
  rwa [he] at h

end HlawkaCodex84Scalar


/- Solutions/Hlawka84_TaylorBounds.lean -/
set_option autoImplicit false

namespace HlawkaCodex84Scalar

theorem exp_quartic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1+x+x^2/2+x^3/6+x^4/12 := by
  have h := Real.exp_bound' hx hx1 (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [pow_nonneg hx 4]

theorem exp_neg_quartic_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1-x+x^2/2-x^3/6-x^4/12 ≤ Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (n := 4)
    (by simpa only [abs_neg, abs_of_nonneg hx] using hx1) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx] at hh
  nlinarith [pow_nonneg hx 4]

theorem one_sub_exp_neg_quartic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x-x^2/2+x^3/6-x^4/12 ≤ 1-Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (n := 4)
    (by simpa only [abs_neg, abs_of_nonneg hx] using hx1) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx] at hh
  nlinarith [pow_nonneg hx 4]

theorem log_one_add_upper {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    Real.log (1+u) ≤ u-u^2/2+2*u^3 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -u) (by rw [abs_neg, abs_of_nonneg hu]; linarith) 2
  have hh := (abs_le.mp h).2
  norm_num [Finset.sum_range_succ, abs_of_nonneg hu] at hh
  have hd : 0 < 1-u := by linarith
  have he : u^3/(1-u) ≤ 2*u^3 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (pow_nonneg hu 3) (show 0 ≤ 1-2*u by linarith)]
  linarith

theorem log_two_add_upper {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (2+x) ≤ 6931471808/10^10+x/2-x^2/8+x^3/4 := by
  have h := log_one_add_upper (u := x/2) (by positivity) (by linarith)
  have he : Real.log (2+x) = Real.log 2+Real.log (1+x/2) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    ring
  rw [he]
  nlinarith [Real.log_two_lt_d9]

end HlawkaCodex84Scalar
/- Solutions/Hlawka66_ScalarCertificates.lean -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace HlawkaCodex66Scalar
noncomputable def Nlo (x : ℝ) : ℝ :=
  let z := (371849888/10^8 : ℝ)*x+1/84
  let y := (6931471803/10^10+3/8*x-9/64*x^2)*x
  let c := (1098612289/10^9 : ℝ)*x
  3*(1+y+y^2/2)-(1+c+c^2/2+c^3/6+c^4/12)*(1+z-z^2/2+z^3/6+z^4/12)
noncomputable def Dup (x : ℝ) : ℝ :=
  let t := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  6*(t+t^2/2+t^3/6+t^4/12)
noncomputable def Glo (x : ℝ) : ℝ :=
  let g := (6931471803/10^10-x^2/1000)*x
  g-(6931471808/10^10*x)^2/2+g^3/6-(6931471808/10^10*x)^4/12

noncomputable def envelopeBernstein (x : ℝ) : ℝ :=
    (25522439334814841616904028021828302174587587014180119249050380509556535644991475519284131377311196598018014606188231743646179447351122906107792236443/9765625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^0*(1/66-x)^17 +
    (85160094568992197799439247214187451585558879398837524771400767361403051529369871496543869510302848679913062042586683327529392703095653175652406210457/1953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^1*(1/66-x)^16 +
    (167058966635256619872283484153764325135075050547951598820120166946107941870709503955569567701989902505532472805524119409349629110810252770620781457999/488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^2*(1/66-x)^15 +
    (818844620614203798172077224315113481682308987794456705280968576891900966354474616146056208213822884669434465546470598026668522570586366811980467625119/488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^3*(1/66-x)^14 +
    (1403938075340496652296631132855797933494366629174499264740374698580373135799568786882357842146446581136081237582501354877147920712618588811583878007201/244140625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^4*(1/66-x)^13 +
    (8935198754127881786271478915507301245906964210771892790066955068416126933636511016006631674044491385160589372697711968501926646156196977923191751267073/610351562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^5*(1/66-x)^12 +
    (13989058541911139753108038009227538824253291886880634632762634591625020129909166130466239314205477462468841104761580418164489605746745349582231596561991/488281250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^6*(1/66-x)^11 +
    (4299170218148732716546173742578269432046845049997179644473851688493865872499972019726676500344827179033320413381553096672162307211071128101262309847827/97656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^7*(1/66-x)^10 +
    (420095552127164771307736422373347007706181679070039428339484925213790610139340325860630593371071562841305232840954019820806544750514986915335581221619/7812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^8*(1/66-x)^9 +
    (82038345677945485061149396852357207457570843493789600370951046982735717946479433994076996322952159973085826522572306086370315847888972725824226365981/1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^9*(1/66-x)^8 +
    (32016444995780316605812513121937735031379807174952201349615259073337467801095344791025886170414444578362838671269226148850532675529584244235577757461/781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^10*(1/66-x)^7 +
    (3972304673417237955735832727319684157911720993619992362749786664272175770708430351836651942157436043876604323643432284280974095192364805565982878993/156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^11*(1/66-x)^6 +
    (96723773058116590200679356337526864759845194713619321834078304291932488763835534046814787180368682458075997528412503492001434946182815307549116169/7812500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^12*(1/66-x)^5 +
    (78191151355785988193696408895735952633297241544507915464662143612325781887802522803886883596319476677990015029651219205647185288257050646505797213/16875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^13*(1/66-x)^4 +
    (2895610110240915048589337504137519127008321453280329618344199056749073409717339880136546194258644863327132531723086972228331093876360542424050473/2250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^14*(1/66-x)^3 +
    (62485484998033270836224732205424085336889177420614620681487002126957401518530830538219573621889869908266810356184170422562965854227293086974297/250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^15*(1/66-x)^2 +
    (6060935037816142729274108077565232800843811813168700952259229247202583345640006507446235894774704723386605658796533468060072134004143636853139/200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^16*(1/66-x)^1 +
    (69080575991679998426429290129489265225774103799199948166886180438271899932930968372891827559506923992467444487672479275149457342539256722313/40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^17*(1/66-x)^0

theorem envelope_identity (x : ℝ) : Nlo x*(2*Glo x)-(1-73/200)*Dup x = envelopeBernstein x := by
  dsimp [Nlo, Dup, Glo, envelopeBernstein]
  ring

theorem envelope_certificate {x : ℝ} (hlo : 1/70 ≤ x) (hhi : x ≤ 1/66) :
    0 < Nlo x*(2*Glo x)-(1-73/200)*Dup x := by
  rw [envelope_identity]
  unfold envelopeBernstein
  by_cases ht : x < 1/66
  · have hl : 0 ≤ x-1/70 := by linarith
    have hr : 0 < 1/66-x := by linarith
    positivity
  · have he : x = 1/66 := by linarith
    rw [he]
    norm_num

noncomputable def linearBernstein (x : ℝ) : ℝ :=
    (18379496571375121217477537485162386154268863148658834252471793375599733589396410319549589847320875309479713/10000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^0*(1/66-x)^16 +
    (144918414231112616473598436698538892636759655045020385265984019214546936706852203730764450194010262619900353/5000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^1*(1/66-x)^15 +
    (1070846020193092973246009429575238481157661359682277016934900018152236164135517444220731545406635371435101339/5000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^2*(1/66-x)^14 +
    (984333985703920787621205047173071938683966152218600374807728650784176993450825205663884340386481921415836837/1000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^3*(1/66-x)^13 +
    (3149451565645514834565457360505835673098731422173679967794063916204900986719839879847772461202718254957622193/1000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^4*(1/66-x)^12 +
    (37191975950901564763298249410731803807301030413607116417798260453703146312151398827089352335513681478817249749/5000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^5*(1/66-x)^11 +
    (67071945804463178493480327318122697004666449868858906158434108673623251783316890103512590593948235492677323503/5000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^6*(1/66-x)^10 +
    (94211293651714405581509816537955828362391206900462956349845505681290333325303903354888189780155042908240743709/5000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^7*(1/66-x)^9 +
    (10416402309597844007950387538437432959321223631957242440301645836809712655527526050817430276489983881085100487/500000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^8*(1/66-x)^8 +
    (3638156590980937786273454389415376341351948772627234723830694418238985818599149264867709837180869857515568859/200000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^9*(1/66-x)^7 +
    (500092945839756638134665482439826506320744431541694036288947318120305806689756479337699954210806716019608309/40000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^10*(1/66-x)^6 +
    (53537284377173485034702936086484490126151675766235580431025512271753177444692505918186919223058466707457499/8000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^11*(1/66-x)^5 +
    (4375803790821148268269954052795777864761901468542804913277851992836144257525794035910888612369138769882391/1600000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^12*(1/66-x)^4 +
    (263962454731592994772894814944221534700854923610139332679776461048520558675420929002229320765699218073551/320000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^13*(1/66-x)^3 +
    (11082722014940051172763765652919705417873029882613404339640599126888230329874366351893653031771803159241/64000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^14*(1/66-x)^2 +
    (289352476000346000464668745591960728559230851425210704018535925321855572797314504766450187698670463391/12800000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^15*(1/66-x)^1 +
    (7077776272898580435126792187464721238207027700809539134656141795828387044553963714100853717754011047/5120000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/70)^16*(1/66-x)^0

theorem linear_identity (x : ℝ) : x*Nlo x-(23/50)*Dup x = linearBernstein x := by
  dsimp [Nlo, Dup, Glo, linearBernstein]
  ring

theorem linear_certificate {x : ℝ} (hlo : 1/70 ≤ x) (hhi : x ≤ 1/66) :
    0 < x*Nlo x-(23/50)*Dup x := by
  rw [linear_identity]
  unfold linearBernstein
  by_cases ht : x < 1/66
  · have hl : 0 ≤ x-1/70 := by linarith
    have hr : 0 < 1/66-x := by linarith
    positivity
  · have he : x = 1/66 := by linarith
    rw [he]
    norm_num

end HlawkaCodex66Scalar

/- Solutions/Hlawka66_WitnessBounds.lean -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction
open HlawkaCodex66Scalar
open HlawkaCodex84Scalar (witness_scaled_tangent exp_quartic exp_neg_quartic_lower log_two_add_upper)

lemma codex66_inverse_bounds {p : ℝ} (hp : 66 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1/66 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩
lemma codex66_inverse_lower {p : ℝ} (hp : 66 ≤ p) (hhi : p ≤ 70) : 1/70 ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hhi
lemma codex66_scaled {p : ℝ} (hp : 66 ≤ p) :
    0 ≤ (Real.log p-Real.log (3/4))*p⁻¹ ∧
    (Real.log p-Real.log (3/4))*p⁻¹ ≤ (371849888/10^8 : ℝ)*p⁻¹+1/84 ∧
    (371849888/10^8 : ℝ)*p⁻¹+1/84 <1/14 := by
  have hi := codex66_inverse_bounds hp
  have h0 : 0 ≤ Real.log p-Real.log (3/4) := by
    linarith [Real.log_nonneg (show 1 ≤ p by linarith), codex85_log_three_quarters.2]
  exact ⟨mul_nonneg h0 hi.1.le, witness_scaled_tangent (by linarith), by linarith [hi.2]⟩
lemma codex66_witness_bounds {p : ℝ} (hp : 66 ≤ p) :
    1/2 ≤ codex85Witness p ∧ codex85Witness p ≤ 1 := by
  have hl := codex66_scaled hp
  have h := Real.add_one_le_exp (-((Real.log p-Real.log (3/4))*p⁻¹))
  exact ⟨by dsimp [codex85Witness]; linarith [hl.2.1,hl.2.2],
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)⟩
lemma codex66_cyclicA_exp {p : ℝ} (hp : 66 ≤ p) :
    cyclicA p (codex85Witness p) = Real.exp (Real.log (2+3/4*p⁻¹)*p⁻¹) := by
  rw [cyclicA, codex85_witness_power (by linarith), add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]

lemma codex66_numerator_lower {p : ℝ} (hp : 66 ≤ p) :
    Nlo p⁻¹ ≤ 3*cyclicA p (codex85Witness p)-(3 : ℝ)^(1/p)*|2-codex85Witness p| := by
  set x := p⁻¹ with hxdef
  have hi := codex66_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ht := codex66_witness_bounds hp
  have hl := codex66_scaled hp
  let C : ℝ := 1098612289/10^9*x
  let Z : ℝ := 371849888/10^8*x+1/84
  have hc0 : 0 ≤ C := by dsimp [C]; positivity
  have hc1 : C ≤ 1 := by dsimp [C]; linarith [hi.2]
  have hz0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hz1 : Z ≤ 1 := by dsimp [Z]; linarith [hl.2.2]
  have hroot : (3 : ℝ)^(1/p) = Real.exp (Real.log 3*x) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div]
  have hc : Real.log 3*x ≤ C := by
    apply mul_le_mul_of_nonneg_right _ hx0
    linarith [Real.log_three_lt_d9]
  have hr := (Real.exp_le_exp.mpr hc).trans (exp_quartic hc0 hc1)
  have hw : Real.exp (-Z) ≤ codex85Witness p := by
    apply Real.exp_le_exp.mpr
    dsimp [Z]
    linarith [hl.2.1]
  have htup : 2-codex85Witness p ≤ 1+Z-Z^2/2+Z^3/6+Z^4/12 := by
    have h := exp_neg_quartic_lower hz0 hz1
    linarith
  have habs : |2-codex85Witness p| = 2-codex85Witness p := abs_of_nonneg (by linarith [ht.2])
  have hprod := mul_le_mul hr htup (show 0 ≤ 2-codex85Witness p by linarith [ht.2])
    (show 0 ≤ 1+C+C^2/2+C^3/6+C^4/12 by positivity)
  have ha := codex85Aux_log_two_add (show 0 ≤ 3/4*x by positivity)
  have hA := Real.quadratic_le_exp_of_nonneg
    (mul_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2+3/4*x)) hx0)
  rw [← codex66_cyclicA_exp hp] at hA
  have hy0 : 0 ≤ (6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x := by
    apply mul_nonneg _ hx0
    nlinarith [hi.2]
  have hyy := mul_le_mul_of_nonneg_right ha.1 hx0
  have hAmono : 1+(6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x+
      ((6931471803/10^10+3/4*x/2-(3/4*x)^2/4)*x)^2/2 ≤
      1+Real.log (2+3/4*x)*x+(Real.log (2+3/4*x)*x)^2/2 := by
    have h2 := pow_le_pow_left₀ hy0 hyy 2
    linarith
  rw [hroot,habs]
  dsimp [Nlo,C,Z] at hprod ⊢
  nlinarith

lemma codex66_denominator_upper {p : ℝ} (hp : 66 ≤ p) :
    6*cyclicA p (codex85Witness p)-3*cyclicB p (codex85Witness p) ≤ Dup p⁻¹ := by
  set x := p⁻¹ with hxdef
  have hi := codex66_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have hk0 : 0 ≤ 3/4*x := by positivity
  have hk1 : 3/4*x ≤ 1 := by linarith [hi.2]
  have ha := log_two_add_upper hk0 hk1
  have hy0 : 0 ≤ Real.log (2+3/4*x)*x :=
    mul_nonneg (Real.log_nonneg (by linarith)) hx0
  let T : ℝ := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  have hyy : Real.log (2+3/4*x)*x ≤ T := by
    have h := mul_le_mul_of_nonneg_right ha hx0
    dsimp [T]
    nlinarith
  have ht0 : 0 ≤ T := hy0.trans hyy
  have hx2 := pow_le_pow_left₀ hx0 hi.2 2
  have hx3 := pow_le_pow_left₀ hx0 hi.2 3
  have ht1 : T ≤ 1 := by
    dsimp [T]
    have hinner : 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 ≤ 1 := by
      nlinarith [sq_nonneg x]
    have h := mul_le_mul_of_nonneg_right hinner hx0
    nlinarith [hi.2]
  have hE := (Real.exp_le_exp.mpr hyy).trans (exp_quartic ht0 ht1)
  rw [← codex66_cyclicA_exp hp] at hE
  have hB := codex85Aux_cyclicB_ge_two (t := codex85Witness p) (show 0 < p by linarith)
  dsimp [Dup,T] at hE ⊢
  linarith

end HlawkaSchatten.DiagonalConstruction

/- Solutions/Hlawka66_ScalarBounds.lean -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction
open HlawkaCodex66Scalar
open HlawkaCodex84Scalar (one_sub_exp_neg_quartic)

lemma codex66_cyclicConstant_gt_linear {p : ℝ} (hp : 66 ≤ p) (hp' : p ≤ 70) :
    (23 / 50 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := codex66_inverse_bounds hp
  have hi' := codex66_inverse_lower hp hp'
  have ht := codex66_witness_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codex85Witness p by linarith [ht.1])
  have hn := codex66_numerator_lower hp
  have hd := codex66_denominator_upper hp
  have hc := (sub_pos.mp (linear_certificate hi' hi.2))
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hr : (23 / 50 : ℝ) * p < cyclicRatio p (codex85Witness p) := by
    rw [cyclicRatio, lt_div_iff₀ hD]
    have hcp := mul_lt_mul_of_pos_left hc hp0
    have hdp := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 23 / 50 * p by positivity)
    have : p * (p⁻¹ * Nlo p⁻¹) = Nlo p⁻¹ := by
      rw [← mul_assoc, hpi, one_mul]
    nlinarith
  exact hr.trans_le (codex85Aux_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)


lemma codex66_power_tail {p : ℝ} (hp : 66 ≤ p) (hp' : p ≤ 70) :
    (73/200 : ℝ) ^ p < (p⁻¹) ^ 2 / 1000 := by
  have hp0 : 0 < p := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num)
    (show 1 ≤ p - 20 by linarith)
  norm_num at h
  have heq : (2 : ℝ) ^ p = 1048576 * (2 : ℝ) ^ (p - 20) := by
    rw [show p = (p - 20) + 20 by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  have htwo : 1000 * p ^ 2 < (2 : ℝ) ^ p := by rw [heq]; nlinarith
  calc
    (73/200 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ p :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hp0.le
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, Real.inv_rpow (by norm_num)]
    _ < (1000 * p ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) htwo
    _ = (p⁻¹) ^ 2 / 1000 := by field_simp


lemma codex66_Dup_pos {x : ℝ} (hx : 0 < x) (hhi : x ≤ 1/66) : 0 < Dup x := by
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have h : 0 < 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 := by
    nlinarith [pow_nonneg hx.le 3]
  dsimp [Dup]
  positivity

lemma codex66_Nlo_pos {x : ℝ} (hlo : 1/70 ≤ x) (hhi : x ≤ 1/66) : 0 < Nlo x := by
  have hx : 0 < x := by linarith
  have hc := sub_pos.mp (linear_certificate hlo hhi)
  have hd := codex66_Dup_pos hx hhi
  nlinarith

lemma codex66_Glo_pos {x : ℝ} (hlo : 1/70 ≤ x) (hhi : x ≤ 1/66) : 0 < Glo x := by
  have hx : 0 < x := by linarith
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have hx4 := pow_le_pow_left₀ hx.le hhi 4
  have hg : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hx.le
    nlinarith
  dsimp [Glo]
  nlinarith [pow_nonneg hg 3]

lemma codex66_envelope_deficit {p : ℝ} (hp : 66 ≤ p) (hp' : p ≤ 70) :
    Glo p⁻¹ < 1-scalarEnvelopeRoot p (73/200) := by
  have hi := codex66_inverse_bounds hp
  set x := p⁻¹ with hxdef
  let a := (73/200 : ℝ)^p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a < x^2/1000 := codex66_power_tail hp hp'
  let d := Real.log 2-Real.log (1+a)
  have hdLower : Real.log 2-x^2/1000 < d := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1+a by positivity)
    dsimp [d]
    linarith
  have hdUpper : d ≤ Real.log 2 := by
    have h := Real.log_nonneg (show 1 ≤ 1+a by linarith)
    dsimp [d]
    linarith
  have hL : (6931471803/10^10 : ℝ) < Real.log 2 ∧ Real.log 2 <6931471808/10^10 := by
    constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]
  have hx2 : x^2/1000 ≤ 1/1000 := by nlinarith [hi.1,hi.2]
  have hd0 : 0 ≤ d := by linarith [hL.1]
  have hdx0 : 0 ≤ d*x := mul_nonneg hd0 hi.1.le
  have hdx1 : d*x ≤ 1 := by nlinarith [hL.2,hi.2]
  have he := one_sub_exp_neg_quartic hdx0 hdx1
  have hdx : d*x ≤ 6931471808/10^10*x :=
    mul_le_mul_of_nonneg_right (by linarith) hi.1.le
  have hsq := pow_le_pow_left₀ hdx0 hdx 2
  have hfour := pow_le_pow_left₀ hdx0 hdx 4
  have hgl : (6931471803/10^10-x^2/1000)*x < d*x :=
    mul_lt_mul_of_pos_right (by linarith) hi.1
  have hg0 : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hi.1.le
    linarith [hL.1]
  have hcube := pow_le_pow_left₀ hg0 hgl.le 3
  have hroot : scalarEnvelopeRoot p (73/200) = Real.exp (-(d*x)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d,a]
    simp only [one_div,hxdef]
    ring
  rw [hroot]
  dsimp [Glo]
  linarith

lemma codex66_envelope_lt {p : ℝ} (hp : 66 ≤ p) (hp' : p ≤ 70) :
    scalarEnvelope p (73/200) < cyclicConstant p := by
  have hi := codex66_inverse_bounds hp
  have hi' := codex66_inverse_lower hp hp'
  have ht := codex66_witness_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codex85Witness p by linarith [ht.1])
  have hn := codex66_numerator_lower hp
  have hd := codex66_denominator_upper hp
  have hg := codex66_envelope_deficit hp hp'
  have hc := (sub_pos.mp (envelope_certificate hi' hi.2))
  have hN0 := codex66_Nlo_pos hi' hi.2
  have hG0 := codex66_Glo_pos hi' hi.2
  have henvD : 0 < 2 * (1 - scalarEnvelopeRoot p (73/200)) := by linarith
  have hr : scalarEnvelope p (73/200) < cyclicRatio p (codex85Witness p) := by
    rw [scalarEnvelope, cyclicRatio, div_lt_div_iff₀ henvD hD]
    calc
      _ ≤ (1 - (73/200 : ℝ)) * Dup p⁻¹ :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ < Nlo p⁻¹ * (2 * Glo p⁻¹) := hc
      _ ≤ (3 * cyclicA p (codex85Witness p) -
          (3 : ℝ) ^ (1 / p) * |2 - codex85Witness p|) *
          (2 * (1 - scalarEnvelopeRoot p (73/200))) :=
        mul_le_mul hn (by linarith) (by linarith) (hN0.le.trans hn)
  exact hr.trans_le (codex85Aux_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)



end HlawkaSchatten.DiagonalConstruction

/- Solutions/Hlawka66_CyclicUpperBound.lean -/
set_option autoImplicit false

namespace HlawkaCodex66Scalars
open HlawkaSchatten.DiagonalConstruction

theorem cyclicA_lower {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    1 + (69 / 100 : ℝ) / p ≤ cyclicA p t := by
  have hlog : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have he := Real.add_one_le_exp (Real.log 2 * (1 / p))
  have hr : 1 + (69 / 100 : ℝ) / p ≤ (2 : ℝ) ^ (1 / p) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hm := mul_le_mul_of_nonneg_right hlog (one_div_nonneg.mpr hp.le)
    simp only [div_eq_mul_inv, one_mul] at he hm ⊢
    linarith
  exact hr.trans (Real.rpow_le_rpow (by norm_num)
    (by linarith [Real.rpow_nonneg ht p])
    (one_div_nonneg.mpr hp.le))

theorem cyclicB_upper {p t : ℝ} (hp : 66 ≤ p) (ht : t ∈ Set.Icc (1 / 2) 2) :
    cyclicB p t ≤ 2 + (1 / p) / 100 := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ 1 / p := by positivity
  have hx1 : 1 / p ≤ 1 := (div_le_iff₀ hp0).mpr (by linarith)
  have habs : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpow : (2 : ℝ) ^ p ≥ 400 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (9 : ℝ) ≤ p by linarith)
    norm_num at h
    linarith
  have htwo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have htail : 4 / (2 : ℝ) ^ p ≤ 1 / 100 := by
    rw [div_le_iff₀ htwo]
    linarith
  have hb : cyclicB p t ≤ (2 + (2 : ℝ) ^ p) ^ (1 / p) := by
    apply Real.rpow_le_rpow (by positivity) _ hx0
    have h := Real.rpow_le_rpow (abs_nonneg _) habs hp0.le
    simp only [Real.one_rpow] at h
    linarith
  have heq : (2 + (2 : ℝ) ^ p) ^ (1 / p) =
      2 * (1 + 2 / (2 : ℝ) ^ p) ^ (1 / p) := by
    rw [show 2 + (2 : ℝ) ^ p = (2 : ℝ) ^ p * (1 + 2 / (2 : ℝ) ^ p) by
      field_simp; ring,
      Real.mul_rpow htwo.le (by positivity), ← Real.rpow_mul (by norm_num),
      mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hconc := rpow_one_add_le_one_add_mul_self
    (s := 2 / (2 : ℝ) ^ p)
    (by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) htwo.le]) hx0 hx1
  rw [heq] at hb
  have hm := mul_le_mul_of_nonneg_left hconc (by norm_num : (0 : ℝ) ≤ 2)
  have ht0 := mul_le_mul_of_nonneg_right htail hx0
  have halg : 2 * (1 + (1/p) * (2 / (2 : ℝ) ^ p)) =
      2 + (4 / (2 : ℝ) ^ p) * (1/p) := by ring
  rw [halg] at hm
  nlinarith

theorem cyclicRatio_le_half_exponent {p t : ℝ} (hp : 66 ≤ p)
    (ht : t ∈ Set.Icc (1 / 2) 2) : cyclicRatio p t ≤ p / 2 := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hden := cyclic_denominator_pos (show 1 < p by linarith) ht0
  have hA := cyclicA_lower (t := t) hp0 ht0
  have hB := cyclicB_upper hp ht
  have htA : t ≤ cyclicA p t := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg ht0 p)
      (show t ^ p ≤ t ^ p + 2 by linarith) (one_div_nonneg.mpr hp0.le)
    rw [← Real.rpow_mul ht0, mul_one_div_cancel hp0.ne', Real.rpow_one] at h
    exact h
  have hthree : 1 ≤ (3 : ℝ) ^ (1/p) := Real.one_le_rpow (by norm_num) (by positivity)
  have hnum : 3 * cyclicA p t - (3 : ℝ) ^ (1/p) * |2-t| ≤ 4 * cyclicA p t - 2 := by
    have h := mul_le_mul_of_nonneg_right hthree (abs_nonneg (2-t))
    rw [abs_of_nonneg (by linarith [ht.2])] at h
    rw [abs_of_nonneg (by linarith [ht.2])]
    nlinarith
  have hx : 1 / p ≤ 1 / 66 := (one_div_le_one_div_of_le (by norm_num) hp)
  have hpx : p * (1/p) = 1 := mul_one_div_cancel hp0.ne'
  have hAl := mul_le_mul_of_nonneg_left hA (show 0 ≤ 3*p-4 by linarith)
  have hBu := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*p/2 by positivity)
  have hfinal : 4 * cyclicA p t - 2 ≤ (p/2) * (6 * cyclicA p t - 3 * cyclicB p t) := by
    simp only [div_eq_mul_inv, one_mul] at hAl hBu hpx hx ⊢
    nlinarith
  exact (div_le_iff₀ hden).mpr (hnum.trans hfinal)

theorem cyclicConstant_le_half_exponent {p : ℝ} (hp : 66 ≤ p) :
    cyclicConstant p ≤ p / 2 := by
  obtain ⟨t, ht, he⟩ := cyclic_maximum_attained (show 1 < p by linarith)
  rw [← he]
  exact cyclicRatio_le_half_exponent hp ht

end HlawkaCodex66Scalars

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution : ∀ p : ℝ, 66 ≤ p → p ≤ 70 →
    (23 / 50 : ℝ) * p < cyclicConstant p ∧
    scalarEnvelope p (73 / 200) < cyclicConstant p ∧
    cyclicConstant p ≤ p / 2 := by
  intro p hp hp'
  exact ⟨codex66_cyclicConstant_gt_linear hp hp',
    codex66_envelope_lt hp hp',
    HlawkaCodex66Scalars.cyclicConstant_le_half_exponent hp⟩
#print axioms solution
