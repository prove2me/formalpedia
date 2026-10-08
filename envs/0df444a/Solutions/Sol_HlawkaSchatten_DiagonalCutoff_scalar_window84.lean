-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.scalar_window84
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T05:24:51.984087+00:00
-- url     : https://prove2.me/submissions/caac4fb7-a536-4ca8-9c2b-0c3a2b788e3b

/- Modular cutoff84 dependency, preserving the original exact argument. -/
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos

set_option autoImplicit false
/- Local module: Solutions.Sol_Hlawka85_AnalyticScalarBounds -/
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


/- Local module: Solutions.Hlawka84_LogTangent -/

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


/- Local module: Solutions.Hlawka84_TaylorBounds -/

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


/- Local module: Solutions.Hlawka84_ScalarCertificates -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace HlawkaCodex84Scalar
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
    (1045427587432204629127531464247858108826973401223583516751283040558712838799090022421103359882336226703564491764592852936177191429573631987995348087/277555756156289135105907917022705078125000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^0*(1/84-x)^17 +
    (13400880121756417897619209438449906797165070391446942513068294352954116752872597384268658225606387875807619011740628895534231545308649456897139717961/222044604925031308084726333618164062500000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^1*(1/84-x)^16 +
    (402647256822404568118050513125396741024139701156970099722788543451074021883432468216613021385488118599665876852578270942615729197912502764843858640509/888178419700125232338905334472656250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^2*(1/84-x)^15 +
    (7528547314847442091196921797299940828132257195694911773525933149939005022593622557337785791716431964409197244821679523796505862410390555086851069017391/3552713678800500929355621337890625000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^3*(1/84-x)^14 +
    (49023588819705599815313511813208377182154499305409162321565579195830430527134625102141796650947158256526633926336733087907450468115044014493343084175371/7105427357601001858711242675781250000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^4*(1/84-x)^13 +
    (2357778224375550564214537769103488490117422866233989271579404854374820559877489959615936246029462079361113774080857396163246212032057407478688059112866769/142108547152020037174224853515625000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^5*(1/84-x)^12 +
    (3465673674407006217402639184692563873143349128610040876621458760320143596852250442965055377865570078185776212230155738901056543692815260660583702808134581/113686837721616029739379882812500000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^6*(1/84-x)^11 +
    (3970620527220786085295017666609681194087951292097243748836480887201847468947352509497955883154772855046076652787160565769720757954203863318095863336552091/90949470177292823791503906250000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^7*(1/84-x)^10 +
    (1433529346290351246620163969405644919441654900030677092560616613900724376612277691891633997699371177232587885159394490818242300012284479866102307153074051/29103830456733703613281250000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^8*(1/84-x)^9 +
    (1022865738832646692301137691963379048336171165274884911129419740291776877538749799832843002447079707277227095322325204260881585758492198417147128636682157/23283064365386962890625000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^9*(1/84-x)^8 +
    (2875921146845442497813652914328765497207014454995227061264823251237221595867767681974844350445562706958609503206596221069784596212310136465199674382404697/93132257461547851562500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^10*(1/84-x)^7 +
    (1261571812038691764322670373059776691089117924398110593594160278515031551042433449685943689574594736391008226807678269617122324685613930418577385136005543/74505805969238281250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^11*(1/84-x)^6 +
    (158811117910855253188941867041685077907940730025201960024264802512554616204613106968595348673463610272298574819244282993991612384965619090883642981011333/22351741790771484375000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^12*(1/84-x)^5 +
    (35540816130940064184248527333470093940430209841170868486539274945230635224265093386385709776337903150867747358780129070216489858379907670158394794238559/16093254089355468750000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^13*(1/84-x)^4 +
    (21500643341405377368518080452214690825184048638045496131230399907758913065652685495852282549868475792938966236138157338488317311217629890375165616101/44703483581542968750000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^14*(1/84-x)^3 +
    (7885056994081371023302372759808429988559541539506152411678102836738184281470336546069678680534073471454266626264274409982793709106665981395959953657/119209289550781250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^15*(1/84-x)^2 +
    (53723418176282873585069101791242704809041426147402228412407529393554216115257740083272326078598520007935564621045481229817569660451759764556442331/11920928955078125000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^16*(1/84-x)^1 +
    (207488024885149610824918438014815344886026133666941390623188280122251120826129462409511132282916154529421145221537724317708727956879202761641263/4768371582031250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/85)^17*(1/84-x)^0

theorem envelope_identity (x : ℝ) : Nlo x*(2*Glo x)-(1-17867/50000)*Dup x = envelopeBernstein x := by
  dsimp [Nlo, Dup, Glo, envelopeBernstein]
  ring

theorem envelope_certificate {x : ℝ} (hlo : 1/85 ≤ x) (hhi : x ≤ 1/84) :
    0 < Nlo x*(2*Glo x)-(1-17867/50000)*Dup x := by
  rw [envelope_identity]
  unfold envelopeBernstein
  by_cases ht : x < 1/84
  · have hl : 0 ≤ x-1/85 := by linarith
    have hr : 0 < 1/84-x := by linarith
    positivity
  · have he : x = 1/84 := by linarith
    rw [he]
    norm_num

noncomputable def linearBernstein (x : ℝ) : ℝ :=
    (5407245126552880185255752869763722475578995914133313713288928533667456741748737424583451059006751144024263/4547473508864641189575195312500000000000000000000 : ℝ)*(x-1/85)^0*(1/84-x)^16 +
    (14636238843171992389663700739933181734610135768035475012399761673261739855839273654167005227394519289198665337/782165443524718284606933593750000000000000000000000 : ℝ)*(x-1/85)^1*(1/84-x)^15 +
    (53967513465612536678610753412543893825101997976582994561978502010133180928720438327128475255684267644602214613/391082721762359142303466796875000000000000000000000 : ℝ)*(x-1/85)^2*(1/84-x)^14 +
    (396088919519889707421002583957256436466440756727841191916227803778354053235814093064328395424615603819102743751/625732354819774627685546875000000000000000000000000 : ℝ)*(x-1/85)^3*(1/84-x)^13 +
    (10119437764376287032251709980032434725422914608055202728474306051748509729086623137387720542084008664357081369619/5005858838558197021484375000000000000000000000000000 : ℝ)*(x-1/85)^4*(1/84-x)^12 +
    (477133001171343542631991809362694154405963716809531240452111296638763602271840251824733100211514741504698903190043/100117176771163940429687500000000000000000000000000000 : ℝ)*(x-1/85)^5*(1/84-x)^11 +
    (1717902770137789669216715390824315285692621136279326635828618317007244970051002802534863777658194327020549872872597/200234353542327880859375000000000000000000000000000000 : ℝ)*(x-1/85)^6*(1/84-x)^10 +
    (9635807686739473857577071989081808150261232028074389235363232831912216959432826561172356372819848872737422335366519/800937414169311523437500000000000000000000000000000000 : ℝ)*(x-1/85)^7*(1/84-x)^9 +
    (34037041313971656421186179558556365375510236691153471969950604181039637841223991943540114517215676315067001875771193/2562999725341796875000000000000000000000000000000000000 : ℝ)*(x-1/85)^8*(1/84-x)^8 +
    (23739815165671959276670142164849238368770219562856861852283220210960013738535268210518301901616821799091505477255169/2050399780273437500000000000000000000000000000000000000 : ℝ)*(x-1/85)^9*(1/84-x)^7 +
    (3258466174364572924829218800208904185153297361127999112100578417374925593878241771425212898210685977736705661414443/410079956054687500000000000000000000000000000000000000 : ℝ)*(x-1/85)^10*(1/84-x)^6 +
    (348354841449341098995207162293136049820492439542647168747197166424733485757617562188755467385002112450081763256861/82015991210937500000000000000000000000000000000000000 : ℝ)*(x-1/85)^11*(1/84-x)^5 +
    (28435761293194093625252706591718625551609170904504875719163739833035939205332103743388312451074488858757205824663/16403198242187500000000000000000000000000000000000000 : ℝ)*(x-1/85)^12*(1/84-x)^4 +
    (1713291895695489063738488143392010941346547456639861721919860370006689588139573627547786770601185280718553996371/3280639648437500000000000000000000000000000000000000 : ℝ)*(x-1/85)^13*(1/84-x)^3 +
    (71855647060757024337572642188743642340488494964650250154587547304368309348829287270965013459900955300182708017/656127929687500000000000000000000000000000000000000 : ℝ)*(x-1/85)^14*(1/84-x)^2 +
    (1874185841266006270812419076103747545069157497985239150352753198865780445909578378876166062695794785755161999/131225585937500000000000000000000000000000000000000 : ℝ)*(x-1/85)^15*(1/84-x)^1 +
    (22901920514982867639155384471074014206526914382185830962951361755517920459695947343279908268351215774019433/26245117187500000000000000000000000000000000000000 : ℝ)*(x-1/85)^16*(1/84-x)^0

theorem linear_identity (x : ℝ) : x*Nlo x-(20/43)*Dup x = linearBernstein x := by
  dsimp [Nlo, Dup, Glo, linearBernstein]
  ring

theorem linear_certificate {x : ℝ} (hlo : 1/85 ≤ x) (hhi : x ≤ 1/84) :
    0 < x*Nlo x-(20/43)*Dup x := by
  rw [linear_identity]
  unfold linearBernstein
  by_cases ht : x < 1/84
  · have hl : 0 ≤ x-1/85 := by linarith
    have hr : 0 < 1/84-x := by linarith
    positivity
  · have he : x = 1/84 := by linarith
    rw [he]
    norm_num

end HlawkaCodex84Scalar


/- Local module: Solutions.Hlawka84_WitnessBounds -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction
open HlawkaCodex84Scalar

lemma codex84_inverse_bounds {p : ℝ} (hp : 84 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1/84 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩
lemma codex84_inverse_lower {p : ℝ} (hp : 84 ≤ p) (hhi : p ≤ 85) : 1/85 ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hhi
lemma codex84_scaled {p : ℝ} (hp : 84 ≤ p) :
    0 ≤ (Real.log p-Real.log (3/4))*p⁻¹ ∧
    (Real.log p-Real.log (3/4))*p⁻¹ ≤ (371849888/10^8 : ℝ)*p⁻¹+1/84 ∧
    (371849888/10^8 : ℝ)*p⁻¹+1/84 <1/17 := by
  have hi := codex84_inverse_bounds hp
  have h0 : 0 ≤ Real.log p-Real.log (3/4) := by
    linarith [Real.log_nonneg (show 1 ≤ p by linarith), codex85_log_three_quarters.2]
  exact ⟨mul_nonneg h0 hi.1.le, witness_scaled_tangent (by linarith), by linarith [hi.2]⟩
lemma codex84_witness_bounds {p : ℝ} (hp : 84 ≤ p) :
    1/2 ≤ codex85Witness p ∧ codex85Witness p ≤ 1 := by
  have hl := codex84_scaled hp
  have h := Real.add_one_le_exp (-((Real.log p-Real.log (3/4))*p⁻¹))
  exact ⟨by dsimp [codex85Witness]; linarith [hl.2.1,hl.2.2],
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)⟩
lemma codex84_cyclicA_exp {p : ℝ} (hp : 84 ≤ p) :
    cyclicA p (codex85Witness p) = Real.exp (Real.log (2+3/4*p⁻¹)*p⁻¹) := by
  rw [cyclicA, codex85_witness_power (by linarith), add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]

lemma codex84_numerator_lower {p : ℝ} (hp : 84 ≤ p) :
    Nlo p⁻¹ ≤ 3*cyclicA p (codex85Witness p)-(3 : ℝ)^(1/p)*|2-codex85Witness p| := by
  set x := p⁻¹ with hxdef
  have hi := codex84_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ht := codex84_witness_bounds hp
  have hl := codex84_scaled hp
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
  rw [← codex84_cyclicA_exp hp] at hA
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

lemma codex84_denominator_upper {p : ℝ} (hp : 84 ≤ p) :
    6*cyclicA p (codex85Witness p)-3*cyclicB p (codex85Witness p) ≤ Dup p⁻¹ := by
  set x := p⁻¹ with hxdef
  have hi := codex84_inverse_bounds hp
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
  rw [← codex84_cyclicA_exp hp] at hE
  have hB := codex85Aux_cyclicB_ge_two (t := codex85Witness p) (show 0 < p by linarith)
  dsimp [Dup,T] at hE ⊢
  linarith

end HlawkaSchatten.DiagonalConstruction


/- Local module: Solutions.Hlawka84_ScalarBounds -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction
open HlawkaCodex84Scalar

lemma codex84_cyclicConstant_gt_linear {p : ℝ} (hp : 84 ≤ p) (hp' : p ≤ 85) :
    (20 / 43 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := codex84_inverse_bounds hp
  have hi' := codex84_inverse_lower hp hp'
  have ht := codex84_witness_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codex85Witness p by linarith [ht.1])
  have hn := codex84_numerator_lower hp
  have hd := codex84_denominator_upper hp
  have hc := (sub_pos.mp (linear_certificate hi' hi.2))
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hr : (20 / 43 : ℝ) * p < cyclicRatio p (codex85Witness p) := by
    rw [cyclicRatio, lt_div_iff₀ hD]
    have hcp := mul_lt_mul_of_pos_left hc hp0
    have hdp := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 20 / 43 * p by positivity)
    have : p * (p⁻¹ * Nlo p⁻¹) = Nlo p⁻¹ := by
      rw [← mul_assoc, hpi, one_mul]
    nlinarith
  exact hr.trans_le (codex85Aux_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)


lemma codex84_power_tail {p : ℝ} (hp : 84 ≤ p) (hp' : p ≤ 85) :
    (17867 / 50000 : ℝ) ^ p < (p⁻¹) ^ 2 / 1000 := by
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
    (17867 / 50000 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ p :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hp0.le
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, Real.inv_rpow (by norm_num)]
    _ < (1000 * p ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) htwo
    _ = (p⁻¹) ^ 2 / 1000 := by field_simp


lemma codex84_Dup_pos {x : ℝ} (hx : 0 < x) (hhi : x ≤ 1/84) : 0 < Dup x := by
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have h : 0 < 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 := by
    nlinarith [pow_nonneg hx.le 3]
  dsimp [Dup]
  positivity

lemma codex84_Nlo_pos {x : ℝ} (hlo : 1/85 ≤ x) (hhi : x ≤ 1/84) : 0 < Nlo x := by
  have hx : 0 < x := by linarith
  have hc := sub_pos.mp (linear_certificate hlo hhi)
  have hd := codex84_Dup_pos hx hhi
  nlinarith

lemma codex84_Glo_pos {x : ℝ} (hlo : 1/85 ≤ x) (hhi : x ≤ 1/84) : 0 < Glo x := by
  have hx : 0 < x := by linarith
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have hx4 := pow_le_pow_left₀ hx.le hhi 4
  have hg : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hx.le
    nlinarith
  dsimp [Glo]
  nlinarith [pow_nonneg hg 3]

lemma codex84_envelope_deficit {p : ℝ} (hp : 84 ≤ p) (hp' : p ≤ 85) :
    Glo p⁻¹ < 1-scalarEnvelopeRoot p (17867/50000) := by
  have hi := codex84_inverse_bounds hp
  set x := p⁻¹ with hxdef
  let a := (17867/50000 : ℝ)^p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a < x^2/1000 := codex84_power_tail hp hp'
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
  have hroot : scalarEnvelopeRoot p (17867/50000) = Real.exp (-(d*x)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d,a]
    simp only [one_div,hxdef]
    ring
  rw [hroot]
  dsimp [Glo]
  linarith

lemma codex84_envelope_lt {p : ℝ} (hp : 84 ≤ p) (hp' : p ≤ 85) :
    scalarEnvelope p (17867 / 50000) < cyclicConstant p := by
  have hi := codex84_inverse_bounds hp
  have hi' := codex84_inverse_lower hp hp'
  have ht := codex84_witness_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codex85Witness p by linarith [ht.1])
  have hn := codex84_numerator_lower hp
  have hd := codex84_denominator_upper hp
  have hg := codex84_envelope_deficit hp hp'
  have hc := (sub_pos.mp (envelope_certificate hi' hi.2))
  have hN0 := codex84_Nlo_pos hi' hi.2
  have hG0 := codex84_Glo_pos hi' hi.2
  have henvD : 0 < 2 * (1 - scalarEnvelopeRoot p (17867 / 50000)) := by linarith
  have hr : scalarEnvelope p (17867 / 50000) < cyclicRatio p (codex85Witness p) := by
    rw [scalarEnvelope, cyclicRatio, div_lt_div_iff₀ henvD hD]
    calc
      _ ≤ (1 - (17867 / 50000 : ℝ)) * Dup p⁻¹ :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ < Nlo p⁻¹ * (2 * Glo p⁻¹) := hc
      _ ≤ (3 * cyclicA p (codex85Witness p) -
          (3 : ℝ) ^ (1 / p) * |2 - codex85Witness p|) *
          (2 * (1 - scalarEnvelopeRoot p (17867 / 50000))) :=
        mul_le_mul hn (by linarith) (by linarith) (hN0.le.trans hn)
  exact hr.trans_le (codex85Aux_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)



end HlawkaSchatten.DiagonalConstruction

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution : ∀ p : ℝ, 84 ≤ p → p ≤ 85 →
    (20/43 : ℝ)*p < cyclicConstant p ∧
    scalarEnvelope p (17867/50000) < cyclicConstant p := by
  intro p hp hp'
  exact ⟨codex84_cyclicConstant_gt_linear hp hp', codex84_envelope_lt hp hp'⟩
