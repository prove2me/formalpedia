-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.scalar_window80
-- status  : ACCEPTED   (prove)
-- author  : @sorry_not_sorry
-- created : 2026-10-06T18:04:10.285133+00:00
-- url     : https://prove2.me/submissions/d1480c2c-675f-40f6-bc30-69e1b68992f1

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


/- Local module: Solutions.Hlawka80_LogTangent -/

set_option autoImplicit false

namespace HlawkaCodex80Scalar

theorem log_three_twenty_thirds : Real.log (320/3 : ℝ) < 46697087089/10^10 := by
  have he : Real.log (320/3 : ℝ) = 6*Real.log 2+Real.log 5-Real.log 3 := by
    rw [show (320/3 : ℝ) = 2^6*5/3 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    ring
  rw [he]
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9, Real.log_three_gt_d9]

/-- Tangent at 80 for `log p - log (3/4)`. -/
theorem witness_log_tangent {p : ℝ} (hp : 0 < p) :
    Real.log p-Real.log (3/4 : ℝ) ≤ 46697087089/10^10+(p-80)/80 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < p/80 by positivity)
  rw [Real.log_div hp.ne' (by norm_num)] at h
  have he : Real.log (80 : ℝ)-Real.log (3/4 : ℝ) = Real.log (320/3 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have h2 : (p-80)/80 = p/80-1 := by ring
  rw [h2]
  linarith [h, he, log_three_twenty_thirds]

theorem witness_scaled_tangent {p : ℝ} (hp : 0 < p) :
    (Real.log p-Real.log (3/4 : ℝ))*p⁻¹ ≤
      (36697087089/10^10 : ℝ)*p⁻¹+1/80 := by
  have h := mul_le_mul_of_nonneg_right (witness_log_tangent hp) (inv_nonneg.mpr hp.le)
  have he : (46697087089/10^10+(p-80)/80)*p⁻¹ =
      (36697087089/10^10 : ℝ)*p⁻¹+1/80 := by
    field_simp
    ring
  rwa [he] at h

end HlawkaCodex80Scalar


/- Local module: Solutions.Hlawka80_TaylorBounds -/

set_option autoImplicit false

namespace HlawkaCodex80Scalar

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

end HlawkaCodex80Scalar

/- Local module: Solutions.Hlawka80_ScalarCertificates -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace HlawkaCodex80Scalar

noncomputable def Nlo (x : ℝ) : ℝ :=
  let z := (36697087089/10^10 : ℝ)*x+1/80
  let y := (6931471803/10^10+3/8*x-9/64*x^2)*x
  let c := (1098612289/10^9 : ℝ)*x
  3*(1+y+y^2/2)-(1+c+c^2/2+c^3/6+c^4/12)*(1+z-z^2/2+z^3/6+z^4/12)
noncomputable def Dup (x : ℝ) : ℝ :=
  let t := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  6*(t+t^2/2+t^3/6+t^4/12)
noncomputable def Glo (x : ℝ) : ℝ :=
  let g := (6931471803/10^10-x^2/1000)*x
  g-(6931471808/10^10*x)^2/2+g^3/6-(6931471808/10^10*x)^4/12

noncomputable def envelopeBernstein80 (x : ℝ) : ℝ :=
    (26186023962151318843233229029799997973203828427778316885342289391382421498065295015998044355852210896691041306635713172801499976367912868239/29103830456733703613281250000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^0*(1/80-x)^17 +
    (8737958546523786336480446433953388776511283803037830223079516047990293348872954216161077723610305429309284275716415384591686722758657917510753/582076609134674072265625000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^1*(1/80-x)^16 +
    (1371437437752804033156419943853663345896618585206236934055803238219929940408691474107195235483557313894994492743076472939031618848397231552965009/11641532182693481445312500000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^2*(1/80-x)^15 +
    (26892238658699462209698394882926826727455642185023055409503029884196974663246241288080042572737634693019005832322477684401695878604028598836078131/46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^3*(1/80-x)^14 +
    (922317810016410694208197177816200383949008626910505746338068850699836045063832790436386607864824236053205953124052062798044574904001239815284735183/465661287307739257812500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^4*(1/80-x)^13 +
    (234851393460389975569081250723370857949425208083090024493726541301748001620752267932467589185126481981899552757560625274901101251459723547834265935169/46566128730773925781250000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^5*(1/80-x)^12 +
    (9194626548826137144701731770143920005079569322846588896491096283524256725533895470999975248987919626438005204830948189381819193873778428498099928658353/931322574615478515625000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^6*(1/80-x)^11 +
    (282662844818789980130433374412983613528326187537845280601734139561628952228488722308729884865547530185448435061881970943823155732970995842590798483128079/18626451492309570312500000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^7*(1/80-x)^10 +
    (2763083587079105606681641931342736344058454606363659645026600803504010381312461894794877816702335917289821702255448609851781309770768484121865999696202831/149011611938476562500000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^8*(1/80-x)^9 +
    (53982104626841582029792616979921282230967288731788917369630662134035807564012154219710428844919247966704012297532229295228157366293372801009959895321047921/2980232238769531250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^9*(1/80-x)^8 +
    (4215509477032025228141984574372806520148575093276402654107248820581987545108997438798743223620342217283987550013659896418662620689604426410366458387737997949/298023223876953125000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^10*(1/80-x)^7 +
    (52331454349115214046432014419796674381369741171070620250471451216446277489264633533933404530006127452755888998304032833141583494112279095562547059820602487603/5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^11*(1/80-x)^6 +
    (15938170296257044368224977427972956878862962670307166173084079078082969496056485722354039057340151462583131361280931470400396510721109471429811209719885150457/3725290298461914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^12*(1/80-x)^5 +
    (19101542866643031125666371251753686981250006474832210481586291084675792451404858997644582131908538327084649272923399131790779815877056419321214168406761110947/11920928955078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^13*(1/80-x)^4 +
    (2654783226515252157690486326100253182820266637143979465149398718077631929095325269767244130669896818377183248443301130585439845728007152428733159614543078717/5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^14*(1/80-x)^3 +
    (2064231895094844871078534085031909141629225394804167469058897076618860620193492178500366264224842357671044727886115500364204734302148764797744696338045349753/23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^15*(1/80-x)^2 +
    (62632795306296493077999866736478653359805999445934349760482715705191202191426820816347689239376603990103011801623380624192182093629743735557281557014994159/5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^16*(1/80-x)^1 +
    (142932300220688037476218090691053571912054647135595032604562585828923832085287901698022582614225078984925404861523667901462694150729829268423059364903949773/238418579101562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^17*(1/80-x)^0

noncomputable def linearBernstein80 (x : ℝ) : ℝ :=
    (16498380864264171793384025303734254383574471182457313737215695044910256056516140386216450933010512331/14901161193847656250000000000000000000000000000000000 : ℝ)*(x-1/84)^0*(1/80-x)^16 +
    (5259584490641222171726431755299078429120017867790154970009709484073246567189012993484908194250458556899/298023223876953125000000000000000000000000000000000000 : ℝ)*(x-1/84)^1*(1/80-x)^15 +
    (49119811287670068762378688757870221315050665547196734162041659241790521632016976101180792026408834601601/372529029846191406250000000000000000000000000000000000 : ℝ)*(x-1/84)^2*(1/80-x)^14 +
    (18266738134620195038923267586409543936692517076554036105656062129617645224708731363447884366250476937832571/29802322387695312500000000000000000000000000000000000000 : ℝ)*(x-1/84)^3*(1/80-x)^13 +
    (2365294302160015870812889542171601597839745592020729334813595016505423085358601555607263732419352249511582573/1192092895507812500000000000000000000000000000000000000000 : ℝ)*(x-1/84)^4*(1/80-x)^12 +
    (113078554481813376358860087567412055847309491611870938873980198448569980065314770558161283462049497936108559973/23841857910156250000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^5*(1/80-x)^11 +
    (2064658390105347642747142008571191546754175282516187700489441750125374451273010302045064805080723418811319800381/238418579101562500000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^6*(1/80-x)^10 +
    (58746104812053365131061917382822032188685170374533186348429265135357657115971396417265972088299462538282902424179/4768371582031250000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^7*(1/80-x)^9 +
    (5264929737818037146106716697045593340782873503119967765715900244606747301553847041749208802541604686408002531707859/381469726562500000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^8*(1/80-x)^8 +
    (93199333531124319445339324933404959574890135493845256198640357338953458849664431649713212520742711317082264131699371/7629394531250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^9*(1/80-x)^7 +
    (64956861204607422645439225271149292694420354066788663219212847777933127089117949175863247841201302300722861706352157/7629394531250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^10*(1/80-x)^6 +
    (35275150419730492966907490803100256312033262181286488432702761623776079599917906259941066773681452992760797405205831/7629394531250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^11*(1/80-x)^5 +
    (2926467156572353499941758975759481253848357327151597527271415696962218735432273991282127688834083122995063409637717/1525878906250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^12*(1/80-x)^4 +
    (896368762348049539406772621857786809039136340807336637085876126232918147132273020402245423571830285507723883609133/1525878906250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^13*(1/80-x)^3 +
    (955974673885895959319796300759001681429589918130263484346103004524931513013307441145645419925335226044875252737591/7629394531250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^14*(1/80-x)^2 +
    (126867748073394818607753679667048516723380010684190218386496037825844304944587594957088434305851410379429954720557/7629394531250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^15*(1/80-x)^1 +
    (7891628472263358058365612094166223622716861738726769407311296953185398107401163038995954810500400016519354890311/7629394531250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/84)^16*(1/80-x)^0

theorem envelope_identity (x : ℝ) : Nlo x*(2*Glo x)-(1-9/25)*Dup x = envelopeBernstein80 x := by
  dsimp [Nlo, Dup, Glo, envelopeBernstein80]
  ring

theorem envelope_certificate {x : ℝ} (hlo : 1/84 ≤ x) (hhi : x ≤ 1/80) :
    0 < Nlo x*(2*Glo x)-(1-9/25)*Dup x := by
  rw [envelope_identity]
  unfold envelopeBernstein80
  by_cases ht : x < 1/80
  · have hl : 0 ≤ x-1/84 := by linarith
    have hr : 0 < 1/80-x := by linarith
    positivity
  · have he : x = 1/80 := by linarith
    rw [he]
    norm_num

theorem linear_identity (x : ℝ) : x*Nlo x-(23/50)*Dup x = linearBernstein80 x := by
  dsimp [Nlo, Dup, Glo, linearBernstein80]
  ring

theorem linear_certificate {x : ℝ} (hlo : 1/84 ≤ x) (hhi : x ≤ 1/80) :
    0 < x*Nlo x-(23/50)*Dup x := by
  rw [linear_identity]
  unfold linearBernstein80
  by_cases ht : x < 1/80
  · have hl : 0 ≤ x-1/84 := by linarith
    have hr : 0 < 1/80-x := by linarith
    positivity
  · have he : x = 1/80 := by linarith
    rw [he]
    norm_num

end HlawkaCodex80Scalar


/- Local module: Solutions.Hlawka80_WitnessBounds -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction
open HlawkaCodex80Scalar

lemma codex80_inverse_bounds {p : ℝ} (hp : 80 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1/80 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩
lemma codex80_inverse_lower {p : ℝ} (hp : 80 ≤ p) (hhi : p ≤ 84) : 1/84 ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hhi
lemma codex80_scaled {p : ℝ} (hp : 80 ≤ p) :
    0 ≤ (Real.log p-Real.log (3/4))*p⁻¹ ∧
    (Real.log p-Real.log (3/4))*p⁻¹ ≤ (36697087089/10^10 : ℝ)*p⁻¹+1/80 ∧
    (36697087089/10^10 : ℝ)*p⁻¹+1/80 <1/17 := by
  have hi := codex80_inverse_bounds hp
  have h0 : 0 ≤ Real.log p-Real.log (3/4) := by
    linarith [Real.log_nonneg (show 1 ≤ p by linarith), codex85_log_three_quarters.2]
  exact ⟨mul_nonneg h0 hi.1.le, witness_scaled_tangent (by linarith), by linarith [hi.2]⟩
lemma codex80_witness_bounds {p : ℝ} (hp : 80 ≤ p) :
    1/2 ≤ codex85Witness p ∧ codex85Witness p ≤ 1 := by
  have hl := codex80_scaled hp
  have h := Real.add_one_le_exp (-((Real.log p-Real.log (3/4))*p⁻¹))
  exact ⟨by dsimp [codex85Witness]; linarith [hl.2.1,hl.2.2],
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)⟩
lemma codex80_cyclicA_exp {p : ℝ} (hp : 80 ≤ p) :
    cyclicA p (codex85Witness p) = Real.exp (Real.log (2+3/4*p⁻¹)*p⁻¹) := by
  rw [cyclicA, codex85_witness_power (by linarith), add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]

lemma codex80_numerator_lower {p : ℝ} (hp : 80 ≤ p) :
    Nlo p⁻¹ ≤ 3*cyclicA p (codex85Witness p)-(3 : ℝ)^(1/p)*|2-codex85Witness p| := by
  set x := p⁻¹ with hxdef
  have hi := codex80_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ht := codex80_witness_bounds hp
  have hl := codex80_scaled hp
  let C : ℝ := 1098612289/10^9*x
  let Z : ℝ := 36697087089/10^10*x+1/80
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
  rw [← codex80_cyclicA_exp hp] at hA
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

lemma codex80_denominator_upper {p : ℝ} (hp : 80 ≤ p) :
    6*cyclicA p (codex85Witness p)-3*cyclicB p (codex85Witness p) ≤ Dup p⁻¹ := by
  set x := p⁻¹ with hxdef
  have hi := codex80_inverse_bounds hp
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
  rw [← codex80_cyclicA_exp hp] at hE
  have hB := codex85Aux_cyclicB_ge_two (t := codex85Witness p) (show 0 < p by linarith)
  dsimp [Dup,T] at hE ⊢
  linarith

end HlawkaSchatten.DiagonalConstruction


/- Local module: Solutions.Hlawka80_ScalarBounds -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction
open HlawkaCodex80Scalar

lemma codex80_cyclicConstant_gt_linear {p : ℝ} (hp : 80 ≤ p) (hp' : p ≤ 84) :
    (23 / 50 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := codex80_inverse_bounds hp
  have hi' := codex80_inverse_lower hp hp'
  have ht := codex80_witness_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codex85Witness p by linarith [ht.1])
  have hn := codex80_numerator_lower hp
  have hd := codex80_denominator_upper hp
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


lemma codex80_power_tail {p : ℝ} (hp : 80 ≤ p) (hp' : p ≤ 84) :
    (9 / 25 : ℝ) ^ p < (p⁻¹) ^ 2 / 1000 := by
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
    (9 / 25 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ p :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hp0.le
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, Real.inv_rpow (by norm_num)]
    _ < (1000 * p ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) htwo
    _ = (p⁻¹) ^ 2 / 1000 := by field_simp


lemma codex80_Dup_pos {x : ℝ} (hx : 0 < x) (hhi : x ≤ 1/80) : 0 < Dup x := by
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have h : 0 < 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 := by
    nlinarith [pow_nonneg hx.le 3]
  dsimp [Dup]
  positivity

lemma codex80_Nlo_pos {x : ℝ} (hlo : 1/84 ≤ x) (hhi : x ≤ 1/80) : 0 < Nlo x := by
  have hx : 0 < x := by linarith
  have hc := sub_pos.mp (linear_certificate hlo hhi)
  have hd := codex80_Dup_pos hx hhi
  nlinarith

lemma codex80_Glo_pos {x : ℝ} (hlo : 1/84 ≤ x) (hhi : x ≤ 1/80) : 0 < Glo x := by
  have hx : 0 < x := by linarith
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have hx4 := pow_le_pow_left₀ hx.le hhi 4
  have hg : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hx.le
    nlinarith
  dsimp [Glo]
  nlinarith [pow_nonneg hg 3]

lemma codex80_envelope_deficit {p : ℝ} (hp : 80 ≤ p) (hp' : p ≤ 84) :
    Glo p⁻¹ < 1-scalarEnvelopeRoot p (9/25) := by
  have hi := codex80_inverse_bounds hp
  set x := p⁻¹ with hxdef
  let a := (9/25 : ℝ)^p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a < x^2/1000 := codex80_power_tail hp hp'
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
  have hroot : scalarEnvelopeRoot p (9/25) = Real.exp (-(d*x)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d,a]
    simp only [one_div,hxdef]
    ring
  rw [hroot]
  dsimp [Glo]
  linarith

lemma codex80_envelope_lt {p : ℝ} (hp : 80 ≤ p) (hp' : p ≤ 84) :
    scalarEnvelope p (9 / 25) < cyclicConstant p := by
  have hi := codex80_inverse_bounds hp
  have hi' := codex80_inverse_lower hp hp'
  have ht := codex80_witness_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codex85Witness p by linarith [ht.1])
  have hn := codex80_numerator_lower hp
  have hd := codex80_denominator_upper hp
  have hg := codex80_envelope_deficit hp hp'
  have hc := (sub_pos.mp (envelope_certificate hi' hi.2))
  have hN0 := codex80_Nlo_pos hi' hi.2
  have hG0 := codex80_Glo_pos hi' hi.2
  have henvD : 0 < 2 * (1 - scalarEnvelopeRoot p (9 / 25)) := by linarith
  have hr : scalarEnvelope p (9 / 25) < cyclicRatio p (codex85Witness p) := by
    rw [scalarEnvelope, cyclicRatio, div_lt_div_iff₀ henvD hD]
    calc
      _ ≤ (1 - (9 / 25 : ℝ)) * Dup p⁻¹ :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ < Nlo p⁻¹ * (2 * Glo p⁻¹) := hc
      _ ≤ (3 * cyclicA p (codex85Witness p) -
          (3 : ℝ) ^ (1 / p) * |2 - codex85Witness p|) *
          (2 * (1 - scalarEnvelopeRoot p (9 / 25))) :=
        mul_le_mul hn (by linarith) (by linarith) (hN0.le.trans hn)
  exact hr.trans_le (codex85Aux_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)



end HlawkaSchatten.DiagonalConstruction

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
theorem solution : ∀ p : ℝ, 80 ≤ p → p ≤ 84 →
    (23/50 : ℝ)*p < cyclicConstant p ∧
    scalarEnvelope p (9/25) < cyclicConstant p := by
  intro p hp hp'
  exact ⟨codex80_cyclicConstant_gt_linear hp hp', codex80_envelope_lt hp hp'⟩
