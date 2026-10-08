-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.scalar_window79
-- status  : ACCEPTED   (prove)
-- author  : @sorry_not_sorry
-- created : 2026-10-07T23:19:42.382665+00:00
-- url     : https://prove2.me/submissions/45876f57-dc24-407f-9547-b8b94c730413

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
These are new supporting bounds for the window [79,80], not a cutoff proof.
-/

set_option autoImplicit false

namespace HlawkaSchatten.DiagonalConstruction

/-! Analytic scalar estimates on 79 ≤ p ≤ 80. These extend the
cutoff-79 witness estimates with q0 = 9/25. -/



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


/- Local module: Solutions.Hlawka79_LogTangent -/

set_option autoImplicit false

namespace HlawkaCodex79Scalar

theorem log_three_twenty_thirds : Real.log (320/3 : ℝ) < 46697087089/10^10 := by
  have he : Real.log (320/3 : ℝ) = 6*Real.log 2+Real.log 5-Real.log 3 := by
    rw [show (320/3 : ℝ) = 2^6*5/3 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    ring
  rw [he]
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9, Real.log_three_gt_d9]

/-- Tangent at 79 for `log p - log (3/4)`. -/
theorem witness_log_tangent {p : ℝ} (hp : 0 < p) :
    Real.log p-Real.log (3/4 : ℝ) ≤ 46697087089/10^10+(p-79)/79 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < p/79 by positivity)
  rw [Real.log_div hp.ne' (by norm_num)] at h
  have he : Real.log (79 : ℝ)-Real.log (3/4 : ℝ) = Real.log (316/3 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have hB : Real.log (316/3 : ℝ) < 46697087089/10^10 := by
    have hle : Real.log (316/3 : ℝ) < Real.log (320/3 : ℝ) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    linarith [hle, log_three_twenty_thirds]
  have h2 : (p-79)/79 = p/79-1 := by ring
  rw [h2]
  linarith [h, he, hB]

theorem witness_scaled_tangent {p : ℝ} (hp : 0 < p) :
    (Real.log p-Real.log (3/4 : ℝ))*p⁻¹ ≤
      (36697087089/10^10 : ℝ)*p⁻¹+1/79 := by
  have h := mul_le_mul_of_nonneg_right (witness_log_tangent hp) (inv_nonneg.mpr hp.le)
  have he : (46697087089/10^10+(p-79)/79)*p⁻¹ =
      (36697087089/10^10 : ℝ)*p⁻¹+1/79 := by
    field_simp
    ring
  rwa [he] at h

end HlawkaCodex79Scalar


/- Local module: Solutions.Hlawka79_TaylorBounds -/

set_option autoImplicit false

namespace HlawkaCodex79Scalar

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

end HlawkaCodex79Scalar

/- Local module: Solutions.Hlawka79_ScalarCertificates -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
namespace HlawkaCodex79Scalar

noncomputable def Nlo (x : ℝ) : ℝ :=
  let z := (36697087089/10^10 : ℝ)*x+1/79
  let y := (6931471803/10^10+3/8*x-9/64*x^2)*x
  let c := (1098612289/10^9 : ℝ)*x
  3*(1+y+y^2/2)-(1+c+c^2/2+c^3/6+c^4/12)*(1+z-z^2/2+z^3/6+z^4/12)
noncomputable def Dup (x : ℝ) : ℝ :=
  let t := (6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3)*x
  6*(t+t^2/2+t^3/6+t^4/12)
noncomputable def Glo (x : ℝ) : ℝ :=
  let g := (6931471803/10^10-x^2/1000)*x
  g-(6931471808/10^10*x)^2/2+g^3/6-(6931471808/10^10*x)^4/12

noncomputable def envelopeBernstein79 (x : ℝ) : ℝ :=
    (7556453648867490409710519048374443923122924272629302803728151742384690442716735774974056736875451998974855611634916659977894249074295893281943613428220556023500280943/2145767211914062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^0*(1/79-x)^17 +
    (707578982409916502934394710000097878920117490851643088484419260292145498895337439594490079961520960338360713482434277993514741691235513316865747490921326150237615087/11920928955078125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^1*(1/79-x)^16 +
    (11223720562180550508786260618119993510643794720934925182241029096527759062971635236873584726724620664881463422786504884187861325417084728307674801252127636905395337347/23841857910156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^2*(1/79-x)^15 +
    (62583815275576703645133048934770868081999998831777667649614531392062951297025088135510941629361741556645785969674841456703167506964475458197434540767775106658052627811/26822090148925781250000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^3*(1/79-x)^14 +
    (868465776932707288772126446711667597773140842418087660005118305684417498159056620743699977502411202555192080202647959609787070539202958122458617816921738239100949818777/107288360595703125000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^4*(1/79-x)^13 +
    (932473840818800414910780916327585528986800030988991021765057979993569753592472183529876339715221099986300750845345074447282095669107668779948731122686808247933058073441/44703483581542968750000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^5*(1/79-x)^12 +
    (246425496747520385006967700428917663615089269193610091422475452027008115559160907188616599391907148544336628623593983250866362916061695205360011828227576179613213310337/5960464477539062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^6*(1/79-x)^11 +
    (43168867091214552991408058357635890235652297111064339351354164025395952893386863588171178453607270420744901544672691321364087250785885275779851189683914945373701380461/670552253723144531250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^7*(1/79-x)^10 +
    (44554749974856113205134525552372095535934734639723900867694531100267063689883360182906552240683251423114741195840499031326245843782687570696144697336312311487037377/558793544769287109375000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^8*(1/79-x)^9 +
    (551765444425471778496072478052113671690830912091410498854088623506292085901383913571584974122096391969659597593212438401618405787431641329362282078492050173431853/6984919309616088867187500000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^9*(1/79-x)^8 +
    (40994087477019781742728473806362813057342862509622466157567886161311030047049095290544603639555683499830738882461579074154889769252665485302053164685015741430669/654836185276508331298828125000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^10*(1/79-x)^7 +
    (107665079119292518875493669170983310376586367710384164060077358125087881464007837043537485772244967338169084431354981348131510287333917793373272385808775175739/2728484105318784713745117187500000000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^11*(1/79-x)^6 +
    (1999349773070927779391855158266247316188554672677320724004936478775589243764395065285847310573271091556754483578889279776054256864858948170178974341625688959/102318153949454426765441894531250000000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^12*(1/79-x)^5 +
    (1903795140250254063309122241580741655944693336637991434552018752850997442356257920478388535020898984575348468669241364093644616332041665302022193852450487/255795384873636066913604736328125000000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^13*(1/79-x)^4 +
    (4488351082165921983431715700003125477322137304136751915331019082380318040504846890024736868049676368906378711317721603625573562332357600195376826088547/2131628207280300557613372802734375000000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^14*(1/79-x)^3 +
    (166641843612261828294385822276192230099641585203702935213389075816814664944213957528918776245035262783888640485800043706556348524360012024497000317601/399680288865056354552507400512695312500000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^15*(1/79-x)^2 +
    (85920699539447031962423988961713808560373533999945331524942582338152916785371275075051868842670291171613459877017114526090307838338230260900298561/1665334536937734810635447502136230468750000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^16*(1/79-x)^1 +
    (20844932618891631256737214154084865620248832975302357812919476294164796282903163027554812973379609169984228402964412067146542525389359531591919/6938893903907228377647697925567626953125000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^17*(1/79-x)^0

noncomputable def linearBernstein79 (x : ℝ) : ℝ :=
    (37809664986102964980583187133833495565191162595931106148364086962336045323301694797750834499637036800790058139262493914133/22888183593750000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^0*(1/79-x)^16 +
    (604179210576566640192490367306681871621733065502363672290333115636110957891898364425097686080344109064206276047959933578371/22888183593750000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^1*(1/79-x)^15 +
    (4525512628447766780728297998323691960201579089437532633563488057975687236815127900318882347470758290797509813657807583648073/22888183593750000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^2*(1/79-x)^14 +
    (4218354416341482286967332393162282622294614492062219893887196643596281234171258579233108551171294294494681076780505993821059/4577636718750000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^3*(1/79-x)^13 +
    (13691867682215901647266140734127091464226177951534449975228948424918034433390496733574908939309790309229108308253697993097251/4577636718750000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^4*(1/79-x)^12 +
    (164088429537047401933155373245917014900566696206065842155995387354080037136811866003602331276548802452955569853968449812365193/22888183593750000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^5*(1/79-x)^11 +
    (300435436221096077454628966632892418569225817170924701791302016983669393405918477261496159067071704090786409042509560036239171/22888183593750000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^6*(1/79-x)^10 +
    (142876683449259094846598533646938034576093406078511241828476885173226719598951008763259120394608171669991830685178139437276471/7629394531250000000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^7*(1/79-x)^9 +
    (2006555253862470257637792228491484901263097809318647612826178561950697243016236668330330203143918313121485764922485487861841/95367431640625000000000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^8*(1/79-x)^8 +
    (16699167647673710548400098471843125861203057566801889048227971981361399593639451870406756997678818027976918120385663006637/894069671630859375000000000000000000000000000000000000000000 : ℝ)*(x-1/80)^9*(1/79-x)^7 +
    (145923600721267767489175183070081459276229561506754954179444718315446738415088263522646039734416485253325196990430477407/11175870895385742187500000000000000000000000000000000000000 : ℝ)*(x-1/80)^10*(1/79-x)^6 +
    (1987213254801696829441106366298205365496054850494774404273069492008018283910238893903094313266164153368257719289849819/279396772384643554687500000000000000000000000000000000000 : ℝ)*(x-1/80)^11*(1/79-x)^5 +
    (10336209575426005648835277661706260374282438567340182190772443709885850415177030611954060987975963808570994782373381/3492459654808044433593750000000000000000000000000000000 : ℝ)*(x-1/80)^12*(1/79-x)^4 +
    (19850603302989931681490270508347059804176724747441485000083296418098301724500909400935077827784173376496267646313/21827872842550277709960937500000000000000000000000000 : ℝ)*(x-1/80)^13*(1/79-x)^3 +
    (53099492424539923495231737749891174579882802874190793659075759005631608417422191512711883155466844655646350063/272848410531878471374511718750000000000000000000000 : ℝ)*(x-1/80)^14*(1/79-x)^2 +
    (353516923478225455276553631211939600865522166214628144198693855968273483846427172913478038947524239306321997/13642420526593923568725585937500000000000000000000 : ℝ)*(x-1/80)^15*(1/79-x)^1 +
    (91936453373903384766242667367820267091660752878533209950830884797464924510013297493001606855310890455369/56843418860808014869689941406250000000000000000 : ℝ)*(x-1/80)^16*(1/79-x)^0

theorem envelope_identity (x : ℝ) : Nlo x*(2*Glo x)-(1-9/25)*Dup x = envelopeBernstein79 x := by
  dsimp [Nlo, Dup, Glo, envelopeBernstein79]
  ring

theorem envelope_certificate {x : ℝ} (hlo : 1/80 ≤ x) (hhi : x ≤ 1/79) :
    0 < Nlo x*(2*Glo x)-(1-9/25)*Dup x := by
  rw [envelope_identity]
  unfold envelopeBernstein79
  by_cases ht : x < 1/79
  · have hl : 0 ≤ x-1/80 := by linarith
    have hr : 0 < 1/79-x := by linarith
    positivity
  · have he : x = 1/79 := by linarith
    rw [he]
    norm_num

theorem linear_identity (x : ℝ) : x*Nlo x-(23/50)*Dup x = linearBernstein79 x := by
  dsimp [Nlo, Dup, Glo, linearBernstein79]
  ring

theorem linear_certificate {x : ℝ} (hlo : 1/80 ≤ x) (hhi : x ≤ 1/79) :
    0 < x*Nlo x-(23/50)*Dup x := by
  rw [linear_identity]
  unfold linearBernstein79
  by_cases ht : x < 1/79
  · have hl : 0 ≤ x-1/80 := by linarith
    have hr : 0 < 1/79-x := by linarith
    positivity
  · have he : x = 1/79 := by linarith
    rw [he]
    norm_num

end HlawkaCodex79Scalar


/- Local module: Solutions.Hlawka79_WitnessBounds -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction
open HlawkaCodex79Scalar

lemma codex79_inverse_bounds {p : ℝ} (hp : 79 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1/79 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩
lemma codex79_inverse_lower {p : ℝ} (hp : 79 ≤ p) (hhi : p ≤ 80) : 1/80 ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hhi
lemma codex79_scaled {p : ℝ} (hp : 79 ≤ p) :
    0 ≤ (Real.log p-Real.log (3/4))*p⁻¹ ∧
    (Real.log p-Real.log (3/4))*p⁻¹ ≤ (36697087089/10^10 : ℝ)*p⁻¹+1/79 ∧
    (36697087089/10^10 : ℝ)*p⁻¹+1/79 <1/16 := by
  have hi := codex79_inverse_bounds hp
  have h0 : 0 ≤ Real.log p-Real.log (3/4) := by
    linarith [Real.log_nonneg (show 1 ≤ p by linarith), codex85_log_three_quarters.2]
  exact ⟨mul_nonneg h0 hi.1.le, witness_scaled_tangent (by linarith), by linarith [hi.2]⟩
lemma codex79_witness_bounds {p : ℝ} (hp : 79 ≤ p) :
    1/2 ≤ codex85Witness p ∧ codex85Witness p ≤ 1 := by
  have hl := codex79_scaled hp
  have h := Real.add_one_le_exp (-((Real.log p-Real.log (3/4))*p⁻¹))
  exact ⟨by dsimp [codex85Witness]; linarith [hl.2.1,hl.2.2],
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)⟩
lemma codex79_cyclicA_exp {p : ℝ} (hp : 79 ≤ p) :
    cyclicA p (codex85Witness p) = Real.exp (Real.log (2+3/4*p⁻¹)*p⁻¹) := by
  rw [cyclicA, codex85_witness_power (by linarith), add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]

lemma codex79_numerator_lower {p : ℝ} (hp : 79 ≤ p) :
    Nlo p⁻¹ ≤ 3*cyclicA p (codex85Witness p)-(3 : ℝ)^(1/p)*|2-codex85Witness p| := by
  set x := p⁻¹ with hxdef
  have hi := codex79_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ht := codex79_witness_bounds hp
  have hl := codex79_scaled hp
  let C : ℝ := 1098612289/10^9*x
  let Z : ℝ := 36697087089/10^10*x+1/79
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
  rw [← codex79_cyclicA_exp hp] at hA
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

lemma codex79_denominator_upper {p : ℝ} (hp : 79 ≤ p) :
    6*cyclicA p (codex85Witness p)-3*cyclicB p (codex85Witness p) ≤ Dup p⁻¹ := by
  set x := p⁻¹ with hxdef
  have hi := codex79_inverse_bounds hp
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
  rw [← codex79_cyclicA_exp hp] at hE
  have hB := codex85Aux_cyclicB_ge_two (t := codex85Witness p) (show 0 < p by linarith)
  dsimp [Dup,T] at hE ⊢
  linarith

end HlawkaSchatten.DiagonalConstruction


/- Local module: Solutions.Hlawka79_ScalarBounds -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace HlawkaSchatten.DiagonalConstruction
open HlawkaCodex79Scalar

lemma codex79_cyclicConstant_gt_linear {p : ℝ} (hp : 79 ≤ p) (hp' : p ≤ 80) :
    (23 / 50 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := codex79_inverse_bounds hp
  have hi' := codex79_inverse_lower hp hp'
  have ht := codex79_witness_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codex85Witness p by linarith [ht.1])
  have hn := codex79_numerator_lower hp
  have hd := codex79_denominator_upper hp
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


lemma codex79_power_tail {p : ℝ} (hp : 79 ≤ p) (hp' : p ≤ 80) :
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


lemma codex79_Dup_pos {x : ℝ} (hx : 0 < x) (hhi : x ≤ 1/79) : 0 < Dup x := by
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have h : 0 < 6931471808/10^10+3/8*x-9/128*x^2+27/256*x^3 := by
    nlinarith [pow_nonneg hx.le 3]
  dsimp [Dup]
  positivity

lemma codex79_Nlo_pos {x : ℝ} (hlo : 1/80 ≤ x) (hhi : x ≤ 1/79) : 0 < Nlo x := by
  have hx : 0 < x := by linarith
  have hc := sub_pos.mp (linear_certificate hlo hhi)
  have hd := codex79_Dup_pos hx hhi
  nlinarith

lemma codex79_Glo_pos {x : ℝ} (hlo : 1/80 ≤ x) (hhi : x ≤ 1/79) : 0 < Glo x := by
  have hx : 0 < x := by linarith
  have hx2 := pow_le_pow_left₀ hx.le hhi 2
  have hx4 := pow_le_pow_left₀ hx.le hhi 4
  have hg : 0 ≤ (6931471803/10^10-x^2/1000)*x := by
    apply mul_nonneg _ hx.le
    nlinarith
  dsimp [Glo]
  nlinarith [pow_nonneg hg 3]

lemma codex79_envelope_deficit {p : ℝ} (hp : 79 ≤ p) (hp' : p ≤ 80) :
    Glo p⁻¹ < 1-scalarEnvelopeRoot p (9/25) := by
  have hi := codex79_inverse_bounds hp
  set x := p⁻¹ with hxdef
  let a := (9/25 : ℝ)^p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a < x^2/1000 := codex79_power_tail hp hp'
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

lemma codex79_envelope_lt {p : ℝ} (hp : 79 ≤ p) (hp' : p ≤ 80) :
    scalarEnvelope p (9 / 25) < cyclicConstant p := by
  have hi := codex79_inverse_bounds hp
  have hi' := codex79_inverse_lower hp hp'
  have ht := codex79_witness_bounds hp
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ codex85Witness p by linarith [ht.1])
  have hn := codex79_numerator_lower hp
  have hd := codex79_denominator_upper hp
  have hg := codex79_envelope_deficit hp hp'
  have hc := (sub_pos.mp (envelope_certificate hi' hi.2))
  have hN0 := codex79_Nlo_pos hi' hi.2
  have hG0 := codex79_Glo_pos hi' hi.2
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
theorem solution : ∀ p : ℝ, 79 ≤ p → p ≤ 80 →
    (23/50 : ℝ)*p < cyclicConstant p ∧
    scalarEnvelope p (9/25) < cyclicConstant p := by
  intro p hp hp'
  exact ⟨codex79_cyclicConstant_gt_linear hp hp', codex79_envelope_lt hp hp'⟩
