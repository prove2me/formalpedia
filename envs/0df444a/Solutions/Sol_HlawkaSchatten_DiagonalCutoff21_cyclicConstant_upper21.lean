-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff21.cyclicConstant_upper21
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T09:04:09.39198+00:00
-- url     : https://prove2.me/submissions/e696f6e8-38ad-49b3-b319-6be8f8688015

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Mathlib.Analysis.Complex.ExponentialBounds
open HlawkaSchatten.DiagonalConstruction



/- Pair-tail bounds from Section 3 of the cutoff-21 paper. The finite
   numerical premise is an integer-power rational inequality, not an
   assumption that an external checker succeeded. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff21

theorem two_tail_norm_bound (m : ℕ) (hm : 1 ≤ m)
    {p S y1 y2 rho cap eps : ℝ}
    (hp : (m : ℝ) ≤ p) (hS : 0 ≤ S) (hScap : S ≤ cap) (hcap : 0 < cap)
    (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (heps : 0 ≤ eps)
    (hy1 : |y1| ≤ rho * S) (hy2 : |y2| ≤ rho * S)
    (hcert : 2 * rho ^ m * cap ≤ (m : ℝ) * eps) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + eps := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp1 : 1 ≤ p := hm1.trans hp
  have hp0 : 0 < p := by linarith
  rcases eq_or_lt_of_le hS with hS0 | hSpos
  · have hzero : S = 0 := hS0.symm
    subst S
    have hy10 : y1 = 0 := abs_nonpos_iff.mp (by simpa using hy1)
    have hy20 : y2 = 0 := abs_nonpos_iff.mp (by simpa using hy2)
    subst y1 y2
    simpa [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')] using heps
  · rw [abs_of_pos hSpos]
    have hpow : rho ^ p ≤ rho ^ m := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge' hrho hrho1 (by positivity) hp
    have hy (y : ℝ) (hy : |y| ≤ rho * S) :
        |y| ^ p ≤ rho ^ m * S ^ p := by
      calc
        _ ≤ (rho * S) ^ p := Real.rpow_le_rpow (abs_nonneg _) hy hp0.le
        _ = rho ^ p * S ^ p := Real.mul_rpow hrho hSpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
    have hnum : 2 * rho ^ m ≤ p * (eps / S) := by
      have h1 : 2 * rho ^ m ≤ (m : ℝ) * eps / cap := (le_div_iff₀ hcap).2 hcert
      have h2 : eps / cap ≤ eps / S := div_le_div_of_nonneg_left heps hSpos hScap
      have h3 := mul_le_mul hp h2 (div_nonneg heps hcap.le) (by positivity : (0 : ℝ) ≤ p)
      calc
        _ ≤ (m : ℝ) * eps / cap := h1
        _ = (m : ℝ) * (eps / cap) := by ring
        _ ≤ p * (eps / S) := h3
    have hbern : 1 + p * (eps / S) ≤ (1 + eps / S) ^ p :=
      one_add_mul_self_le_rpow_one_add (by have := div_nonneg heps hSpos.le; linarith) hp1
    have heq : (S + eps) ^ p = S ^ p * (1 + eps / S) ^ p := by
      rw [← Real.mul_rpow hSpos.le (by positivity)]
      congr 1
      field_simp
    have h1 := hy y1 hy1
    have h2 := hy y2 hy2
    have h3 := mul_le_mul_of_nonneg_right hnum (show 0 ≤ S ^ p by positivity)
    have h4 := mul_le_mul_of_nonneg_left hbern (show 0 ≤ S ^ p by positivity)
    have hsum : S ^ p + |y1| ^ p + |y2| ^ p ≤ (S + eps) ^ p := by
      rw [heq]
      nlinarith
    calc
      _ ≤ ((S + eps) ^ p) ^ (1 / p) := Real.rpow_le_rpow (by positivity) hsum (by positivity)
      _ = S + eps := by rw [one_div, Real.rpow_rpow_inv (by positivity) hp0.ne']

theorem half_tail21 {p S y1 y2 : ℝ} (hp : 21 ≤ p)
    (hS : 0 ≤ S) (hS3 : S ≤ 3) (hy1 : |y1| ≤ S / 2) (hy2 : |y2| ≤ S / 2) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + 1 / 100000 := by
  apply two_tail_norm_bound 21 (by norm_num) hp hS hS3 (by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num) (by norm_num)
  · linarith
  · linarith
  · norm_num

theorem refined_tail21 {p S y1 y2 : ℝ} (hp : 21 ≤ p)
    (hS : 349 / 250 ≤ S) (hS3 : S ≤ 3)
    (hy1 : |y1| ≤ 129 / 250) (hy2 : |y2| ≤ 129 / 250) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + 1 / 100000000 := by
  apply two_tail_norm_bound 21 (by norm_num) hp (by linarith) hS3 (by norm_num)
    (show (0 : ℝ) ≤ 129 / 349 by norm_num) (by norm_num) (by norm_num)
  · linarith
  · linarith
  · norm_num

theorem refined_tail26 {p S y1 y2 : ℝ} (hp : 26 ≤ p)
    (hS : 3 / 2 ≤ S) (hS3 : S ≤ 3)
    (hy1 : |y1| ≤ 353 / 500) (hy2 : |y2| ≤ 353 / 500) :
    (|S| ^ p + |y1| ^ p + |y2| ^ p) ^ (1 / p) ≤ S + 1 / 100000000 := by
  apply two_tail_norm_bound 26 (by norm_num) hp (by linarith) hS3 (by norm_num)
    (show (0 : ℝ) ≤ 353 / 750 by norm_num) (by norm_num) (by norm_num)
  · linarith
  · linarith
  · norm_num

theorem clip_pair_tail {ell u v w A diagonal off total excluded y : ℝ}
    (hd : -u ≤ diagonal ∧ diagonal ≤ -ell) (ho : v ≤ off ∧ off ≤ w)
    (hV : total ≤ A) (hx : v ≤ excluded)
    (hpair : y = diagonal + off) (hclip : y = total - excluded) :
    v - u ≤ y ∧ y ≤ min (w - ell) (A - v) := by
  constructor
  · linarith [hd.1, ho.1]
  · apply le_min <;> linarith [hd.2, ho.2]

end HlawkaSchatten.DiagonalCutoff21


/- An elementary upper bound for the cyclic ratio on the finite window.
   This proves the upper-bound component of the paper's scalar targets
   directly, without assuming the stored interval-arithmetic reports. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem root_two_three_bounds {p : ℝ} (hp : 21 ≤ p) (hp32 : p ≤ 32) :
    1 + (69/100 : ℝ) * (1/p) + (69/100 : ℝ)^2 * (1/p)^2 / 2 ≤ (2 : ℝ)^(1/p) ∧
    (2 : ℝ)^(1/p) ≤ 1 + 1/p ∧
    1 + 1/p ≤ (3 : ℝ)^(1/p) ∧
    (3 : ℝ)^(1/p) ≤ 3 := by
  have hp0 : 0 < p := by linarith
  have hu0 : 0 ≤ 1/p := by positivity
  have hu1 : 1/p ≤ 1 := (div_le_one hp0).mpr (by linarith)
  have hpu : p * (1/p) = 1 := mul_one_div_cancel hp0.ne'
  have hlog2 : (69/100 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hb : 1 + (69/100 : ℝ) * (1/p) + (69/100 : ℝ)^2 * (1/p)^2 / 2 ≤ (2 : ℝ)^(1/p) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ (69/100 : ℝ) * (1/p) by positivity)
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlog2 hu0)
    nlinarith [he]
  have hbU : (2 : ℝ)^(1/p) ≤ 1 + 1/p := by
    have hbern := one_add_mul_self_le_rpow_one_add
      (show -1 ≤ 1/p by linarith) (show 1 ≤ p by linarith)
    have hr : ((2 : ℝ)^(1/p))^p = 2 := by
      rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hp0.ne', Real.rpow_one]
    apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) hp0).mp
    rw [hr]
    nlinarith
  have ha : 1 + 1/p ≤ (3 : ℝ)^(1/p) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have h := Real.add_one_le_exp (Real.log 3 * (1/p))
    have hm := mul_le_mul_of_nonneg_right hlog3 hu0
    linarith
  have haU : (3 : ℝ)^(1/p) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hu1
    simpa using h
  exact ⟨hb,hbU,ha,haU⟩

theorem cyclicB_upper21 {p t : ℝ} (hp : 21 ≤ p)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) : cyclicB p t ≤ 2 + 1/100000 := by
  have hy : |1-t| ≤ (2 : ℝ)/2 := abs_le.mpr ⟨by linarith [ht.1,ht.2],by linarith [ht.1,ht.2]⟩
  have h := half_tail21 (p := p) (S := 2) (y1 := 1-t) (y2 := 1-t)
    hp (by norm_num) (by norm_num) hy hy
  have he : (|2| ^ p + |1-t| ^ p + |1-t| ^ p : ℝ) = 2 * |1-t| ^ p + 2^p := by
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [he] at h
  exact h

theorem cyclicA_lower21 {p t : ℝ} (hp : 21 ≤ p)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) :
    (2 : ℝ)^(1/p) ≤ cyclicA p t ∧ t ≤ cyclicA p t := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  constructor
  · apply Real.rpow_le_rpow (by norm_num)
      (show (2 : ℝ) ≤ t^p+2 by linarith [Real.rpow_nonneg ht0 p]) (by positivity)
  · calc
      t = (t^p)^(1/p) := by rw [one_div, Real.rpow_rpow_inv ht0 hp0.ne']
      _ ≤ cyclicA p t := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

theorem cyclic_minimum_lower21 {p a b A t : ℝ} (hp : 21 ≤ p)
    (hb : 1 + (69/100 : ℝ)*(1/p)+(69/100 : ℝ)^2*(1/p)^2/2 ≤ b)
    (hbU : b ≤ 1+1/p) (ha : 1+1/p ≤ a) (haU : a ≤ 3)
    (hAb : b ≤ A) (hAt : t ≤ A) :
    2*p + 1/1000 ≤ 2*(p-1)*A + (2/3)*a*(2-t) := by
  have hp0 : 0 < p := by linarith
  set z := 1/p with hz
  have hz0 : 0 ≤ z := by positivity
  have hz21 : z ≤ 1/21 := one_div_le_one_div_of_le (by norm_num) hp
  have hpz : p*z = 1 := mul_one_div_cancel hp0.ne'
  have hpz2 : p*z^2 = z := by
    calc
      _ = (p*z)*z := by ring
      _ = z := by rw [hpz]; ring
  have hz2 : z^2 ≤ (1/21 : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1/21-z by linarith) (show 0 ≤ 1/21+z by linarith)]
  have hradial := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*(p-1) by linarith)
  have htail := mul_le_mul ha (show 1-z ≤ 2-b by linarith)
    (show 0 ≤ 1-z by linarith) (show 0 ≤ a by linarith)
  have hmin : 2*p+1/1000 ≤ 2*(p-1)*b+(2/3)*a*(2-b) := by
    nlinarith
  have hpm : 0 ≤ p-1 := by linarith
  have ha0 : 0 ≤ a := by linarith
  by_cases htb : t ≤ b
  · have h1 := mul_nonneg hpm (sub_nonneg.mpr hAb)
    have h2 := mul_nonneg ha0 (sub_nonneg.mpr htb)
    nlinarith
  · have h1 := mul_nonneg hpm (sub_nonneg.mpr hAt)
    have h2 := mul_nonneg (show 0 ≤ p-1-a/3 by linarith) (show 0 ≤ t-b by linarith)
    nlinarith

theorem cyclicRatio_upper21 {p t : ℝ} (hp : 21 ≤ p) (hp32 : p ≤ 32)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) : cyclicRatio p t ≤ p/2 := by
  obtain ⟨hb,hbU,ha,haU⟩ := root_two_three_bounds hp hp32
  obtain ⟨hAb,hAt⟩ := cyclicA_lower21 hp ht
  have hB := cyclicB_upper21 hp ht
  have hm := cyclic_minimum_lower21 hp hb hbU ha haU hAb hAt
  have hp0 : 0 < p := by linarith
  have hu32 : (1/32 : ℝ) ≤ 1/p := one_div_le_one_div_of_le hp0 hp32
  have hB0 : 0 ≤ (2 : ℝ)^(1/p) := by positivity
  have hA : 1+1/64 ≤ cyclicA p t := by nlinarith [sq_nonneg (1/p)]
  have hden : 0 < 6*cyclicA p t-3*cyclicB p t := by linarith
  have hmB := mul_le_mul_of_nonneg_left hB hp0.le
  unfold cyclicRatio
  rw [abs_of_nonneg (show 0 ≤ 2-t by linarith [ht.2]), div_le_iff₀ hden]
  nlinarith

theorem cyclicConstant_upper21 {p : ℝ} (hp : 21 ≤ p) (hp32 : p ≤ 32) :
    cyclicConstant p ≤ p/2 := by
  unfold cyclicConstant
  apply csSup_le
  · exact ⟨cyclicRatio p 1, 1, by norm_num, rfl⟩
  · rintro y ⟨t,ht,rfl⟩
    exact cyclicRatio_upper21 hp hp32 ht

end HlawkaSchatten.DiagonalCutoff21

theorem solution {p : ℝ} (hp : 21 ≤ p) (hp32 : p ≤ 32) :
    cyclicConstant p ≤ p/2 := by
  exact HlawkaSchatten.DiagonalCutoff21.cyclicConstant_upper21 hp hp32

#print axioms solution
