-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff21.lower21_chunk08
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-17T09:33:59.949266+00:00
-- url     : https://prove2.me/submissions/463ec8fe-700f-499f-939b-3ea2ee65b99a

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
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


/- Adapted from @bwdaugherty's accepted cutoff-32 contribution,
   submission d75400b0-5a0e-4167-8192-7fd299469c2e (2026-10-16),
   https://prove2.me/theorems/4e05427b-74d9-4e61-8d14-a52384a5ca10 .
   Public Prove2Me contribution under Apache-2.0; see sources/NOTICE.md.
   These generic lemmas do not assume p >= 32. -/
set_option autoImplicit false

namespace HlawkaSchatten.DiagonalCutoff21

/-- Increments of `x ↦ x ^ p` over intervals of equal length grow to the right. -/
theorem rpow_swap_le {p : ℝ} (hp : 1 ≤ p) {x y c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hc : 0 ≤ c) : (x + c) ^ p + y ^ p ≤ x ^ p + (y + c) ^ p := by
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ y - x + c by linarith) with h | h
  · have hc0 : c = 0 := by linarith
    have hy : y = x := by linarith
    subst hc0 hy; simp
  · have hconv := (convexOn_rpow hp).2
    have hxm : x ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 hx
    have hym : y + c ∈ Set.Ici (0:ℝ) := Set.mem_Ici.2 (by linarith)
    have hl : 0 ≤ (y - x) / (y - x + c) := div_nonneg (by linarith) h.le
    have hm : 0 ≤ c / (y - x + c) := div_nonneg hc h.le
    have hs : (y - x) / (y - x + c) + c / (y - x + c) = 1 := by
      rw [← add_div, div_self h.ne']
    have h1 := hconv hxm hym hl hm hs
    have h2 := hconv hxm hym hm hl (by linarith)
    simp only [smul_eq_mul] at h1 h2
    have e1 : (y - x) / (y - x + c) * x + c / (y - x + c) * (y + c) = x + c := by
      field_simp; ring
    have e2 : c / (y - x + c) * x + (y - x) / (y - x + c) * (y + c) = y := by
      field_simp; ring
    rw [e1] at h1
    rw [e2] at h2
    calc (x + c) ^ p + y ^ p ≤ _ := add_le_add h1 h2
      _ = ((y - x) / (y - x + c) + c / (y - x + c)) * (x ^ p + (y + c) ^ p) := by ring
      _ = _ := by rw [hs, one_mul]

/-- Power mean for two terms. -/
theorem add_rpow_le_two {p : ℝ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u + v) ^ p ≤ 2 ^ p / 2 * (u ^ p + v ^ p) := by
  have h := (convexOn_rpow hp).2 (Set.mem_Ici.2 hu) (Set.mem_Ici.2 hv)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : 1/2 * u + 1/2 * v = (u + v) / 2 := by ring
  rw [e, Real.div_rpow (by linarith) (by norm_num)] at h
  have h2p : 0 < (2:ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  rw [div_le_iff₀ h2p] at h
  calc (u + v) ^ p ≤ _ := h
    _ = _ := by ring

/-- The two-coordinate constant `2 ^ (1 - 1/p)`. -/
noncomputable def cp (p : ℝ) : ℝ := 2 * (1/2 : ℝ) ^ (1/p)

theorem cp_pos (p : ℝ) : 0 < cp p := by unfold cp; positivity

theorem cp_rpow {p : ℝ} (hp : 0 < p) : cp p ^ p = 2 ^ p / 2 := by
  unfold cp
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by norm_num),
    one_div_mul_cancel hp.ne', Real.rpow_one]; ring

theorem sum_div_cp_rpow_le {p : ℝ} (hp : 1 ≤ p) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ((u + v) / cp p) ^ p ≤ u ^ p + v ^ p := by
  have hp0 : 0 < p := by linarith
  rw [Real.div_rpow (by linarith) (cp_pos p).le, cp_rpow hp0, div_le_iff₀ (by positivity)]
  rw [mul_comm]; exact add_rpow_le_two hp hu hv

theorem sum_le_cp_mul {p : ℝ} (hp : 1 ≤ p) {u v S : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hS : 0 ≤ S) (h : u ^ p + v ^ p ≤ S ^ p) : u + v ≤ cp p * S := by
  have hp0 : 0 < p := by linarith
  have h1 := (sum_div_cp_rpow_le hp hu hv).trans h
  have h2 : (u + v) / cp p ≤ S :=
    (Real.rpow_le_rpow_iff (div_nonneg (by linarith) (cp_pos p).le) hS hp0).1 h1
  rw [div_le_iff₀ (cp_pos p)] at h2; linarith

/-- Diagonal certificate: a row with nearly extremal two-coordinate mass has a small
diagonal entry. -/
theorem diag_cert {p : ℝ} (hp : 1 ≤ p) {a w c N D δ U Ab : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hrow : a ^ p + (w / c) ^ p ≤ N ^ p) (hw : c * N - D ≤ w) (hDc : D / c ≤ δ)
    (hδ : 0 ≤ δ) (hδN : δ ≤ N) (hNU : N ≤ U) (hU : 0 < U) (hAb : 0 ≤ Ab)
    (hcert : 1 ≤ (Ab / U) ^ p + (1 - δ / U) ^ p) : a ≤ Ab := by
  have hp0 : 0 < p := by linarith
  have h1 : N - δ ≤ w / c := by
    have e : w / c = N - D / c + (w - (c * N - D)) / c := by field_simp; ring
    rw [e]
    have : 0 ≤ (w - (c * N - D)) / c := div_nonneg (by linarith) hc.le
    linarith
  have h2 : (N - δ) ^ p ≤ (w / c) ^ p := Real.rpow_le_rpow (by linarith) h1 hp0.le
  have h3 := rpow_swap_le hp (x := N - δ) (y := U - δ) (c := δ) (by linarith) (by linarith) hδ
  rw [sub_add_cancel, sub_add_cancel] at h3
  have h4 : U ^ p ≤ Ab ^ p + (U - δ) ^ p := by
    have e : 1 - δ / U = (U - δ) / U := by field_simp
    rw [e, Real.div_rpow hAb hU.le, Real.div_rpow (by linarith) hU.le, ← add_div,
      le_div_iff₀ (by positivity), one_mul] at hcert
    exact hcert
  have h5 : a ^ p ≤ Ab ^ p := by linarith
  exact (Real.rpow_le_rpow_iff ha hAb hp0).1 h5

/-- Two-dimensional Minkowski inequality in power form. -/
theorem mink2 {p : ℝ} (hp : 1 ≤ p) {x1 y1 x2 y2 N1 N2 : ℝ} (hx1 : 0 ≤ x1) (hy1 : 0 ≤ y1)
    (hx2 : 0 ≤ x2) (hy2 : 0 ≤ y2) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2)
    (h1 : x1 ^ p + y1 ^ p ≤ N1 ^ p) (h2 : x2 ^ p + y2 ^ p ≤ N2 ^ p) :
    (x1 + x2) ^ p + (y1 + y2) ^ p ≤ (N1 + N2) ^ p := by
  have hp0 : 0 < p := by linarith
  have hM := Real.Lp_add_le (Finset.univ : Finset (Fin 2)) ![x1, y1] ![x2, y2] hp
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hM
  rw [abs_of_nonneg (by linarith : 0 ≤ x1 + x2), abs_of_nonneg (by linarith : 0 ≤ y1 + y2),
    abs_of_nonneg hx1, abs_of_nonneg hy1, abs_of_nonneg hx2, abs_of_nonneg hy2] at hM
  have hr1 : (x1 ^ p + y1 ^ p) ^ (1/p) ≤ N1 := by
    calc (x1 ^ p + y1 ^ p) ^ (1/p) ≤ (N1 ^ p) ^ (1/p) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = N1 := by rw [one_div, Real.rpow_rpow_inv hN1 hp0.ne']
  have hr2 : (x2 ^ p + y2 ^ p) ^ (1/p) ≤ N2 := by
    calc (x2 ^ p + y2 ^ p) ^ (1/p) ≤ (N2 ^ p) ^ (1/p) :=
          Real.rpow_le_rpow (by positivity) h2 (by positivity)
      _ = N2 := by rw [one_div, Real.rpow_rpow_inv hN2 hp0.ne']
  have h3 : ((x1 + x2) ^ p + (y1 + y2) ^ p) ^ (1/p) ≤ N1 + N2 := by linarith
  have hS : 0 ≤ (x1 + x2) ^ p + (y1 + y2) ^ p := by positivity
  calc (x1 + x2) ^ p + (y1 + y2) ^ p
      = (((x1 + x2) ^ p + (y1 + y2) ^ p) ^ (1/p)) ^ p := by
        rw [← Real.rpow_mul hS, one_div_mul_cancel hp0.ne', Real.rpow_one]
    _ ≤ (N1 + N2) ^ p := Real.rpow_le_rpow (by positivity) h3 hp0.le

/-- Ratio lower bound from a convexity certificate. -/
theorem ratio_lower {p x y s τ : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) (_hy : 0 ≤ y)
    (hxy : x ^ p + y ^ p ≤ 1) (hs : s ≤ x + y) (hτ0 : 0 ≤ τ) (hτs : 2 * τ ≤ s)
    (hc : 1 < τ ^ p + (s - τ) ^ p) : τ < x := by
  have hp0 : 0 < p := by linarith
  by_contra hle
  push Not at hle
  have h1 := rpow_swap_le hp (x := x) (y := s - τ) (c := τ - x) hx (by linarith) (by linarith)
  have e1 : x + (τ - x) = τ := by ring
  have e2 : s - τ + (τ - x) = s - x := by ring
  rw [e1, e2] at h1
  have h2 : (s - x) ^ p ≤ y ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
  linarith

/-- Ratio upper bound from a convexity certificate. -/
theorem ratio_upper {p x y s σ : ℝ} (hp : 1 ≤ p) (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ^ p + y ^ p ≤ 1) (hs : s ≤ x + y) (hs1 : 1 ≤ s) (hσs : s ≤ 2 * σ)
    (hc : 1 < σ ^ p + (s - σ) ^ p) : x < σ := by
  have hp0 : 0 < p := by linarith
  by_contra hle
  push Not at hle
  have hx1 : x ≤ 1 := by
    by_contra h
    push Not at h
    have : 1 < x ^ p := Real.one_lt_rpow h hp0
    have : 0 ≤ y ^ p := Real.rpow_nonneg hy p
    linarith
  have h1 := rpow_swap_le hp (x := s - x) (y := σ) (c := x - σ) (by linarith) (by linarith)
    (by linarith)
  have e1 : s - x + (x - σ) = s - σ := by ring
  have e2 : σ + (x - σ) = x := by ring
  rw [e1, e2] at h1
  have h2 : (s - x) ^ p ≤ y ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0.le
  linarith

/-! ## Turning integer-power checks into real-exponent certificates -/

theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)

theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'

theorem cert_le {x y X Y : ℝ} (m k : ℕ) (hk : 0 < k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : X ^ k ≤ x ^ m) (hY : Y ^ k ≤ y ^ m)
    (hXY : 1 ≤ X + Y) : ∀ p : ℝ, 0 ≤ p → p ≤ (m : ℝ) / k → 1 ≤ x ^ p + y ^ p := by
  intro p hp0 hpb
  have h1 := le_rpow_of_pow_le hx0 m k hk hX
  have h2 := le_rpow_of_pow_le hy0 m k hk hY
  have h3 : x ^ ((m : ℝ) / k) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp0 hpb
  have h4 : y ^ ((m : ℝ) / k) ≤ y ^ p := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1 hp0 hpb
  linarith

theorem cert_lt {x y X Y : ℝ} (m k : ℕ) (hk : 0 < k) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hX : X ^ k ≤ x ^ m) (hY : Y ^ k ≤ y ^ m)
    (hXY : 1 < X + Y) : ∀ p : ℝ, 0 ≤ p → p ≤ (m : ℝ) / k → 1 < x ^ p + y ^ p := by
  intro p hp0 hpb
  have h1 := le_rpow_of_pow_le hx0 m k hk hX
  have h2 := le_rpow_of_pow_le hy0 m k hk hY
  have h3 : x ^ ((m : ℝ) / k) ≤ x ^ p := Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp0 hpb
  have h4 : y ^ ((m : ℝ) / k) ≤ y ^ p := Real.rpow_le_rpow_of_exponent_ge' hy0 hy1 hp0 hpb
  linarith


end HlawkaSchatten.DiagonalCutoff21

/- Fixed cyclic witnesses and Bernoulli transport of endpoint root bounds.
   This is a kernel-checkable route to the remaining scalar lower bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem root_transfer_upper {m p B b A : ℝ} (hm : 0 < m) (hp : m ≤ p)
    (hB : 0 ≤ B) (hBb : B ≤ b) (hb : b ≤ A^m) (hA : 1 ≤ A) :
    B^(1/p) ≤ 1+(m/p)*(A-1) := by
  have hp0 : 0 < p := hm.trans_le hp
  have hmp : 0 ≤ m/p := div_nonneg hm.le hp0.le
  have hbase : 0 ≤ 1+(m/p)*(A-1) := by positivity
  have hratio : 1 ≤ p/m := (le_div_iff₀ hm).mpr (by simpa using hp)
  have hb0 := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ (m/p)*(A-1) by
      have hnon := mul_nonneg hmp (sub_nonneg.mpr hA)
      linarith) hratio
  have hroot : A ≤ (1+(m/p)*(A-1))^(p/m) := by
    convert hb0 using 1 <;> field_simp <;> ring
  have hpow : A^m ≤ (1+(m/p)*(A-1))^p := by
    have h := Real.rpow_le_rpow (by linarith : 0 ≤ A) hroot hm.le
    rw [← Real.rpow_mul hbase] at h
    convert h using 1 <;> field_simp
  calc
    _ ≤ ((1+(m/p)*(A-1))^p)^(1/p) :=
      Real.rpow_le_rpow hB (hBb.trans (hb.trans hpow)) (by positivity)
    _ = _ := by rw [one_div, Real.rpow_rpow_inv hbase hp0.ne']

theorem cyclic_denominator_positive21 {p t : ℝ} (hp : 21 ≤ p) (hp32 : p ≤ 32)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 2) : 0 < 6*cyclicA p t-3*cyclicB p t := by
  obtain ⟨hb,_,_,_⟩ := root_two_three_bounds hp hp32
  have hAb := (cyclicA_lower21 hp ht).1
  have hB := cyclicB_upper21 hp ht
  have hp0 : 0 < p := by linarith
  have hu32 : (1/32 : ℝ) ≤ 1/p := one_div_le_one_div_of_le hp0 hp32
  have hA : 1+1/64 ≤ cyclicA p t := by nlinarith [sq_nonneg (1/p)]
  linarith

theorem cyclicB_lower_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  have h : (2 : ℝ)^p ≤ 2*|1-t|^p+2^p := by
    have := Real.rpow_nonneg (abs_nonneg (1-t)) p
    linarith
  calc
    (2 : ℝ) = (2^p)^(1/p) := by rw [one_div, Real.rpow_rpow_inv (by norm_num) hp.ne']
    _ ≤ cyclicB p t := Real.rpow_le_rpow (by positivity) h (by positivity)

theorem cyclicRatio_lower_endpoint {p alpha beta c t Aup aup : ℝ}
    (hp : 21 ≤ p) (hp32 : p ≤ 32) (ha : 0 < alpha)
    (hap : alpha ≤ p) (hpb : p ≤ beta) (hc : 0 < c) (hcp : 1 ≤ 2*c*p)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hAup : 1 ≤ Aup) (haup : 1 ≤ aup)
    (hAend : t^alpha+2 ≤ Aup^alpha) (haend : (3 : ℝ) ≤ aup^alpha)
    (hH : 0 ≤ 3*(Aup-1)-(2-t)*(aup-1))
    (hcheck : 0 < 3-(2-t)+(alpha/beta)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) :
    c*p < cyclicRatio p t := by
  have hp0 : 0 < p := by linarith
  have htpos : 0 < t := by linarith
  have htp : t^p ≤ t^alpha := Real.rpow_le_rpow_of_exponent_ge htpos ht1 hap
  have hAp : cyclicA p t ≤ 1+(alpha/p)*(Aup-1) := by
    exact root_transfer_upper ha hap (by positivity) (by linarith) hAend hAup
  have hap' : (3 : ℝ)^(1/p) ≤ 1+(alpha/p)*(aup-1) :=
    root_transfer_upper ha hap (by norm_num) le_rfl haend haup
  have hB := cyclicB_lower_two (t := t) hp0
  have hden := cyclic_denominator_positive21 hp hp32 (show t ∈ Set.Icc (1/2 : ℝ) 2 by exact ⟨ht0,by linarith⟩)
  have hmono := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left ha.le hp0 hpb) hH
  have hpos : 0 < 3-(2-t)+(alpha/p)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1) := by linarith
  have h1 := mul_le_mul_of_nonneg_left hAp (show 0 ≤ 6*c*p-3 by linarith)
  have h2 := mul_le_mul_of_nonneg_left hap' (show 0 ≤ 2-t by linarith)
  have heq : (6*c*p-3)*(1+(alpha/p)*(Aup-1))+(2-t)*(1+(alpha/p)*(aup-1)) =
      6*c*p-(3-(2-t)+(alpha/p)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) := by
    field_simp
    ring
  have h3 := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*c*p by positivity)
  unfold cyclicRatio
  rw [abs_of_nonneg (show 0 ≤ 2-t by linarith), lt_div_iff₀ hden]
  nlinarith

theorem cyclicConstant_lower_endpoint {p alpha beta c t Aup aup : ℝ}
    (hp : 21 ≤ p) (hp32 : p ≤ 32) (ha : 0 < alpha)
    (hap : alpha ≤ p) (hpb : p ≤ beta) (hc : 0 < c) (hcp : 1 ≤ 2*c*p)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hAup : 1 ≤ Aup) (haup : 1 ≤ aup)
    (hAend : t^alpha+2 ≤ Aup^alpha) (haend : (3 : ℝ) ≤ aup^alpha)
    (hH : 0 ≤ 3*(Aup-1)-(2-t)*(aup-1))
    (hcheck : 0 < 3-(2-t)+(alpha/beta)*(3*(Aup-1)-(2-t)*(aup-1))-6*c*alpha*(Aup-1)) :
    c*p < cyclicConstant p := by
  have hratio := cyclicRatio_lower_endpoint hp hp32 ha hap hpb hc hcp ht0 ht1 hAup haup hAend haend hH hcheck
  have hbounded : BddAbove (cyclicRatio p '' Set.Icc (1/2 : ℝ) 2) := by
    refine ⟨p/2, ?_⟩
    rintro y ⟨s,hs,rfl⟩
    exact cyclicRatio_upper21 hp hp32 hs
  have ht : t ∈ Set.Icc (1/2 : ℝ) 2 := ⟨ht0,by linarith⟩
  exact hratio.trans_le (le_csSup hbounded (Set.mem_image_of_mem (cyclicRatio p) ht))

end HlawkaSchatten.DiagonalCutoff21


/- Fixed rational cyclic witnesses on the original real-exponent slabs.
   Every endpoint root bound is reduced to a rational integer-power
   inequality. The conclusion holds throughout each real interval. -/
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxHeartbeats 200000000

namespace HlawkaSchatten.DiagonalCutoff21
open HlawkaSchatten.DiagonalConstruction

theorem lower21_scalar128 (p : ℝ) (hpa : (25 : ℝ) ≤ p) (hpb : p ≤ (801/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(25 : ℝ) ≤ (171978099/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (171978099/10000000000 : ℝ)) (by norm_num) (by norm_num) 25 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20171978099/10000000000 : ℝ) ≤ (5142330007/5000000000 : ℝ)^(25 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5142330007/5000000000 : ℝ)) (X := (20171978099/10000000000 : ℝ)) (by norm_num) 25 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1306155439/1250000000 : ℝ)^(25 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1306155439/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 25 1 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (25 : ℝ)) (beta := (801/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (5142330007/5000000000 : ℝ)) (aup := (1306155439/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar129 (p : ℝ) (hpa : (801/32 : ℝ) ≤ p) (hpb : p ≤ (401/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(801/32 : ℝ) ≤ (34221377/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (34221377/2000000000 : ℝ)) (by norm_num) (by norm_num) 801 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4034221377/2000000000 : ℝ) ≤ (2571070471/2500000000 : ℝ)^(801/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2571070471/2500000000 : ℝ)) (X := (4034221377/2000000000 : ℝ)) (by norm_num) 801 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10448670261/10000000000 : ℝ)^(801/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10448670261/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 801 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (801/32 : ℝ)) (beta := (401/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2571070471/2500000000 : ℝ)) (aup := (10448670261/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar130 (p : ℝ) (hpa : (401/16 : ℝ) ≤ p) (hpb : p ≤ (803/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(401/16 : ℝ) ≤ (34048017/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (34048017/2000000000 : ℝ)) (by norm_num) (by norm_num) 401 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4034048017/2000000000 : ℝ) ≤ (10283904799/10000000000 : ℝ)^(401/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10283904799/10000000000 : ℝ)) (X := (4034048017/2000000000 : ℝ)) (by norm_num) 401 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10448098471/10000000000 : ℝ)^(401/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10448098471/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 401 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (401/16 : ℝ)) (beta := (803/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10283904799/10000000000 : ℝ)) (aup := (10448098471/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar131 (p : ℝ) (hpa : (803/32 : ℝ) ≤ p) (hpb : p ≤ (201/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(803/32 : ℝ) ≤ (42344419/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (42344419/2500000000 : ℝ)) (by norm_num) (by norm_num) 803 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5042344419/2500000000 : ℝ) ≤ (2570882189/2500000000 : ℝ)^(803/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2570882189/2500000000 : ℝ)) (X := (5042344419/2500000000 : ℝ)) (by norm_num) 803 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1305941017/1250000000 : ℝ)^(803/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1305941017/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 803 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (803/32 : ℝ)) (beta := (201/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2570882189/2500000000 : ℝ)) (aup := (1305941017/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar132 (p : ℝ) (hpa : (201/8 : ℝ) ≤ p) (hpb : p ≤ (805/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(201/8 : ℝ) ≤ (33703927/2000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (33703927/2000000000 : ℝ)) (by norm_num) (by norm_num) 201 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (4033703927/2000000000 : ℝ) ≤ (8226523/8000000 : ℝ)^(201/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (8226523/8000000 : ℝ)) (X := (4033703927/2000000000 : ℝ)) (by norm_num) 201 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10446959251/10000000000 : ℝ)^(201/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10446959251/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 201 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (201/8 : ℝ)) (beta := (805/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (8226523/8000000 : ℝ)) (aup := (10446959251/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar133 (p : ℝ) (hpa : (805/32 : ℝ) ≤ p) (hpb : p ≤ (403/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(805/32 : ℝ) ≤ (167665941/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (167665941/10000000000 : ℝ)) (by norm_num) (by norm_num) 805 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20167665941/10000000000 : ℝ) ≤ (10282779777/10000000000 : ℝ)^(805/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10282779777/10000000000 : ℝ)) (X := (20167665941/10000000000 : ℝ)) (by norm_num) 805 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1044639181/1000000000 : ℝ)^(805/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1044639181/1000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 805 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (805/32 : ℝ)) (beta := (403/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10282779777/10000000000 : ℝ)) (aup := (1044639181/1000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar134 (p : ℝ) (hpa : (403/16 : ℝ) ≤ p) (hpb : p ≤ (807/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(403/16 : ℝ) ≤ (41704143/2500000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (41704143/2500000000 : ℝ)) (by norm_num) (by norm_num) 403 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (5041704143/2500000000 : ℝ) ≤ (642650427/625000000 : ℝ)^(403/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (642650427/625000000 : ℝ)) (X := (5041704143/2500000000 : ℝ)) (by norm_num) 403 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (652864113/625000000 : ℝ)^(403/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (652864113/625000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 403 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (403/16 : ℝ)) (beta := (807/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (642650427/625000000 : ℝ)) (aup := (652864113/625000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar135 (p : ℝ) (hpa : (807/32 : ℝ) ≤ p) (hpb : p ≤ (101/4 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(807/32 : ℝ) ≤ (82985753/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (82985753/5000000000 : ℝ)) (by norm_num) (by norm_num) 807 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10082985753/5000000000 : ℝ) ≤ (10282034911/10000000000 : ℝ)^(807/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10282034911/10000000000 : ℝ)) (X := (10082985753/5000000000 : ℝ)) (by norm_num) 807 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10445261239/10000000000 : ℝ)^(807/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10445261239/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 807 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (807/32 : ℝ)) (beta := (101/4 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10282034911/10000000000 : ℝ)) (aup := (10445261239/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar136 (p : ℝ) (hpa : (101/4 : ℝ) ≤ p) (hpb : p ≤ (809/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(101/4 : ℝ) ≤ (1032067/62500000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (1032067/62500000 : ℝ)) (by norm_num) (by norm_num) 101 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (126032067/62500000 : ℝ) ≤ (10281664009/10000000000 : ℝ)^(101/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10281664009/10000000000 : ℝ)) (X := (126032067/62500000 : ℝ)) (by norm_num) 101 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5222349049/5000000000 : ℝ)^(101/4 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5222349049/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 101 4 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (101/4 : ℝ)) (beta := (809/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10281664009/10000000000 : ℝ)) (aup := (5222349049/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar137 (p : ℝ) (hpa : (809/32 : ℝ) ≤ p) (hpb : p ≤ (405/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(809/32 : ℝ) ≤ (82147097/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (82147097/5000000000 : ℝ)) (by norm_num) (by norm_num) 809 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10082147097/5000000000 : ℝ) ≤ (10281294123/10000000000 : ℝ)^(809/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10281294123/10000000000 : ℝ)) (X := (10082147097/5000000000 : ℝ)) (by norm_num) 809 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (10444136379/10000000000 : ℝ)^(809/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10444136379/10000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 809 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (809/32 : ℝ)) (beta := (405/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10281294123/10000000000 : ℝ)) (aup := (10444136379/10000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar138 (p : ℝ) (hpa : (405/16 : ℝ) ≤ p) (hpb : p ≤ (811/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(405/16 : ℝ) ≤ (81730953/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (81730953/5000000000 : ℝ)) (by norm_num) (by norm_num) 405 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10081730953/5000000000 : ℝ) ≤ (10280925249/10000000000 : ℝ)^(405/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10280925249/10000000000 : ℝ)) (X := (10081730953/5000000000 : ℝ)) (by norm_num) 405 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5221788039/5000000000 : ℝ)^(405/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5221788039/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 405 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (405/16 : ℝ)) (beta := (811/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10280925249/10000000000 : ℝ)) (aup := (5221788039/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar139 (p : ℝ) (hpa : (811/32 : ℝ) ≤ p) (hpb : p ≤ (203/8 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(811/32 : ℝ) ≤ (81316917/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (81316917/5000000000 : ℝ)) (by norm_num) (by norm_num) 811 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10081316917/5000000000 : ℝ) ≤ (10280557381/10000000000 : ℝ)^(811/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10280557381/10000000000 : ℝ)) (X := (10081316917/5000000000 : ℝ)) (by norm_num) 811 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2610754297/2500000000 : ℝ)^(811/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2610754297/2500000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 811 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (811/32 : ℝ)) (beta := (203/8 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10280557381/10000000000 : ℝ)) (aup := (2610754297/2500000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar140 (p : ℝ) (hpa : (203/8 : ℝ) ≤ p) (hpb : p ≤ (813/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(203/8 : ℝ) ≤ (161809957/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (161809957/10000000000 : ℝ)) (by norm_num) (by norm_num) 203 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20161809957/10000000000 : ℝ) ≤ (2570047629/2500000000 : ℝ)^(203/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2570047629/2500000000 : ℝ)) (X := (20161809957/10000000000 : ℝ)) (by norm_num) 203 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (2088491941/2000000000 : ℝ)^(203/8 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (2088491941/2000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 203 8 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (203/8 : ℝ)) (beta := (813/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (2570047629/2500000000 : ℝ)) (aup := (2088491941/2000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar141 (p : ℝ) (hpa : (813/32 : ℝ) ≤ p) (hpb : p ≤ (407/16 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(813/32 : ℝ) ≤ (160990253/10000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (160990253/10000000000 : ℝ)) (by norm_num) (by norm_num) 813 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (20160990253/10000000000 : ℝ) ≤ (205596493/200000000 : ℝ)^(813/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (205596493/200000000 : ℝ)) (X := (20160990253/10000000000 : ℝ)) (by norm_num) 813 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (5220951811/5000000000 : ℝ)^(813/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (5220951811/5000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 813 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (813/32 : ℝ)) (beta := (407/16 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (205596493/200000000 : ℝ)) (aup := (5220951811/5000000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar142 (p : ℝ) (hpa : (407/16 : ℝ) ≤ p) (hpb : p ≤ (815/32 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(407/16 : ℝ) ≤ (80087351/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (80087351/5000000000 : ℝ)) (by norm_num) (by norm_num) 407 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10080087351/5000000000 : ℝ) ≤ (10279459779/10000000000 : ℝ)^(407/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10279459779/10000000000 : ℝ)) (X := (10080087351/5000000000 : ℝ)) (by norm_num) 407 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (1305168617/1250000000 : ℝ)^(407/16 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (1305168617/1250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 407 16 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (407/16 : ℝ)) (beta := (815/32 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10279459779/10000000000 : ℝ)) (aup := (1305168617/1250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_scalar143 (p : ℝ) (hpa : (815/32 : ℝ) ≤ p) (hpb : p ≤ (51/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  have ht : (17/20 : ℝ)^(815/32 : ℝ) ≤ (79681641/5000000000 : ℝ) := by
    have h := rpow_le_of_pow_le (x := (17/20 : ℝ)) (X := (79681641/5000000000 : ℝ)) (by norm_num) (by norm_num) 815 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have hA : (10079681641/5000000000 : ℝ) ≤ (10279095897/10000000000 : ℝ)^(815/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (10279095897/10000000000 : ℝ)) (X := (10079681641/5000000000 : ℝ)) (by norm_num) 815 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  have ha : (3 : ℝ) ≤ (261019891/250000000 : ℝ)^(815/32 : ℝ) := by
    have h := le_rpow_of_pow_le (x := (261019891/250000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 815 32 (by norm_num) (by norm_num)
    convert h using 1 <;> norm_num
  apply cyclicConstant_lower_endpoint (alpha := (815/32 : ℝ)) (beta := (51/2 : ℝ))
    (t := (17/20 : ℝ)) (Aup := (10279095897/10000000000 : ℝ)) (aup := (261019891/250000000 : ℝ))
    (by linarith) (by linarith) (by norm_num) hpa hpb (by norm_num)
    (by nlinarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · linarith only [ht, hA]
  · exact ha
  · norm_num
  · norm_num

theorem lower21_chunk08 (p : ℝ) (hpa : (25 : ℝ) ≤ p) (hpb : p ≤ (51/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  rcases le_total p (101/4 : ℝ) with hl | hr
  ·
    rcases le_total p (201/8 : ℝ) with hal | har
    ·
      rcases le_total p (401/16 : ℝ) with haal | haar
      ·
        rcases le_total p (801/32 : ℝ) with haaal | haaar
        ·
          exact lower21_scalar128 p hpa haaal
        ·
          exact lower21_scalar129 p haaar haal
      ·
        rcases le_total p (803/32 : ℝ) with haabl | haabr
        ·
          exact lower21_scalar130 p haar haabl
        ·
          exact lower21_scalar131 p haabr hal
    ·
      rcases le_total p (403/16 : ℝ) with habl | habr
      ·
        rcases le_total p (805/32 : ℝ) with habal | habar
        ·
          exact lower21_scalar132 p har habal
        ·
          exact lower21_scalar133 p habar habl
      ·
        rcases le_total p (807/32 : ℝ) with habbl | habbr
        ·
          exact lower21_scalar134 p habr habbl
        ·
          exact lower21_scalar135 p habbr hl
  ·
    rcases le_total p (203/8 : ℝ) with hbl | hbr
    ·
      rcases le_total p (405/16 : ℝ) with hbal | hbar
      ·
        rcases le_total p (809/32 : ℝ) with hbaal | hbaar
        ·
          exact lower21_scalar136 p hr hbaal
        ·
          exact lower21_scalar137 p hbaar hbal
      ·
        rcases le_total p (811/32 : ℝ) with hbabl | hbabr
        ·
          exact lower21_scalar138 p hbar hbabl
        ·
          exact lower21_scalar139 p hbabr hbl
    ·
      rcases le_total p (407/16 : ℝ) with hbbl | hbbr
      ·
        rcases le_total p (813/32 : ℝ) with hbbal | hbbar
        ·
          exact lower21_scalar140 p hbr hbbal
        ·
          exact lower21_scalar141 p hbbar hbbl
      ·
        rcases le_total p (815/32 : ℝ) with hbbbl | hbbbr
        ·
          exact lower21_scalar142 p hbbr hbbbl
        ·
          exact lower21_scalar143 p hbbbr hpb

end HlawkaSchatten.DiagonalCutoff21

theorem solution (p : ℝ) (hpa : (25 : ℝ) ≤ p) (hpb : p ≤ (51/2 : ℝ)) :
    (273/625 : ℝ)*p < cyclicConstant p := by
  exact HlawkaSchatten.DiagonalCutoff21.lower21_chunk08 p hpa hpb

#print axioms solution
