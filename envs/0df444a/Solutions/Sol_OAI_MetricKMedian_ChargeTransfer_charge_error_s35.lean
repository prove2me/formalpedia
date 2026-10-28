-- Prove2me | solution 1 for OAI.MetricKMedian.ChargeTransfer.charge_error_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:53:47.779933+00:00
-- url     : https://prove2.me/submissions/0362f043-8a59-48b1-994a-832d5945f6be

import Mathlib
import Definitions.Def_OAIQ035K002

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ChargeTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ChargeTransfer

private theorem mul_abs_bound {a b e K : ℝ} (ha : |a| ≤ e) (hb : |b| ≤ K) :
    |a*b| ≤ e*K := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) ((abs_nonneg a).trans ha)

private theorem affine_abs_bound {a b K r w : ℝ} (ha : |a| ≤ K) (hb : |b| ≤ K)
    (hr : 0 ≤ r) : |a*r+b*w^2| ≤ K*(r+w^2) := by
  calc
    |a*r+b*w^2| ≤ |a*r|+|b*w^2| := abs_add_le _ _
    _ = |a| *r+|b| *w^2 := by rw [abs_mul, abs_mul, abs_of_nonneg hr, abs_of_nonneg (sq_nonneg w)]
    _ ≤ K*r+K*w^2 := add_le_add (mul_le_mul_of_nonneg_right ha hr)
      (mul_le_mul_of_nonneg_right hb (sq_nonneg w))
    _ = K*(r+w^2) := by ring

private theorem convex_abs_bound {a b K r : ℝ} (ha : |a| ≤ K) (hb : |b| ≤ K)
    (hr0 : 0 ≤ r) (hr : r ≤ 1) : |(1-r)*a+b*r| ≤ K := by
  calc
    |(1-r)*a+b*r| ≤ |(1-r)*a|+|b*r| := abs_add_le _ _
    _ = (1-r)*|a|+|b| *r := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1-r), abs_of_nonneg hr0]
    _ ≤ (1-r)*K+K*r := add_le_add (mul_le_mul_of_nonneg_left ha (by linarith))
      (mul_le_mul_of_nonneg_right hb hr0)
    _ = K := by ring

private theorem c_bounds {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (s : Bool) :
    1/2 ≤ c p s ∧ c p s ≤ 1 := by
  cases s
  · norm_num [c, bit]
  · norm_num [c, bit]
    constructor <;> linarith

private theorem bit_mul_bounds {p u : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hu0 : 0 ≤ u) (hu : u ≤ 1) (s : Bool) :
    0 ≤ bit s*p*u ∧ bit s*p*u ≤ 1/2 ∧
      0 ≤ (2-bit s)*p*u ∧ (2-bit s)*p*u ≤ 1 := by
  have hc0 : 0 ≤ p*u := mul_nonneg hp0 hu0
  have hc1 := mul_le_mul hp hu hu0 (by norm_num : (0:ℝ) ≤ 1/2)
  cases s
  · norm_num [bit]
    constructor <;> nlinarith
  · norm_num [bit]
    exact ⟨hc0, by linarith, hc0, by linarith⟩

theorem factor_bounds {p a k H x w r : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (ha0 : 1 ≤ a) (ha : a ≤ 2) (hk0 : 0 ≤ k) (hk : k ≤ 1/5)
    (hH0 : 0 ≤ H) (hH : H ≤ 2/5) (hx0 : 0 ≤ x) (hw0 : 0 ≤ w)
    (hxw : x+w ≤ 1) (hr0 : 0 ≤ r) (hr : r ≤ 1) (s : Bool) :
    |F1 p H x w r s| ≤ 2*(r+w^2) ∧ |F2 p a w r s| ≤ 3 ∧
      |F3 p k H r s| ≤ 2 ∧ |F4 p a x w r s| ≤ 3*(r+w^2) := by
  have hx : x ≤ 1 := by linarith
  have hw : w ≤ 1 := by linarith
  have hc := c_bounds hp0 hp s
  have hc0 : 0 ≤ c p s := by linarith
  have hB := bit_mul_bounds hp0 hp (show 0 ≤ x+w by linarith) hxw s
  have hCH0 : 0 ≤ c p s*H := mul_nonneg hc0 hH0
  have hCH := mul_le_mul hc.2 hH hH0 (by norm_num : (0:ℝ) ≤ 1)
  have hF1 : |F1 p H x w r s| ≤ 2*(r+w^2) := by
    apply affine_abs_bound (r := r) (w := w) (hr := hr0)
    · rw [abs_le]; constructor <;> linarith [hB.2.2.1, hB.2.2.2]
    · rw [abs_le]; constructor <;> linarith
  have hPW0 : 0 ≤ p*w := mul_nonneg hp0 hw0
  have hPW := mul_le_mul hp hw hw0 (by norm_num : (0:ℝ) ≤ 1/2)
  have hCP0 : 0 ≤ c p s*p := mul_nonneg hc0 hp0
  have hCP := mul_le_mul hc.2 hp hp0 (by norm_num : (0:ℝ) ≤ 1)
  have hF2 : |F2 p a w r s| ≤ 3 := by
    apply convex_abs_bound (hr0 := hr0) (hr := hr)
    · rw [abs_le]; constructor <;> linarith
    · rw [abs_le]; constructor <;> linarith
  have hHr0 : 0 ≤ H*r := mul_nonneg hH0 hr0
  have hHr := mul_le_mul hH hr hr0 (by norm_num : (0:ℝ) ≤ 2/5)
  have hC1H0 : 0 ≤ c p s*(1-H*r) := mul_nonneg hc0 (by linarith)
  have hC1H := mul_le_mul hc.2 (show 1-H*r ≤ 1 by linarith) (by linarith : 0 ≤ 1-H*r)
    (by norm_num : (0:ℝ) ≤ 1)
  have hK : 0 ≤ (1-bit s)*k ∧ (1-bit s)*k ≤ 1/5 := by
    cases s
    · simpa only [bit, Bool.false_eq_true, ↓reduceIte, sub_zero, one_mul] using And.intro hk0 hk
    · norm_num [bit]
  have hF3 : |F3 p k H r s| ≤ 2 := by
    have hid : F3 p k H r s = c p s*(1-H*r)-(1-bit s)*k := by unfold F3; ring
    rw [hid, abs_le]
    constructor <;> linarith
  have hBX := bit_mul_bounds hp0 hp (show 0 ≤ 1-x by linarith) (show 1-x ≤ 1 by linarith) s
  have hBW := bit_mul_bounds hp0 hp hw0 hw s
  have hF4 : |F4 p a x w r s| ≤ 3*(r+w^2) := by
    apply affine_abs_bound (r := r) (w := w) (hr := hr0)
    · rw [abs_le]; constructor <;> linarith [hBX.1, hBX.2.1, hBW.2.2.1, hBW.2.2.2]
    · rw [abs_le]; constructor <;> linarith
  exact ⟨hF1, hF2, hF3, hF4⟩

theorem factor_differences {p q a b k H x w r e : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (hH0 : 0 ≤ H) (hH : H ≤ 2/5) (hx0 : 0 ≤ x) (hw0 : 0 ≤ w)
    (hxw : x+w ≤ 1) (hr0 : 0 ≤ r) (hr : r ≤ 1)
    (hpq : |p-q| ≤ e) (hab : |a-b| ≤ 2*e) (s : Bool) :
    |F1 p H x w r s-F1 q H x w r s| ≤ 2*e*(r+w^2) ∧
      |F2 p a w r s-F2 q b w r s| ≤ 4*e ∧
      |F3 p k H r s-F3 q k H r s| ≤ e ∧
      |F4 p a x w r s-F4 q b x w r s| ≤ 4*e*(r+w^2) := by
  have he : 0 ≤ e := (abs_nonneg _).trans hpq
  have hw : w ≤ 1 := by linarith
  have hx : x ≤ 1 := by linarith
  have hF1coeff : |-bit s*H-(2-bit s)*(x+w)| ≤ 2 := by
    rw [abs_le]
    constructor <;> cases s <;> norm_num [bit] <;> linarith
  have hF1coefffull := affine_abs_bound hF1coeff (by norm_num : |(8/5:ℝ)| ≤ 2) (w := w) hr0
  have hF1id : F1 p H x w r s-F1 q H x w r s =
      (p-q)*((-bit s*H-(2-bit s)*(x+w))*r+(8/5)*w^2) := by
    dsimp only [F1, c]
    ring
  have hF1 : |F1 p H x w r s-F1 q H x w r s| ≤ 2*e*(r+w^2) := by
    rw [hF1id]
    calc
      _ ≤ e*(2*(r+w^2)) := mul_abs_bound hpq hF1coefffull
      _ = 2*e*(r+w^2) := by ring
  have hCPcoeff : |1-bit s*(p+q)| ≤ 1 := by
    rw [abs_le]
    constructor <;> cases s <;> norm_num [bit] <;> linarith
  have hCPid : c p s*p-c q s*q = (p-q)*(1-bit s*(p+q)) := by unfold c; ring
  have hCPdif : |c p s*p-c q s*q| ≤ 4*e := by
    rw [hCPid]
    have h := mul_abs_bound hpq hCPcoeff
    nlinarith only [h, he]
  have hPWdif : |(p-q)*w| ≤ e := by
    have h := mul_abs_bound hpq (show |w| ≤ 1 by rwa [abs_of_nonneg hw0])
    simpa only [mul_one] using h
  have hinner : |a-b+2*(p-q)*w| ≤ 4*e := by
    have h := abs_add_le (a-b) (2*((p-q)*w))
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at h
    have hid : a-b+2*(p-q)*w = a-b+2*((p-q)*w) := by ring
    rw [hid]
    linarith only [h, hab, hPWdif]
  have hF2id : F2 p a w r s-F2 q b w r s =
      (1-r)*(a-b+2*(p-q)*w)+(c p s*p-c q s*q)*r := by unfold F2; ring
  have hF2 : |F2 p a w r s-F2 q b w r s| ≤ 4*e := by
    rw [hF2id]
    exact convex_abs_bound hinner hCPdif hr0 hr
  have hHr0 : 0 ≤ H*r := mul_nonneg hH0 hr0
  have hHr := mul_le_mul hH hr hr0 (by norm_num : (0:ℝ) ≤ 2/5)
  have hF3coeff : |-bit s*(1-H*r)| ≤ 1 := by
    rw [abs_le]
    constructor <;> cases s <;> norm_num [bit] <;> linarith
  have hF3id : F3 p k H r s-F3 q k H r s = (p-q)*(-bit s*(1-H*r)) := by
    dsimp only [F3, c]
    ring
  have hF3 : |F3 p k H r s-F3 q k H r s| ≤ e := by
    rw [hF3id]
    have h := mul_abs_bound hpq hF3coeff
    simpa only [mul_one] using h
  have hF4coeff : |-bit s*(1-x)-(2-bit s)*w| ≤ 2 := by
    rw [abs_le]
    constructor <;> cases s <;> norm_num [bit] <;> linarith
  have hF4coefffull := affine_abs_bound hF4coeff (by norm_num : |(2/5:ℝ)| ≤ 2) (w := w) hr0
  have hF4id : F4 p a x w r s-F4 q b x w r s =
      -(a-b)*r+(p-q)*((-bit s*(1-x)-(2-bit s)*w)*r+(2/5)*w^2) := by
    unfold F4
    ring
  have hF4 : |F4 p a x w r s-F4 q b x w r s| ≤ 4*e*(r+w^2) := by
    rw [hF4id]
    have h := abs_add_le (-(a-b)*r) ((p-q)*((-bit s*(1-x)-(2-bit s)*w)*r+(2/5)*w^2))
    have hA : |-(a-b)*r| ≤ 2*e*r := mul_abs_bound
      (show |-(a-b)| ≤ 2*e by simpa only [abs_neg] using hab)
      (show |r| ≤ r by rw [abs_of_nonneg hr0])
    have hP := mul_abs_bound hpq hF4coefffull
    have hew := mul_nonneg he (sq_nonneg w)
    nlinarith only [h, hA, hP, hew]
  exact ⟨hF1, hF2, hF3, hF4⟩

private theorem product_difference_bound (a b a' b' : ℝ) :
    |a*b-a'*b'| ≤ |a-a'| *|b|+|a'| *|b-b'| := by
  have hid : a*b-a'*b' = (a-a')*b+a'*(b-b') := by ring
  rw [hid]
  simpa only [abs_mul] using abs_add_le ((a-a')*b) (a'*(b-b'))

theorem charge_error_s35_oai {p q a b k H x w r e : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (ha0 : 1 ≤ a) (ha : a ≤ 2) (hb0 : 1 ≤ b) (hb : b ≤ 2)
    (hk0 : 0 ≤ k) (hk : k ≤ 1/5) (hH0 : 0 ≤ H) (hH : H ≤ 2/5)
    (hx0 : 0 ≤ x) (hw0 : 0 ≤ w) (hxw : x+w ≤ 1) (hr0 : 0 ≤ r) (hr : r ≤ 1)
    (hpq : |p-q| ≤ e) (hab : |a-b| ≤ 2*e) (s : Bool) :
    |charge p a k H x w r s-charge q b k H x w r s| ≤ 25*e*(r+w^2) := by
  have hleft := factor_bounds hp0 hp ha0 ha hk0 hk hH0 hH hx0 hw0 hxw hr0 hr s
  have hright := factor_bounds hq0 hq hb0 hb hk0 hk hH0 hH hx0 hw0 hxw hr0 hr s
  have hdiff := factor_differences (k := k) hp0 hp hq0 hq hH0 hH hx0 hw0 hxw hr0 hr hpq hab s
  have he : 0 ≤ e := (abs_nonneg _).trans hpq
  have hρ : 0 ≤ r+w^2 := add_nonneg hr0 (sq_nonneg w)
  have h12 := product_difference_bound (F1 p H x w r s) (F2 p a w r s)
    (F1 q H x w r s) (F2 q b w r s)
  have h34 := product_difference_bound (F3 p k H r s) (F4 p a x w r s)
    (F3 q k H r s) (F4 q b x w r s)
  have hterm1 := mul_le_mul hdiff.1 hleft.2.1 (abs_nonneg _) (by positivity : 0 ≤ 2*e*(r+w^2))
  have hterm2 := mul_le_mul hright.1 hdiff.2.1 (abs_nonneg _) (by positivity : 0 ≤ 2*(r+w^2))
  have hterm3 := mul_le_mul hdiff.2.2.1 hleft.2.2.2 (abs_nonneg _) he
  have hterm4 := mul_le_mul hright.2.2.1 hdiff.2.2.2 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  have ht := abs_add_le (F1 p H x w r s*F2 p a w r s-F1 q H x w r s*F2 q b w r s)
    (F3 p k H r s*F4 p a x w r s-F3 q k H r s*F4 q b x w r s)
  have hid : charge p a k H x w r s-charge q b k H x w r s =
      (F1 p H x w r s*F2 p a w r s-F1 q H x w r s*F2 q b w r s) +
      (F3 p k H r s*F4 p a x w r s-F3 q k H r s*F4 q b x w r s) := by unfold charge; ring
  rw [hid]
  nlinarith only [h12, h34, ht, hterm1, hterm2, hterm3, hterm4]

end MetricKMedian.ChargeTransfer


end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.ChargeTransfer.charge_error_s35_oai := @OAI.MetricKMedian.ChargeTransfer.charge_error_s35_oai
