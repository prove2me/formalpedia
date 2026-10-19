-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff32.envelope_certificate_sound
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:21:13.451238+00:00
-- url     : https://prove2.me/submissions/ac08e0b7-7162-49cd-bac0-a54b14bbf7db

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalCutoff32_EnvelopeBounds
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
set_option autoImplicit false

/-
Scalar estimates on the window 32 ≤ p ≤ 50.

Adapted from the scalar section for the window [50,62], which builds on
Ezzeri Esa's Apache-2.0 formalization of the diagonal construction.

The witness is t = (3/(4p))^{1/p}. Writing x = 1/p, the cyclic numerator and
denominator at the witness are bounded by explicit polynomials in x
(`Nlo`, `Dup`), the envelope deficit by `Glo`, and the two resulting
polynomial certificates are checked on x ∈ [1/50, 1/32] by expansion around
x = 1/32 (the tight end), using the hints `s^k ≤ h^(k-1) s` on `s ∈ [0, h]`.
The bound `log p ≤ log(135/4) + 4p/135 - 1` (tangent at p = 135/4) is used
uniformly over the whole window. The upper bound `p/2` uses a quadratic lower
bound for `2^{1/p}`. The file is self-contained.

The second part proves sharpened envelope bounds `scalarEnvelope p q < cyclicConstant p`
on eight sub-slabs of [32, 50] (`envelope_1` … `envelope_8`). On [40, 42] the value
q = 0.3768 is not admissible (at p = 40 the envelope exceeds the cyclic constant), so
that slab is proved with q = 37682/100000 (`envelope_6_q37682`).
-/

namespace HlawkaSchatten.DiagonalCutoff32

open HlawkaSchatten.DiagonalConstruction

/-! ### Elementary analytic bounds -/

lemma exp_quartic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1+x+x^2/2+x^3/6+x^4/12 := by
  have h := Real.exp_bound' hx hx1 (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [pow_nonneg hx 4]

lemma cyclicB_nonneg (p t : ℝ) : 0 ≤ cyclicB p t := by
  unfold cyclicB
  positivity

lemma cyclicA_nonneg (p : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ cyclicA p t := by
  unfold cyclicA
  have := Real.rpow_nonneg ht p
  positivity

lemma cyclicB_rpow {p : ℝ} (hp : 0 < p) (t : ℝ) :
    cyclicB p t ^ p = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
  rw [cyclicB, ← Real.rpow_mul (by positivity :
    0 ≤ 2 * |1 - t| ^ p + (2 : ℝ) ^ p), one_div_mul_cancel hp.ne', Real.rpow_one]

lemma cyclicA_rpow {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    cyclicA p t ^ p = t ^ p + 2 := by
  rw [cyclicA, ← Real.rpow_mul (by positivity : 0 ≤ t ^ p + 2),
    one_div_mul_cancel hp.ne', Real.rpow_one]

lemma cyclicB_ge_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  apply (Real.rpow_le_rpow_iff (by norm_num) (cyclicB_nonneg p t) hp).mp
  rw [cyclicB_rpow hp]
  have hn := Real.rpow_nonneg (abs_nonneg (1 - t)) p
  linarith

/-- Positivity of the cyclic denominator (proved here for `1 < p`, `0 ≤ t`). -/
lemma denominator_pos {p t : ℝ} (hp : 1 < p) (ht : 0 ≤ t) :
    0 < 6 * cyclicA p t - 3 * cyclicB p t := by
  have hp0 : 0 < p := by linarith
  have habs : |1 - t| ^ p ≤ 1 + t ^ p := by
    rcases le_total t 1 with h | h
    · have h1 : |1 - t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have := Real.rpow_le_rpow (abs_nonneg _) h1 hp0.le
      rw [Real.one_rpow] at this
      linarith [Real.rpow_nonneg ht p]
    · have h1 : |1 - t| ≤ t := abs_le.mpr ⟨by linarith, by linarith⟩
      have := Real.rpow_le_rpow (abs_nonneg _) h1 hp0.le
      linarith
  have htwo : (2 : ℝ) < 2 ^ p := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp
    simpa using this
  have htp : 0 ≤ t ^ p := Real.rpow_nonneg ht p
  have hlt : cyclicB p t ^ p < (2 * cyclicA p t) ^ p := by
    rw [Real.mul_rpow (by norm_num) (cyclicA_nonneg p ht), cyclicA_rpow hp0 ht, cyclicB_rpow hp0]
    nlinarith
  have hBA : cyclicB p t < 2 * cyclicA p t :=
    (Real.rpow_lt_rpow_iff (cyclicB_nonneg p t)
      (by have := cyclicA_nonneg p ht; positivity) hp0).mp hlt
  linarith

/-! ### The witness `(3/(4p))^{1/p}` -/

/-- The cyclic witness `(3/(4p))^{1/p}`. -/
noncomputable def witness (p : ℝ) : ℝ :=
  Real.exp (-((Real.log p - Real.log (3 / 4)) * p⁻¹))

lemma inverse_bounds {p : ℝ} (hp : 32 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1/32 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩

lemma inverse_lower {p : ℝ} (hp : 32 ≤ p) (hhi : p ≤ 50) : 1/50 ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hhi

lemma cyclicA_lower {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    1 + (693 / 1000 : ℝ) * (1 / p) + (693 / 1000 : ℝ) ^ 2 / 2 * (1 / p) ^ 2 ≤
      cyclicA p t := by
  have hx0 : 0 ≤ 1 / p := one_div_nonneg.mpr hp.le
  have hlog : (693 / 1000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_right hlog hx0
  have hy0 : 0 ≤ (693 / 1000 : ℝ) * (1 / p) := by positivity
  have he := Real.quadratic_le_exp_of_nonneg (mul_nonneg (Real.log_nonneg
    (by norm_num : (1 : ℝ) ≤ 2)) hx0)
  have hsq := pow_le_pow_left₀ hy0 hm 2
  have hr : 1 + (693 / 1000 : ℝ) * (1 / p) + (693 / 1000 : ℝ) ^ 2 / 2 * (1 / p) ^ 2 ≤
      (2 : ℝ) ^ (1 / p) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have : ((693 / 1000 : ℝ) * (1 / p)) ^ 2 = (693 / 1000 : ℝ) ^ 2 * (1 / p) ^ 2 := by ring
    linarith
  exact hr.trans (Real.rpow_le_rpow (by norm_num)
    (by linarith [Real.rpow_nonneg ht p]) hx0)

lemma cyclicB_upper {p t : ℝ} (hp : 32 ≤ p) (ht : t ∈ Set.Icc (1 / 2) 2) :
    cyclicB p t ≤ 2 + (1 / p) / 1000000 := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 ≤ 1 / p := by positivity
  have hx1 : 1 / p ≤ 1 := (div_le_iff₀ hp0).mpr (by linarith)
  have habs : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpow : (2 : ℝ) ^ p ≥ 4194304 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (22 : ℝ) ≤ p by linarith)
    norm_num at h
    linarith
  have htwo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have htail : 4 / (2 : ℝ) ^ p ≤ 1 / 1000000 := by
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

lemma cyclicRatio_le_half_exponent {p t : ℝ} (hp : 32 ≤ p)
    (ht : t ∈ Set.Icc (1 / 2) 2) : cyclicRatio p t ≤ p / 2 := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hden := denominator_pos (show 1 < p by linarith) ht0
  have hA := cyclicA_lower (t := t) hp0 ht0
  have hB := cyclicB_upper hp ht
  have hthree : 1 ≤ (3 : ℝ) ^ (1/p) := Real.one_le_rpow (by norm_num) (by positivity)
  have hnum : 3 * cyclicA p t - (3 : ℝ) ^ (1/p) * |2-t| ≤ 4 * cyclicA p t - 2 := by
    have htA : t ≤ cyclicA p t := by
      have h := Real.rpow_le_rpow (Real.rpow_nonneg ht0 p)
        (show t ^ p ≤ t ^ p + 2 by linarith) (one_div_nonneg.mpr hp0.le)
      rw [← Real.rpow_mul ht0, mul_one_div_cancel hp0.ne', Real.rpow_one] at h
      exact h
    have h := mul_le_mul_of_nonneg_right hthree (abs_nonneg (2-t))
    rw [abs_of_nonneg (by linarith [ht.2])] at h
    rw [abs_of_nonneg (by linarith [ht.2])]
    nlinarith
  set x := 1 / p with hxdef
  have hpx : p * x = 1 := mul_one_div_cancel hp0.ne'
  have hx0 : 0 ≤ x := by positivity
  have hx : x ≤ 1 / 32 := one_div_le_one_div_of_le (by norm_num) hp
  have hkey : 2 + 1/1000 ≤ (3*p-4) * ((693 / 1000 : ℝ) * x + (693 / 1000 : ℝ) ^ 2 / 2 * x ^ 2) := by
    have hid : (3*p-4) * ((693 / 1000 : ℝ) * x + (693 / 1000 : ℝ) ^ 2 / 2 * x ^ 2) =
        3 * (693 / 1000) + (3 * (693 / 1000 : ℝ) ^ 2 / 2 - 4 * (693 / 1000)) * x -
          2 * (693 / 1000 : ℝ) ^ 2 * x ^ 2 := by
      linear_combination (3 * (693 / 1000 : ℝ) + 3 * (693 / 1000 : ℝ) ^ 2 / 2 * x) * hpx
    rw [hid]
    nlinarith
  have hAl := mul_le_mul_of_nonneg_left hA (show 0 ≤ 3*p-4 by linarith)
  have hBu := mul_le_mul_of_nonneg_left hB (show 0 ≤ 3*p/2 by positivity)
  have hfinal : 4 * cyclicA p t - 2 ≤ (p/2) * (6 * cyclicA p t - 3 * cyclicB p t) := by
    have hpx' : (3*p/2) * (2 + x / 1000000) = 3*p + 3/2000000 := by
      linear_combination (3/2000000 : ℝ) * hpx
    nlinarith
  exact (div_le_iff₀ hden).mpr (hnum.trans hfinal)

lemma cyclicRatio_bddAbove {p : ℝ} (hp : 32 ≤ p) :
    BddAbove (cyclicRatio p '' Set.Icc (1 / 2 : ℝ) 2) := by
  refine ⟨p / 2, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact cyclicRatio_le_half_exponent hp ht

lemma cyclicRatio_le_constant {p t : ℝ} (hp : 32 ≤ p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p :=
  le_csSup (cyclicRatio_bddAbove hp) (Set.mem_image_of_mem (cyclicRatio p) ht)

lemma exp_neg_quintic_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1-x+x^2/2-x^3/6+x^4/24-x^5/100 ≤ Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (n := 5)
    (by simpa only [abs_neg, abs_of_nonneg hx] using hx1) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx] at hh
  nlinarith [pow_nonneg hx 5]

lemma one_sub_exp_neg_quintic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x-x^2/2+x^3/6-x^4/24-x^5/100 ≤ 1-Real.exp (-x) := by
  have h := Real.exp_bound (x := -x) (n := 5)
    (by simpa only [abs_neg, abs_of_nonneg hx] using hx1) (by norm_num)
  have hh := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx] at hh
  nlinarith [pow_nonneg hx 5]

lemma exp_cubic_lower {x : ℝ} (hx : 0 ≤ x) :
    1+x+x^2/2+x^3/6 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma log_one_add_cubic {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/6) :
    u-u^2/2 ≤ Real.log (1+u) ∧ Real.log (1+u) ≤ u-u^2/2+u^3/3+2*u^4 := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -u) (by rw [abs_neg, abs_of_nonneg hu]; linarith) 3
  norm_num [Finset.sum_range_succ, abs_of_nonneg hu] at h
  have hd : 0 < 1-u := by linarith
  have he : u^4/(1-u) ≤ 2*u^4 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (pow_nonneg hu 4) (show 0 ≤ 1-2*u by linarith)]
  have h4 : 2*u^4 ≤ u^3/3 := by nlinarith [pow_nonneg hu 3]
  have hh := abs_le.mp h
  constructor <;> nlinarith [hh.1, hh.2]

/-- The cyclic witness `(c/p)^{1/p}`. -/
noncomputable def witG (c p : ℝ) : ℝ :=
  Real.exp (-((Real.log p - Real.log c) * p⁻¹))

lemma witG_power {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    witG c p ^ p = c * p⁻¹ := by
  rw [witG, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : -((Real.log p - Real.log c) * p⁻¹) * p = Real.log c - Real.log p := by
    field_simp
    ring
  rw [he, Real.exp_sub, Real.exp_log hp, Real.exp_log hc]
  field_simp

/-- Tangent bound for `log p` at `p = a`, for the witness constant `c = a/n`. -/
lemma witG_tangent {a n ℓ p : ℝ} (ha : 0 < a) (hn : 0 < n) (hp : 0 < p)
    (hℓ : Real.log n ≤ ℓ) :
    (Real.log p - Real.log (a / n)) * p⁻¹ ≤ (ℓ - 1) * p⁻¹ + 1 / a := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < p / a by positivity)
  rw [Real.log_div hp.ne' ha.ne'] at h1
  rw [Real.log_div ha.ne' hn.ne']
  have hb : Real.log p - (Real.log a - Real.log n) ≤ ℓ - 1 + p / a := by linarith
  have hm := mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr hp.le)
  have he : (ℓ - 1 + p / a) * p⁻¹ = (ℓ - 1) * p⁻¹ + 1 / a := by
    field_simp
  linarith

lemma cyclicA_expG {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    cyclicA p (witG c p) = Real.exp (Real.log (2+c*p⁻¹)*p⁻¹) := by
  rw [cyclicA, witG_power hc hp, add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]







set_option maxHeartbeats 4000000 in
lemma numerator_lowerG {c Zc Zk p : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hp : 32 ≤ p)
    (hZc : 0 ≤ Zc) (hZk : 0 ≤ Zk)
    (hZ : (Real.log p - Real.log c) * p⁻¹ ≤ Zc * p⁻¹ + Zk)
    (hZ1 : Zc * p⁻¹ + Zk ≤ 1/5) :
    NloG c Zc Zk p⁻¹ ≤ 3*cyclicA p (witG c p)-(3 : ℝ)^(1/p)*|2-witG c p| ∧
      1/2 ≤ witG c p ∧ witG c p ≤ 1 := by
  have hp0 : 0 < p := by linarith
  set x := p⁻¹ with hxdef
  have hi := inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have hlc : 0 ≤ Real.log p - Real.log c := by
    linarith [Real.log_nonneg (show 1 ≤ p by linarith), Real.log_nonpos hc0.le hc1]
  have hw1 : witG c p ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hlc hx0))
  let C : ℝ := 1098612289/10^9*x
  let Z : ℝ := Zc*x+Zk
  have hc0' : 0 ≤ C := by dsimp [C]; positivity
  have hc1' : C ≤ 1 := by dsimp [C]; linarith [hi.2]
  have hz0 : 0 ≤ Z := by dsimp [Z]; positivity
  have hz1 : Z ≤ 1 := by dsimp [Z]; linarith
  have hroot : (3 : ℝ)^(1/p) = Real.exp (Real.log 3*x) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div]
  have hc : Real.log 3*x ≤ C := by
    apply mul_le_mul_of_nonneg_right _ hx0
    linarith [Real.log_three_lt_d9]
  have hr := (Real.exp_le_exp.mpr hc).trans (exp_quartic hc0' hc1')
  have hw : Real.exp (-Z) ≤ witG c p := by
    apply Real.exp_le_exp.mpr
    dsimp [Z]
    linarith
  have hw2 : 1/2 ≤ witG c p := by
    have h := Real.add_one_le_exp (-Z)
    dsimp [Z] at h hw
    linarith
  have htup : 2-witG c p ≤ 1+Z-Z^2/2+Z^3/6-Z^4/24+Z^5/100 := by
    have h := exp_neg_quintic_lower hz0 hz1
    linarith
  have habs : |2-witG c p| = 2-witG c p := abs_of_nonneg (by linarith)
  have hZpos : 0 ≤ 1+Z-Z^2/2+Z^3/6-Z^4/24+Z^5/100 := by
    have h2 : Z^2 ≤ Z := by rw [sq]; exact mul_le_of_le_one_right hz0 hz1
    have h4 : Z^4 ≤ Z := by
      rw [show Z^4 = Z * Z^3 by ring]; exact mul_le_of_le_one_right hz0 (pow_le_one₀ hz0 hz1)
    linarith [pow_nonneg hz0 3, pow_nonneg hz0 5]
  have hprod := mul_le_mul hr htup (show 0 ≤ 2-witG c p by linarith)
    (show 0 ≤ 1+C+C^2/2+C^3/6+C^4/12 by positivity)
  set u := c/2*x with hudef
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1/6 := by
    have : c/2*x ≤ 1/2*(1/32) := mul_le_mul (by linarith) hi.2 hx0 (by norm_num)
    linarith
  have hlog := (log_one_add_cubic hu0 hu1).1
  have hsplit : Real.log (2+c*x) = Real.log 2 + Real.log (1+u) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    rw [hudef]; ring
  have ha : 6931471803/10^10+u-u^2/2 ≤ Real.log (2+c*x) := by
    rw [hsplit]; linarith [Real.log_two_gt_d9]
  have hA := exp_cubic_lower
    (mul_nonneg (Real.log_nonneg (by have := mul_nonneg hc0.le hx0; linarith : (1 : ℝ) ≤ 2+c*x)) hx0)
  rw [← cyclicA_expG hc0 hp0] at hA
  have hy0 : 0 ≤ (6931471803/10^10+u-u^2/2)*x := by
    apply mul_nonneg _ hx0
    have h : u^2 ≤ u*(1/6) := by rw [sq]; exact mul_le_mul_of_nonneg_left hu1 hu0
    linarith
  have hyy := mul_le_mul_of_nonneg_right ha hx0
  have hAmono : 1+(6931471803/10^10+u-u^2/2)*x+((6931471803/10^10+u-u^2/2)*x)^2/2
      +((6931471803/10^10+u-u^2/2)*x)^3/6 ≤
      1+Real.log (2+c*x)*x+(Real.log (2+c*x)*x)^2/2+(Real.log (2+c*x)*x)^3/6 := by
    have h2 := pow_le_pow_left₀ hy0 hyy 2
    have h3 := pow_le_pow_left₀ hy0 hyy 3
    linarith
  refine ⟨?_, hw2, hw1⟩
  rw [hroot,habs]
  dsimp only [NloG]
  dsimp [C,Z] at hprod
  rw [← hudef]
  linarith

set_option maxHeartbeats 4000000 in
lemma denominator_upperG {c p : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hp : 32 ≤ p) :
    6*cyclicA p (witG c p)-3*cyclicB p (witG c p) ≤ DupG c p⁻¹ := by
  have hp0 : 0 < p := by linarith
  set x := p⁻¹ with hxdef
  have hi := inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  set u := c/2*x with hudef
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 1/64 := by
    have : c/2*x ≤ 1/2*(1/32) := mul_le_mul (by linarith) hi.2 hx0 (by norm_num)
    linarith
  have hlog := (log_one_add_cubic hu0 (by linarith)).2
  have hsplit : Real.log (2+c*x) = Real.log 2 + Real.log (1+u) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    rw [hudef]; ring
  have ha : Real.log (2+c*x) ≤ 6931471808/10^10+u-u^2/2+u^3/3+2*u^4 := by
    rw [hsplit]; linarith [Real.log_two_lt_d9]
  have hy0 : 0 ≤ Real.log (2+c*x)*x :=
    mul_nonneg (Real.log_nonneg (by nlinarith)) hx0
  let T : ℝ := (6931471808/10^10+u-u^2/2+u^3/3+2*u^4)*x
  have hyy : Real.log (2+c*x)*x ≤ T := mul_le_mul_of_nonneg_right ha hx0
  have ht0 : 0 ≤ T := hy0.trans hyy
  have ht1 : T ≤ 1 := by
    have hinner : 6931471808/10^10+u-u^2/2+u^3/3+2*u^4 ≤ 1 := by
      nlinarith [pow_le_pow_left₀ hu0 hu1 2, pow_le_pow_left₀ hu0 hu1 3,
        pow_le_pow_left₀ hu0 hu1 4, pow_nonneg hu0 2]
    have h := mul_le_mul hinner hi.2 hx0 (by norm_num)
    dsimp [T]
    linarith
  have hE := (Real.exp_le_exp.mpr hyy).trans (exp_quartic ht0 ht1)
  rw [← cyclicA_expG hc0 hp0] at hE
  have hB := cyclicB_ge_two (t := witG c p) hp0
  dsimp only [DupG]
  rw [← hudef]
  dsimp [T] at hE
  linarith

lemma GloG_pos {x : ℝ} (hlo : 0 < x) (hhi : x ≤ 1/32) : 0 < GloG x := by
  have hx2 := pow_le_pow_left₀ hlo.le hhi 2
  set g := (6931471803/10^10-x^2/10^6)*x with hg
  set w := (6931471808/10^10 : ℝ)*x with hw
  have hg0 : 0 ≤ g := by
    apply mul_nonneg _ hlo.le
    nlinarith
  have hgw : w - g ≤ x^3/10^6 + x/10^9 := by
    rw [hg, hw]; nlinarith
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1/40 := by rw [hw]; linarith
  have hw2 := pow_le_pow_left₀ hw0 hw1 2
  have hw3 := pow_le_pow_left₀ hw0 hw1 3
  have hw4 := pow_le_pow_left₀ hw0 hw1 4
  have hgl : (6931/10^4) * x ≤ g := by rw [hg]; nlinarith
  dsimp only [GloG]
  rw [← hg, ← hw]
  nlinarith [pow_nonneg hg0 3, mul_le_mul_of_nonneg_left hw4 hw0,
    mul_le_mul_of_nonneg_left hw1 hw0, mul_le_mul_of_nonneg_left hw3 hw0]

lemma envelope_deficitG {p q : ℝ} (hp : 32 ≤ p) (hp' : p ≤ 50) (hq0 : 0 < q)
    (hq : q ≤ 2/5) :
    GloG p⁻¹ < 1-scalarEnvelopeRoot p q := by
  have hp0 : 0 < p := by linarith
  have hi := inverse_bounds hp
  have hi' := inverse_lower hp hp'
  set x := p⁻¹ with hxdef
  let a := q^p
  have ha0 : 0 ≤ a := Real.rpow_nonneg hq0.le p
  have ha : a < x^2/10^6 := by
    have h1 : q^p ≤ (2/5 : ℝ)^p := Real.rpow_le_rpow hq0.le hq hp0.le
    have h2 : (2/5 : ℝ)^p ≤ (2/5 : ℝ)^(32 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hp
    have h3 : (2/5 : ℝ)^(32 : ℝ) = (2/5)^(32 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    have h4 := pow_le_pow_left₀ (by norm_num) hi' 2
    dsimp [a]
    rw [h3] at h2
    norm_num at h2 h4 ⊢
    linarith
  let d := Real.log 2-Real.log (1+a)
  have hdLower : Real.log 2-x^2/10^6 < d := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1+a by positivity)
    dsimp [d]
    linarith
  have hdUpper : d ≤ Real.log 2 := by
    have h := Real.log_nonneg (show 1 ≤ 1+a by linarith)
    dsimp [d]
    linarith
  have hL : (6931471803/10^10 : ℝ) < Real.log 2 ∧ Real.log 2 <6931471808/10^10 := by
    constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9]
  have hx2 : x^2/10^6 ≤ 1/10^6 := by nlinarith [hi.1,hi.2]
  have hd0 : 0 ≤ d := by linarith [hL.1]
  have hdx0 : 0 ≤ d*x := mul_nonneg hd0 hi.1.le
  have hdx1 : d*x ≤ 1 := by nlinarith [hL.2,hi.2]
  have he := one_sub_exp_neg_quintic hdx0 hdx1
  have hdx : d*x ≤ 6931471808/10^10*x :=
    mul_le_mul_of_nonneg_right (by linarith) hi.1.le
  have hsq := pow_le_pow_left₀ hdx0 hdx 2
  have hfour := pow_le_pow_left₀ hdx0 hdx 4
  have hfive := pow_le_pow_left₀ hdx0 hdx 5
  have hgl : (6931471803/10^10-x^2/10^6)*x < d*x :=
    mul_lt_mul_of_pos_right (by linarith) hi.1
  have hg0 : 0 ≤ (6931471803/10^10-x^2/10^6)*x := by
    apply mul_nonneg _ hi.1.le
    linarith [hL.1]
  have hcube := pow_le_pow_left₀ hg0 hgl.le 3
  have hroot : scalarEnvelopeRoot p q = Real.exp (-(d*x)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d,a]
    simp only [one_div,hxdef]
    ring
  rw [hroot]
  dsimp only [GloG]
  linarith

/-- Generic envelope comparison on a sub-slab, given a polynomial certificate. -/
lemma envelope_ltG {a b n ℓ q p : ℝ} (ha : 32 ≤ a) (hb : b ≤ 50) (hn : 0 < n) (han : a ≤ n)
    (hℓ : Real.log n ≤ ℓ) (hℓ1 : 1 ≤ ℓ) (hℓ5 : (ℓ - 1) * (1/32) + 1/a ≤ 1/5)
    (hq0 : 0 < q) (hq : q ≤ 2/5)
    (hcert : ∀ x : ℝ, 1/b ≤ x → x ≤ 1/a →
      (1 - q) * DupG (a/n) x < NloG (a/n) (ℓ - 1) (1/a) x * (2 * GloG x))
    (hp : a ≤ p) (hp' : p ≤ b) :
    scalarEnvelope p q < cyclicConstant p := by
  have hp32 : 32 ≤ p := by linarith
  have hp50 : p ≤ 50 := by linarith
  have hp0 : 0 < p := by linarith
  have ha0 : 0 < a := by linarith
  have hi := inverse_bounds hp32
  have hxa : p⁻¹ ≤ 1/a := by rw [← one_div]; exact one_div_le_one_div_of_le ha0 hp
  have hxb : 1/b ≤ p⁻¹ := by rw [← one_div]; exact one_div_le_one_div_of_le hp0 hp'
  have hc0 : 0 < a/n := by positivity
  have hc1 : a/n ≤ 1 := (div_le_one hn).mpr han
  have hZ := witG_tangent ha0 hn hp0 hℓ
  have hZ1 : (ℓ - 1) * p⁻¹ + 1/a ≤ 1/5 := by
    have := mul_le_mul_of_nonneg_left hi.2 (show 0 ≤ ℓ - 1 by linarith)
    linarith
  have hnum := numerator_lowerG hc0 hc1 hp32 (by linarith) (by positivity) hZ hZ1
  have hd := denominator_upperG hc0 hc1 hp32
  have hD := denominator_pos (show 1 < p by linarith) (show 0 ≤ witG (a/n) p by linarith [hnum.2.1])
  have hg := envelope_deficitG hp32 hp50 hq0 hq
  have hc := hcert p⁻¹ hxb hxa
  have hG0 := GloG_pos hi.1 hi.2
  have hDup : 0 < DupG (a/n) p⁻¹ := lt_of_lt_of_le hD hd
  have hN0 : 0 < NloG (a/n) (ℓ - 1) (1/a) p⁻¹ := by
    have h1 : 0 < (1 - q) * DupG (a/n) p⁻¹ := mul_pos (by linarith) hDup
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg (show 0 ≤ 2 * GloG p⁻¹ by linarith)
    linarith
  have henvD : 0 < 2 * (1 - scalarEnvelopeRoot p q) := by linarith
  have hr : scalarEnvelope p q < cyclicRatio p (witG (a/n) p) := by
    rw [scalarEnvelope, cyclicRatio, div_lt_div_iff₀ henvD hD]
    calc
      _ ≤ (1 - q) * DupG (a/n) p⁻¹ :=
        mul_le_mul_of_nonneg_left hd (by linarith)
      _ < NloG (a/n) (ℓ - 1) (1/a) p⁻¹ * (2 * GloG p⁻¹) := hc
      _ ≤ (3 * cyclicA p (witG (a/n) p) -
          (3 : ℝ) ^ (1 / p) * |2 - witG (a/n) p|) *
          (2 * (1 - scalarEnvelopeRoot p q)) :=
        mul_le_mul hnum.1 (by linarith) (by linarith) (hN0.le.trans hnum.1)
  exact hr.trans_le (cyclicRatio_le_constant hp32 ⟨hnum.2.1, by linarith [hnum.2.2]⟩)

end HlawkaSchatten.DiagonalCutoff32

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff32

theorem solution : ∀ a b n ℓ q p : ℝ, 32 ≤ a → b ≤ 50 → 0 < n → a ≤ n →
    Real.log n ≤ ℓ → 1 ≤ ℓ → (ℓ - 1) * (1/32) + 1/a ≤ 1/5 → 0 < q → q ≤ 2/5 →
    (∀ x : ℝ, 1/b ≤ x → x ≤ 1/a →
      (1 - q) * DupG (a/n) x < NloG (a/n) (ℓ - 1) (1/a) x * (2 * GloG x)) →
    a ≤ p → p ≤ b → scalarEnvelope p q < cyclicConstant p :=
  fun a b n ℓ q p ha hb hn han hℓ hℓ1 hℓ5 hq0 hq hcert hp hp' =>
    HlawkaSchatten.DiagonalCutoff32.envelope_ltG ha hb hn han hℓ hℓ1 hℓ5 hq0 hq hcert hp hp'
