-- Prove2me | solution 1 for LonelyRunner.CoprimeReplacements.not_covered
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:55:05.352986+00:00
-- url     : https://prove2.me/submissions/20c35324-8048-4a59-87c2-9d67e7761595

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

namespace LonelyRunner



theorem ndist_eq_norm (x : ℝ) : ndist x = ‖(x : UnitAddCircle)‖ :=
  UnitAddCircle.norm_eq.symm





theorem ndist_eq_min_fract (x : ℝ) : ndist x = min (Int.fract x) (1 - Int.fract x) :=
  abs_sub_round_eq_min x

/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m

@[simp] theorem ndist_add_int (x : ℝ) (m : ℤ) : ndist (x + m) = ndist x := by
  simp only [ndist, round_add_intCast, Int.cast_add]
  ring_nf

@[simp] theorem ndist_int_add (x : ℝ) (m : ℤ) : ndist (m + x) = ndist x := by
  rw [add_comm, ndist_add_int]



@[simp] theorem ndist_neg (x : ℝ) : ndist (-x) = ndist x := by
  rw [ndist_eq_norm, ndist_eq_norm, AddCircle.coe_neg, norm_neg]







/-- On `[0, 1/2]` the distance to the nearest integer is the identity. -/
theorem ndist_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : ndist x = x := by
  have hfr : Int.fract x = x := Int.fract_eq_self.2 ⟨h0, by linarith⟩
  rw [ndist_eq_min_fract, hfr]
  exact min_eq_left (by linarith)

@[simp] theorem ndist_half : ndist (1 / 2) = 1 / 2 := ndist_of_mem (by norm_num) le_rfl

















end LonelyRunner

namespace LonelyRunner.BadCover

theorem continuous_ndist : Continuous ndist := by
  have heq : ndist = fun x : ℝ => ‖(x : UnitAddCircle)‖ := funext ndist_eq_norm
  rw [heq]
  exact continuous_norm.comp (AddCircle.continuous_mk' (1 : ℝ))

theorem band_center_unique {x δ : ℝ} {c d : ℤ} (hδ : 2 * δ < 1)
    (hc : |x - c| ≤ δ) (hd : |x - d| ≤ δ) : c = d := by
  have hc' := abs_le.mp hc
  have hd' := abs_le.mp hd
  have hh : |(c : ℝ) - d| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hhZ : |c - d| < 1 := by exact_mod_cast hh
  have := abs_lt.mp hhZ
  omega

theorem strict_of_between {x δ : ℝ} {m : ℤ}
    (hl : (m : ℝ) + δ < x) (hu : x < m + 1 - δ) : δ < ndist x := by
  change δ < |x - (round x : ℤ)|
  rcases le_or_gt (round x) m with h | h
  · have hR : ((round x : ℤ) : ℝ) ≤ m := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (le_abs_self _)
  · have hR : (m : ℝ) + 1 ≤ (round x : ℤ) := by exact_mod_cast h
    exact lt_of_lt_of_le (by linarith) (neg_le_abs _)

/-- A whole interval of bad times for one positive speed stays in one band. -/
theorem single_band {A B w δ : ℝ} (hw : 0 < w) (hδ : δ < 1 / 2)
    (hAB : A ≤ B) (hcover : ∀ t ∈ Set.Icc A B, ndist (w * t) ≤ δ) :
    ∃ k : ℤ, ∀ t ∈ Set.Icc A B, |w * t - k| ≤ δ := by
  let k : ℤ := round (w * A)
  have hA : |w * A - k| ≤ δ := hcover A ⟨le_rfl, hAB⟩
  have hAl := (abs_le.mp hA).1
  have hAu := (abs_le.mp hA).2
  have hB : w * B < k + 1 / 2 := by
    by_contra! hb
    let t := ((k : ℝ) + 1 / 2) / w
    have ht : t ∈ Set.Icc A B := by
      dsimp [t]
      constructor
      · apply (le_div_iff₀ hw).mpr
        nlinarith
      · apply (div_le_iff₀ hw).mpr
        nlinarith
    have hc := hcover t ht
    have hwt : w * t = k + 1 / 2 := by dsimp [t]; field_simp
    rw [hwt, ndist_int_add, ndist_half] at hc
    linarith
  refine ⟨k, fun t ht => ?_⟩
  have hround : round (w * t) = k := by
    apply round_eq_iff.mpr
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left ht.1 hw.le,
      mul_le_mul_of_nonneg_left ht.2 hw.le]
  simpa only [ndist, hround] using hcover t ht

theorem single_band_length {A B w δ : ℝ} (hw : 0 < w) (hδ : δ < 1 / 2)
    (hAB : A ≤ B) (hcover : ∀ t ∈ Set.Icc A B, ndist (w * t) ≤ δ) :
    w * (B - A) ≤ 2 * δ := by
  obtain ⟨k, hk⟩ := single_band hw hδ hAB hcover
  have ha := abs_le.mp (hk A ⟨le_rfl, hAB⟩)
  have hb := abs_le.mp (hk B ⟨hAB, le_rfl⟩)
  nlinarith [ha.1, hb.2]

/-- In a two-speed covered interval, two distinct slow-speed bands cannot occur. -/
theorem no_two_slow_bands {A B p q δ u v : ℝ} {c d : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5 * δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p * t) ≤ δ ∨ ndist (q * t) ≤ δ)
    (hu : u ∈ Set.Icc A B) (hv : v ∈ Set.Icc A B)
    (hcu : |p * u - c| ≤ δ) (hdv : |p * v - d| ≤ δ) (hcd : c < d) : False := by
  have hcdR : (c : ℝ) + 1 ≤ d := by exact_mod_cast hcd
  have hcu' := abs_le.mp hcu
  have hdv' := abs_le.mp hdv
  let x := ((c : ℝ) + 3 * δ / 2) / p
  let y := ((c : ℝ) + 1 - 3 * δ / 2) / p
  have hpx : p * x = c + 3 * δ / 2 := by dsimp [x]; field_simp
  have hpy : p * y = c + 1 - 3 * δ / 2 := by dsimp [y]; field_simp
  have hux : u ≤ x := by nlinarith [hcu'.2]
  have hyv : y ≤ v := by nlinarith [hdv'.1]
  have hxy : x ≤ y := by nlinarith
  have hqcover : ∀ t ∈ Set.Icc x y, ndist (q * t) ≤ δ := by
    intro t ht
    have hpt : δ < ndist (p * t) := by
      apply strict_of_between (m := c) <;>
        nlinarith [mul_le_mul_of_nonneg_left ht.1 hp.le,
          mul_le_mul_of_nonneg_left ht.2 hp.le]
    exact (hcover t ⟨le_trans hu.1 (le_trans hux ht.1),
      le_trans ht.2 (le_trans hyv hv.2)⟩).resolve_left (not_le.mpr hpt)
  have hlen := single_band_length (lt_trans hp hpq) (by linarith) hxy hqcover
  have hlenp : p * (y - x) = 1 - 3 * δ := by linarith
  have hpos : 0 < y - x := by nlinarith
  have := mul_lt_mul_of_pos_right hpq hpos
  nlinarith

theorem slow_band_unique {A B p q δ u v : ℝ} {c d : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5 * δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p * t) ≤ δ ∨ ndist (q * t) ≤ δ)
    (hu : u ∈ Set.Icc A B) (hv : v ∈ Set.Icc A B)
    (hcu : |p * u - c| ≤ δ) (hdv : |p * v - d| ≤ δ) : c = d := by
  rcases lt_trichotomy c d with h | h | h
  · exact False.elim (no_two_slow_bands hp hpq hδ hsmall hcover hu hv hcu hdv h)
  · exact h
  · exact False.elim (no_two_slow_bands hp hpq hδ hsmall hcover hv hu hdv hcu h)

/-- A fast band containing the left endpoint meets the unique slow band. -/
theorem left_overlap {A B p q δ x : ℝ} {c k : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hδ : 0 < δ) (hsmall : 2 * δ < 1)
    (hx : x ∈ Set.Icc A B) (hc : |p * x - c| ≤ δ)
    (hk : |q * A - k| ≤ δ)
    (hcover : ∀ t ∈ Set.Icc A B, |p * t - c| ≤ δ ∨ ndist (q * t) ≤ δ) :
    ∃ t : ℝ, |p * t - c| ≤ δ ∧ |q * t - k| ≤ δ := by
  by_cases ha : |p * A - c| ≤ δ
  · exact ⟨A, ha, hk⟩
  let L := ((c : ℝ) - δ) / p
  have hpL : p * L = c - δ := by dsimp [L]; field_simp
  have hcx := abs_le.mp hc
  have hAL : A < L := by
    have hpa : p * A < c - δ := by
      have := mul_le_mul_of_nonneg_left hx.1 hp.le
      rw [abs_le] at ha
      push Not at ha
      rcases lt_or_ge (p * A) (c - δ) with hh | hh
      · exact hh
      · exact False.elim (by linarith [ha (by linarith), hcx.2])
    nlinarith
  have hLx : L ≤ x := by nlinarith [hcx.1]
  have hsub : Set.Ico A L ⊆ {t : ℝ | ndist (q * t) ≤ δ} := by
    intro t ht
    have hpt : ¬ |p * t - c| ≤ δ := by
      intro hh
      have := (abs_le.mp hh).1
      nlinarith [mul_lt_mul_of_pos_left ht.2 hp]
    exact (hcover t ⟨ht.1, le_trans ht.2.le (le_trans hLx hx.2)⟩).resolve_left hpt
  have hclosed : IsClosed {t : ℝ | ndist (q * t) ≤ δ} :=
    isClosed_le (continuous_ndist.comp (continuous_const.mul continuous_id)) continuous_const
  have hsub' := closure_minimal hsub hclosed
  rw [closure_Ico (ne_of_lt hAL)] at hsub'
  obtain ⟨j, hj⟩ := single_band hq (by linarith) hAL.le hsub'
  have hjk : j = k := band_center_unique hsmall (hj A ⟨le_rfl, hAL.le⟩) hk
  refine ⟨L, ?_, ?_⟩
  · rw [hpL, sub_sub_cancel_left, abs_neg, abs_of_pos hδ]
  · simpa [hjk] using hj L ⟨hAL.le, le_rfl⟩

/-- The right-endpoint version follows by reflecting time. -/
theorem right_overlap {A B p q δ x : ℝ} {c k : ℤ}
    (hp : 0 < p) (hq : 0 < q) (hδ : 0 < δ) (hsmall : 2 * δ < 1)
    (hx : x ∈ Set.Icc A B) (hc : |p * x - c| ≤ δ)
    (hk : |q * B - k| ≤ δ)
    (hcover : ∀ t ∈ Set.Icc A B, |p * t - c| ≤ δ ∨ ndist (q * t) ≤ δ) :
    ∃ t : ℝ, |p * t - c| ≤ δ ∧ |q * t - k| ≤ δ := by
  have hneg (w t : ℝ) (j : ℤ) : |w * (-t) - (-j : ℤ)| = |w * t - j| := by
    rw [Int.cast_neg, show w * (-t) - -(j : ℝ) = -(w * t - j) by ring, abs_neg]
  have hc' : |p * (-x) - (-c : ℤ)| ≤ δ := by simpa only [hneg] using hc
  have hk' : |q * (-B) - (-k : ℤ)| ≤ δ := by simpa only [hneg] using hk
  have hcover' : ∀ t ∈ Set.Icc (-B) (-A),
      |p * t - (-c : ℤ)| ≤ δ ∨ ndist (q * t) ≤ δ := by
    intro t ht
    have hh := hcover (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [mul_neg, ndist_neg, ← hneg p t (-c), neg_neg] using hh
  obtain ⟨t, ht1, ht2⟩ := left_overlap hp hq hδ hsmall
    (show -x ∈ Set.Icc (-B) (-A) from ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    hc' hk' hcover'
  refine ⟨-t, ?_, ?_⟩
  · simpa only [← hneg p t (-c), neg_neg] using ht1
  · simpa only [← hneg q t (-k), neg_neg] using ht2

theorem overlap_distance {p q δ t : ℝ} {c k : ℤ} (hp : 0 < p) (hq : 0 < q)
    (hc : |p * t - c| ≤ δ) (hk : |q * t - k| ≤ δ) :
    |(c : ℝ) / p - (k : ℝ) / q| ≤ δ / p + δ / q := by
  have hc' : |t - (c : ℝ) / p| ≤ δ / p := by
    have heq : t - (c : ℝ) / p = (p * t - c) / p := by field_simp
    rw [heq, abs_div, abs_of_pos hp]
    exact div_le_div_of_nonneg_right hc hp.le
  have hk' : |t - (k : ℝ) / q| ≤ δ / q := by
    have heq : t - (k : ℝ) / q = (q * t - k) / q := by field_simp
    rw [heq, abs_div, abs_of_pos hq]
    exact div_le_div_of_nonneg_right hk hq.le
  calc
    _ ≤ |(c : ℝ) / p - t| + |t - (k : ℝ) / q| := abs_sub_le _ _ _
    _ ≤ δ / p + δ / q := by rw [abs_sub_comm ((c : ℝ) / p) t]; linarith

end LonelyRunner.BadCover

namespace LonelyRunner.LaminarCover

open Set





end LonelyRunner.LaminarCover

namespace LonelyRunner.Farey



theorem endpoints_lt {a b r s : ℤ} (h : b * r - a * s = 1)
    (hr : 0 < r) (hs : 0 < s) : (a : ℝ) / r < (b : ℝ) / s := by
  apply (div_lt_div_iff₀ (by exact_mod_cast hr) (by exact_mod_cast hs)).mpr
  have hR : (b : ℝ) * r - a * s = 1 := by exact_mod_cast h
  linarith

theorem determinant_identity {a b r s : ℤ} (h : b * r - a * s = 1) (v c : ℤ) :
    (r * c - a * v) * s + (b * v - s * c) * r = v := by
  linear_combination v * h













end LonelyRunner.Farey

namespace LonelyRunner.CoprimeReplacements

open Farey BadCover

/-- At a small-denominator rational, a bad speed is exactly at an integer. -/
theorem endpoint_exact {a n r w c : ℤ} (hr : 0 < r) (hrn : r < n)
    (hc : |(w : ℝ) * ((a : ℝ) / r) - c| ≤ 1 / n) :
    r * c - a * w = 0 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_trans hr hrn)
  have heq : |(r : ℝ) * c - a * w| = r * |(w : ℝ) * ((a : ℝ) / r) - c| := by
    calc
      _ = |-(r * ((w : ℝ) * ((a : ℝ) / r) - c))| := by
        congr 1
        field_simp
        ring
      _ = _ := by rw [abs_neg, abs_mul, abs_of_pos hrR]
  have hlt : |(r : ℝ) * c - a * w| < 1 := by
    rw [heq]
    calc
      _ ≤ (r : ℝ) * (1 / n) := mul_le_mul_of_nonneg_left hc hrR.le
      _ < 1 := by rw [mul_one_div, div_lt_one hnR]; exact_mod_cast hrn
  have hltZ : |r * c - a * w| < 1 := by exact_mod_cast hlt
  have := abs_lt.mp hltZ
  omega

theorem endpoint_value {a n r w c : ℤ} (hr : 0 < r) (hrn : r < n)
    (hc : |(w : ℝ) * ((a : ℝ) / r) - c| ≤ 1 / n) :
    (w : ℝ) * ((a : ℝ) / r) = c := by
  have hz := endpoint_exact hr hrn hc
  have hzR : (r : ℝ) * c - a * w = 0 := by exact_mod_cast hz
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  field_simp
  nlinarith

theorem endpoint_dvd {a b n r s w : ℤ} (h : b * r - a * s = 1)
    (hr : 0 < r) (hrn : r < n) (hc : ndist ((w : ℝ) * ((a : ℝ) / r)) ≤ 1 / n) :
    r ∣ w := by
  let c := round ((w : ℝ) * ((a : ℝ) / r))
  have hz := endpoint_exact (c := c) hr hrn hc
  refine ⟨b * w - s * c, ?_⟩
  have hi := determinant_identity h w c
  rw [hz, zero_mul, zero_add] at hi
  simpa only [mul_comm] using hi.symm

theorem twice_le_of_dvd {r w : ℤ} (hr : 0 < r) (hrw : r < w) (h : r ∣ w) :
    2 * r ≤ w := by
  obtain ⟨k, rfl⟩ := h
  have hk : 2 ≤ k := by
    have : 1 < k := by nlinarith
    omega
  nlinarith

theorem gap_eq {a b r s : ℤ} (h : b * r - a * s = 1) (hr : 0 < r) (hs : 0 < s) :
    (b : ℝ) / s - (a : ℝ) / r = 1 / ((r : ℝ) * s) := by
  have hR : (b : ℝ) * r - a * s = 1 := by exact_mod_cast h
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  field_simp
  linarith

/-- Two endpoint-centered bad bands are too short to meet. -/
theorem endpoint_bands_separated {n r s p q : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrn : r < n) (hsn : s < n)
    (hp : 2 * r ≤ p) (hq : 2 * s ≤ q) :
    (1 / n) / p + (1 / n) / q < 1 / (r * s) := by
  have hn : 0 < n := lt_trans hr hrn
  calc
    _ ≤ (1 / n) / (2 * r) + (1 / n) / (2 * s) :=
      add_le_add (div_le_div_of_nonneg_left (by positivity) (by positivity) hp)
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hq)
    _ = ((r + s) / (2 * n)) / (r * s) := by field_simp; ring
    _ < _ := div_lt_div_of_pos_right
      ((div_lt_one (by positivity)).mpr (by linarith)) (mul_pos hr hs)

/-- A positive integral determinant of a sufficiently close center is exactly one. -/
theorem close_residue_one {a c n r p q : ℤ}
    (hr : 0 < r) (hrn : r < n) (hp : 0 < p) (hpq : p < q)
    (hd : 0 < r * c - a * p)
    (hc : |(c : ℝ) / p - (a : ℝ) / r| ≤ (1 / n) / p + (1 / n) / q) :
    r * c - a * p = 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_trans hr hrn)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hqR : (0 : ℝ) < q := lt_trans hpR hpqR
  have hdR : (0 : ℝ) < r * c - a * p := by exact_mod_cast hd
  have heq : (c : ℝ) / p - (a : ℝ) / r = (r * c - a * p) / (r * p) := by
    field_simp
  have hclose : ((r : ℝ) * c - a * p) / (r * p) ≤ (1 / n) / p + (1 / n) / q := by
    rwa [heq, abs_of_pos (div_pos hdR (mul_pos hrR hpR))] at hc
  have hqp : ((1 : ℝ) / n) / q < (1 / n) / p :=
    div_lt_div_of_pos_left (by positivity) hpR hpqR
  have hnr : ((1 : ℝ) / n) / p < (1 / r) / p :=
    div_lt_div_of_pos_right (one_div_lt_one_div_of_lt hrR (by exact_mod_cast hrn)) hpR
  have hbound : ((r : ℝ) * c - a * p) / (r * p) < 2 / (r * p) := by
    have heq' : (1 / (r : ℝ)) / p = 1 / (r * p) := by ring
    rw [heq'] at hnr
    rw [show (2 : ℝ) / (r * p) = 2 * (1 / (r * p)) by ring]
    linarith
  have hlt : (r : ℝ) * c - a * p < 2 :=
    (div_lt_div_iff_of_pos_right (mul_pos hrR hpR)).mp hbound
  have hltZ : r * c - a * p < 2 := by exact_mod_cast hlt
  omega

theorem final_arithmetic {n r s p q : ℝ}
    (hr : 0 < r) (hrs : r < s) (hn : r + 2 ≤ n)
    (hp : p = r + s) (hq : r * s ≤ q)
    (hc : 1 / (r * p) ≤ (1 / n) / p + (1 / n) / q) : False := by
  have hs : 0 < s := lt_trans hr hrs
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := lt_of_lt_of_le (mul_pos hr hs) hq
  have hn0 : 0 < n := by linarith
  have hc' : n * q ≤ r * q + r * p := by
    have hh := (mul_le_mul_iff_right₀ (show 0 < n * p * q * r by positivity)).mpr hc
    field_simp at hh
    nlinarith
  have h1 := mul_nonneg (show 0 ≤ n - r - 2 by linarith) hq0.le
  have h2 := mul_pos hr (sub_pos.mpr hrs)
  nlinarith

theorem endpoint_dvd_right {a b n r s w : ℤ} (h : b * r - a * s = 1)
    (hs : 0 < s) (hsn : s < n) (hc : ndist ((w : ℝ) * ((b : ℝ) / s)) ≤ 1 / n) :
    s ∣ w := by
  let c := round ((w : ℝ) * ((b : ℝ) / s))
  have hz := endpoint_exact (c := c) hs hsn hc
  refine ⟨r * c - a * w, ?_⟩
  have hi := determinant_identity h w c
  rw [show b * w - s * c = 0 by omega, zero_mul, add_zero] at hi
  simpa only [mul_comm] using hi.symm

theorem common_speed_bound {a b n r s q : ℤ} (h : b * r - a * s = 1)
    (hr : 0 < r) (hs : 0 < s) (hrn : r < n) (hsn : s < n) (hq : 0 < q)
    (hA : ndist ((q : ℝ) * ((a : ℝ) / r)) ≤ 1 / n)
    (hB : ndist ((q : ℝ) * ((b : ℝ) / s)) ≤ 1 / n) : r * s ≤ q := by
  let i := round ((q : ℝ) * ((a : ℝ) / r))
  let j := round ((q : ℝ) * ((b : ℝ) / s))
  have hi := endpoint_value (c := i) hr hrn hA
  have hj := endpoint_value (c := j) hs hsn hB
  have hg := gap_eq h hr hs
  have hgap := endpoints_lt h hr hs
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hijR : (i : ℝ) < j := by nlinarith
  have hij : i < j := by exact_mod_cast hijR
  have hunit : (1 : ℝ) ≤ j - i := by exact_mod_cast (show 1 ≤ j - i by omega)
  have heq : (j : ℝ) - i = (q : ℝ) / ((r : ℝ) * s) := by
    rw [← hi, ← hj, ← mul_sub, hg, mul_one_div]
  rw [heq] at hunit
  have hrsR : (0 : ℝ) < (r : ℝ) * s := by exact_mod_cast mul_pos hr hs
  have := (le_div_iff₀ hrsR).mp hunit
  exact_mod_cast (by simpa using this : (r : ℝ) * s ≤ q)









end LonelyRunner.CoprimeReplacements

namespace LonelyRunner.SingleDeletion

open BadCover









end LonelyRunner.SingleDeletion

namespace LonelyRunner.BadCover











end LonelyRunner.BadCover

namespace LonelyRunner.MatchingArithmetic





end LonelyRunner.MatchingArithmetic

namespace LonelyRunner.LargeDeletionMatching

open BadCover SingleDeletion



















end LonelyRunner.LargeDeletionMatching

namespace LonelyRunner.SeparatedBands

open BadCover









end LonelyRunner.SeparatedBands

namespace LonelyRunner

open Finset



























end LonelyRunner

namespace LonelyRunner

















end LonelyRunner

namespace LonelyRunner.FailedWindow

open Farey BadCover









end LonelyRunner.FailedWindow

namespace LonelyRunner.SeparatedReplacements

open LargeDeletionMatching SeparatedBands























end LonelyRunner.SeparatedReplacements

namespace LonelyRunner.MixedReplacements

open LargeDeletionMatching SeparatedReplacements













end LonelyRunner.MixedReplacements

namespace LonelyRunner.SeparatedMulti

open SeparatedReplacements SeparatedBands SingleDeletion























end LonelyRunner.SeparatedMulti

namespace LonelyRunner.InteractionComponents

open Set























end LonelyRunner.InteractionComponents

namespace LonelyRunner.GWArithmetic

open SeparatedReplacements







end LonelyRunner.GWArithmetic

namespace LonelyRunner.ContactPreservation











end LonelyRunner.ContactPreservation

namespace LonelyRunner.GWContactArithmetic

open SeparatedReplacements ContactPreservation



















end LonelyRunner.GWContactArithmetic

namespace LonelyRunner.ComponentRestoration

open SeparatedMulti InteractionComponents









end LonelyRunner.ComponentRestoration

namespace LonelyRunner.GWGrowth

open SeparatedReplacements GWArithmetic

























end LonelyRunner.GWGrowth

namespace LonelyRunner.OddSmooth

open SeparatedReplacements GWGrowth















end LonelyRunner.OddSmooth

namespace LonelyRunner.SecondUnit

open SeparatedReplacements GWArithmetic OddSmooth











end LonelyRunner.SecondUnit

namespace LonelyRunner.ElementarySmooth

open SeparatedReplacements OddSmooth GWArithmetic GWGrowth SecondUnit

















end LonelyRunner.ElementarySmooth

namespace LonelyRunner.FailedFlank

open Farey BadCover LargeDeletionMatching









end LonelyRunner.FailedFlank

namespace LonelyRunner.FlankReduction

















end LonelyRunner.FlankReduction

namespace LonelyRunner.MixedNormalize

open SeparatedReplacements SecondUnit GWArithmetic



end LonelyRunner.MixedNormalize

namespace LonelyRunner.MixedArithmetic

open SeparatedReplacements GWArithmetic GWGrowth FlankReduction SecondUnit



end LonelyRunner.MixedArithmetic

namespace LonelyRunner.NearData

open LargeDeletionMatching SeparatedReplacements







end LonelyRunner.NearData

namespace LonelyRunner.MixedConverse

open LargeDeletionMatching SeparatedReplacements MixedReplacements
open GWArithmetic GWGrowth FlankReduction









end LonelyRunner.MixedConverse

namespace LonelyRunner.SmallComponentRigidity

open SeparatedMulti SeparatedReplacements InteractionComponents





































end LonelyRunner.SmallComponentRigidity

open LonelyRunner
open LonelyRunner.CoprimeReplacements
open Farey BadCover

set_option maxHeartbeats 1200000 in
/-- The two inserted speeds cannot cover the entire Farey interval. -/
theorem solution {a b n r s p q : ℤ}
    (h : b * r - a * s = 1) (hn : 5 ≤ n) (hr : 0 < r)
    (hrs : r < s) (hsn : s < n) (hnp : n ≤ p) (hpq : p < q) :
    ¬ (∀ t ∈ Set.Icc ((a : ℝ) / r) ((b : ℝ) / s),
      ndist ((p : ℝ) * t) ≤ 1 / n ∨ ndist ((q : ℝ) * t) ≤ 1 / n) := by
  intro hcover
  let A : ℝ := (a : ℝ) / r
  let B : ℝ := (b : ℝ) / s
  let δ : ℝ := 1 / n
  have hs : 0 < s := lt_trans hr hrs
  have hrn : r < n := lt_trans hrs hsn
  have hp : 0 < p := by omega
  have hq : 0 < q := lt_trans hp hpq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpq
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : 5 * δ ≤ 1 := by
    dsimp [δ]
    rw [mul_one_div, div_le_one hnR]
    exact_mod_cast hn
  have hAB : A < B := endpoints_lt h hr hs
  have hAmem : A ∈ Set.Icc A B := ⟨le_rfl, hAB.le⟩
  have hBmem : B ∈ Set.Icc A B := ⟨hAB.le, le_rfl⟩
  have hex : ∃ x ∈ Set.Icc A B, ndist ((p : ℝ) * x) ≤ δ := by
    by_contra! hh
    have hqc : ∀ t ∈ Set.Icc A B, ndist ((q : ℝ) * t) ≤ δ := by
      intro t ht
      exact (hcover t ht).resolve_left (not_le.mpr (hh t ht))
    obtain ⟨k, hk⟩ := single_band hqR (by linarith) hAB.le hqc
    have hi := endpoint_value hr hrn (hk A hAmem)
    have hj := endpoint_value hs hsn (hk B hBmem)
    change (q : ℝ) * A = k at hi
    change (q : ℝ) * B = k at hj
    nlinarith
  obtain ⟨x, hx, hxp⟩ := hex
  let c := round ((p : ℝ) * x)
  have hc : |(p : ℝ) * x - c| ≤ δ := hxp
  have hslow : ∀ t ∈ Set.Icc A B, ndist ((p : ℝ) * t) ≤ δ →
      |(p : ℝ) * t - c| ≤ δ := by
    intro t ht htp
    have heq := slow_band_unique hpR hpqR hδ hsmall hcover hx ht hc htp
    change |(p : ℝ) * t - (round ((p : ℝ) * t) : ℤ)| ≤ δ at htp
    simpa only [← heq] using htp
  have hcover' : ∀ t ∈ Set.Icc A B,
      |(p : ℝ) * t - c| ≤ δ ∨ ndist ((q : ℝ) * t) ≤ δ := by
    intro t ht
    exact (hcover t ht).imp (hslow t ht) id
  have hgap : B - A = 1 / ((r : ℝ) * s) := gap_eq h hr hs
  by_cases hAp : ndist ((p : ℝ) * A) ≤ δ
  · have hAc := endpoint_value hr hrn (hslow A hAmem hAp)
    change (p : ℝ) * A = c at hAc
    have hcA : (c : ℝ) / p = A := (div_eq_iff hpR.ne').mpr (by nlinarith)
    by_cases hBp : ndist ((p : ℝ) * B) ≤ δ
    · have hBc := endpoint_value hs hsn (hslow B hBmem hBp)
      change (p : ℝ) * B = c at hBc
      nlinarith
    · have hBq := (hcover B hBmem).resolve_left hBp
      let k := round ((q : ℝ) * B)
      have hk : |(q : ℝ) * B - k| ≤ δ := hBq
      have hBk := endpoint_value hs hsn hk
      change (q : ℝ) * B = k at hBk
      have hkB : (k : ℝ) / q = B := (div_eq_iff hqR.ne').mpr (by nlinarith)
      obtain ⟨t, ht1, ht2⟩ := right_overlap hpR hqR hδ (by linarith) hx hc hk hcover'
      have ho := overlap_distance hpR hqR ht1 ht2
      rw [hcA, hkB, abs_of_neg (sub_neg.mpr hAB)] at ho
      have hrp := twice_le_of_dvd hr (by omega) (endpoint_dvd h hr hrn hAp)
      have hsq := twice_le_of_dvd hs (by omega) (endpoint_dvd_right h hs hsn hBq)
      have hsep := endpoint_bands_separated (n := (n : ℝ)) hrR hsR
        (by exact_mod_cast hrn) (by exact_mod_cast hsn)
        (by exact_mod_cast hrp : (2 : ℝ) * r ≤ p)
        (by exact_mod_cast hsq : (2 : ℝ) * s ≤ q)
      change δ / p + δ / q < 1 / ((r : ℝ) * s) at hsep
      linarith
  · have hAq := (hcover A hAmem).resolve_left hAp
    let i := round ((q : ℝ) * A)
    have hi : |(q : ℝ) * A - i| ≤ δ := hAq
    have hAi := endpoint_value hr hrn hi
    change (q : ℝ) * A = i at hAi
    have hiA : (i : ℝ) / q = A := (div_eq_iff hqR.ne').mpr (by nlinarith)
    obtain ⟨u, hu1, hu2⟩ := left_overlap hpR hqR hδ (by linarith) hx hc hi hcover'
    have hoA := overlap_distance hpR hqR hu1 hu2
    rw [hiA] at hoA
    by_cases hBp : ndist ((p : ℝ) * B) ≤ δ
    · have hBc := endpoint_value hs hsn (hslow B hBmem hBp)
      change (p : ℝ) * B = c at hBc
      have hcB : (c : ℝ) / p = B := (div_eq_iff hpR.ne').mpr (by nlinarith)
      rw [hcB, abs_of_pos (sub_pos.mpr hAB)] at hoA
      have hsp := twice_le_of_dvd hs (by omega) (endpoint_dvd_right h hs hsn hBp)
      have hrq := twice_le_of_dvd hr (by omega) (endpoint_dvd h hr hrn hAq)
      have hsep := endpoint_bands_separated (n := (n : ℝ)) hsR hrR
        (by exact_mod_cast hsn) (by exact_mod_cast hrn)
        (by exact_mod_cast hsp : (2 : ℝ) * s ≤ p)
        (by exact_mod_cast hrq : (2 : ℝ) * r ≤ q)
      rw [mul_comm (s : ℝ) (r : ℝ)] at hsep
      change δ / p + δ / q < 1 / ((r : ℝ) * s) at hsep
      linarith
    · have hBq := (hcover B hBmem).resolve_left hBp
      let j := round ((q : ℝ) * B)
      have hj : |(q : ℝ) * B - j| ≤ δ := hBq
      have hBj := endpoint_value hs hsn hj
      change (q : ℝ) * B = j at hBj
      have hjB : (j : ℝ) / q = B := (div_eq_iff hqR.ne').mpr (by nlinarith)
      obtain ⟨v, hv1, hv2⟩ := right_overlap hpR hqR hδ (by linarith) hx hc hj hcover'
      have hoB := overlap_distance hpR hqR hv1 hv2
      rw [hjB] at hoB
      have hcnA : ¬ |(p : ℝ) * A - c| ≤ δ :=
        fun hh => hAp ((ndist_le_abs_sub _ c).trans hh)
      have hcnB : ¬ |(p : ℝ) * B - c| ≤ δ :=
        fun hh => hBp ((ndist_le_abs_sub _ c).trans hh)
      have hcx := abs_le.mp hc
      have hcA : (p : ℝ) * A < c := by
        have hh := mul_le_mul_of_nonneg_left hx.1 hpR.le
        rw [abs_le] at hcnA
        push Not at hcnA
        by_contra! hge
        have := hcnA (by linarith)
        linarith [hcx.2]
      have hcB : (c : ℝ) < p * B := by
        have hh := mul_le_mul_of_nonneg_left hx.2 hpR.le
        rw [abs_le] at hcnB
        push Not at hcnB
        have := hcnB (by linarith [hcx.1])
        linarith
      have hd : 0 < r * c - a * p := by
        have hh := (mul_lt_mul_iff_right₀ hrR).mpr hcA
        dsimp [A] at hh
        field_simp at hh
        exact_mod_cast (show (0 : ℝ) < r * c - a * p by nlinarith only [hh])
      have he : 0 < b * p - s * c := by
        have hh := (mul_lt_mul_iff_right₀ hsR).mpr hcB
        dsimp [B] at hh
        field_simp at hh
        exact_mod_cast (show (0 : ℝ) < b * p - s * c by nlinarith only [hh])
      have hd1 := close_residue_one hr hrn hp hpq hd hoA
      have hoB' : |((-c : ℤ) : ℝ) / p - ((-b : ℤ) : ℝ) / s| ≤
          (1 / n) / p + (1 / n) / q := by
        convert hoB using 1
        push_cast
        rw [show -(c : ℝ) / p - -(b : ℝ) / s = -((c : ℝ) / p - (b : ℝ) / s) by ring,
          abs_neg]
      have he1' := close_residue_one hs hsn hp hpq
        (by nlinarith only [he] : 0 < s * (-c) - (-b) * p) hoB'
      have he1 : b * p - s * c = 1 := by nlinarith only [he1']
      have hid := determinant_identity h p c
      rw [hd1, he1] at hid
      have hpSum : p = r + s := by linarith only [hid]
      have hqBound := common_speed_bound h hr hs hrn hsn hq hAq hBq
      have hd1R : (r : ℝ) * c - a * p = 1 := by exact_mod_cast hd1
      have heq : (c : ℝ) / p - A = 1 / ((r : ℝ) * p) := by
        dsimp [A]
        field_simp
        nlinarith only [hd1R]
      rw [heq, abs_of_pos (by positivity)] at hoA
      exact final_arithmetic (s := (s : ℝ)) hrR (by exact_mod_cast hrs) (by exact_mod_cast (show r + 2 ≤ n by omega))
        (by exact_mod_cast hpSum) (by exact_mod_cast hqBound) hoA
