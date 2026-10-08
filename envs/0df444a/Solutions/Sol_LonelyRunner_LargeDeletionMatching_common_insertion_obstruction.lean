-- Prove2me | solution 1 for LonelyRunner.LargeDeletionMatching.common_insertion_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T18:57:17.199886+00:00
-- url     : https://prove2.me/submissions/54baa8d5-18e8-4045-8201-285a20dfe906

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs
import Theorems.Thm_LonelyRunner_BadCover_fast_center_impossible
import Theorems.Thm_LonelyRunner_BadCover_slow_center_gap
import Theorems.Thm_LonelyRunner_MatchingArithmetic_full_width

namespace LonelyRunner



theorem ndist_eq_norm (x : ℝ) : ndist x = ‖(x : UnitAddCircle)‖ :=
  UnitAddCircle.norm_eq.symm





theorem ndist_eq_min_fract (x : ℝ) : ndist x = min (Int.fract x) (1 - Int.fract x) :=
  abs_sub_round_eq_min x



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











theorem retained_not_dvd {n r v : ℤ} (hr : 0 < r) (hn : n ≤ 2 * r)
    (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) : ¬ r ∣ v := by
  rintro ⟨k, rfl⟩
  have hk : 0 < k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  have : k = 1 := by omega
  simp_all







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



























end LonelyRunner.CoprimeReplacements

namespace LonelyRunner.SingleDeletion

open BadCover

/-- Elementary interval constraints suffice for every retained baseline speed. -/
theorem safe_of_bounds {n r v A B t : ℝ}
    (hn : 2 < n) (hr : 1 < r) (hv : 1 ≤ v) (hvn : v ≤ n-1)
    (hne : v ≤ r-1 ∨ r+1 ≤ v)
    (hA : (1+1/n)/(r+1) ≤ A) (hA' : 1/n < A)
    (hB : B ≤ (1-1/n)/(r-1)) (hB' : B ≤ (2-1/n)/(n-1))
    (ht : t ∈ Set.Ioo A B) : 1/n < ndist (v*t) := by
  have hn0 : 0 < n := by linarith
  have ht0 : 0 < t := lt_trans (by positivity : 0 < 1/n) (lt_trans hA' ht.1)
  rcases hne with hvr | hrv
  · apply strict_of_between (m := 0)
    · simp only [Int.cast_zero,zero_add]
      nlinarith [ht.1]
    · simp only [Int.cast_zero,zero_add]
      have hb : t < (1-1/n)/(r-1) := lt_of_lt_of_le ht.2 hB
      have hb' := (lt_div_iff₀ (by linarith : 0 < r-1)).mp hb
      nlinarith
  · apply strict_of_between (m := 1)
    · simp only [Int.cast_one]
      have ha : (1+1/n)/(r+1) < t := lt_of_le_of_lt hA ht.1
      have ha' := (div_lt_iff₀ (by linarith : 0 < r+1)).mp ha
      nlinarith
    · simp only [Int.cast_one]
      have hb : t < (2-1/n)/(n-1) := lt_of_lt_of_le ht.2 hB'
      have hb' := (lt_div_iff₀ (by linarith : 0 < n-1)).mp hb
      nlinarith

set_option maxHeartbeats 600000 in
/-- The two endpoint formulas, including the boundary case n = 2r. -/
theorem interval_bounds {n r F : ℝ}
    (hr : 2 ≤ r) (hrn : r+2 ≤ n)
    (hF : (n ≤ 2*r-1 ∧ F=r-1) ∨ (n=2*r ∧ F=2*r-1)) :
    (1+1/n)/(r+1) = 1/r-(n-r)/(n*r*(r+1)) ∧
    1/n < 1/r-(n-r)/(n*r*(r+1)) ∧
    1/r+(n-r)/(n*r*F) ≤ (1-1/n)/(r-1) ∧
    1/r+(n-r)/(n*r*F) ≤ (2-1/n)/(n-1) := by
  have hn : 0 < n := by linarith
  have hr0 : 0 < r := by linarith
  have hrm : 0 < r-1 := by linarith
  have hrp : 0 < r+1 := by linarith
  have hnm : 0 < n-1 := by linarith
  have heq : (1+1/n)/(r+1) = 1/r-(n-r)/(n*r*(r+1)) := by field_simp; ring
  refine ⟨heq, ?_, ?_⟩
  · rw [← heq]
    apply (lt_div_iff₀ hrp).mpr
    field_simp
    linarith
  · rcases hF with ⟨h, rfl⟩ | ⟨h, rfl⟩
    · have heq' : 1/r+(n-r)/(n*r*(r-1)) = (1-1/n)/(r-1) := by field_simp; ring
      rw [heq']
      refine ⟨le_rfl, ?_⟩
      apply (div_le_div_iff₀ hrm hnm).mpr
      apply (mul_le_mul_iff_right₀ hn).mp
      field_simp
      nlinarith [mul_nonneg (show 0 ≤ n-1 by linarith) (show 0 ≤ 2*r-1-n by linarith)]
    · have hf : 0 < 2*r-1 := by linarith
      have heq' : 1/r+(n-r)/(n*r*(2*r-1)) = (2-1/n)/(n-1) := by
        field_simp [ne_of_gt hn, ne_of_gt hr0, ne_of_gt hf, ne_of_gt hnm,
          show -1+r*2 ≠ 0 by linarith]
        rw [h]
        field_simp
        ring
      rw [heq']
      refine ⟨?_, le_rfl⟩
      apply (div_le_div_iff₀ hnm hrm).mpr
      apply (mul_le_mul_iff_right₀ hn).mp
      field_simp
      nlinarith

/-- Badness at 1/r, with r<n, is equivalent to divisibility (the forward half). -/
theorem dvd_of_bad {n r w : ℕ} (hr : 0 < r) (hrn : r < n)
    (h : ndist ((w:ℝ)*(1/r)) ≤ 1/n) : r ∣ w := by
  have hh := CoprimeReplacements.endpoint_exact (a := 1) (n := (n:ℤ))
    (r := (r:ℤ)) (w := (w:ℤ)) (c := round ((w:ℝ)*(1/r)))
    (by exact_mod_cast hr) (by exact_mod_cast hrn) (by simpa [ndist] using h)
  have hd : (r:ℤ) ∣ (w:ℤ) := ⟨round ((w:ℝ)*(1/r)), by linear_combination -hh⟩
  exact_mod_cast hd



end LonelyRunner.SingleDeletion

namespace LonelyRunner.BadCover

theorem fixed_slow_band {A B p q δ x : ℝ} {c : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5 * δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p*t) ≤ δ ∨ ndist (q*t) ≤ δ)
    (hx : x ∈ Set.Icc A B) (hc : |p*x-c| ≤ δ) :
    ∀ t ∈ Set.Icc A B, |p*t-c| ≤ δ ∨ ndist (q*t) ≤ δ := by
  intro t ht
  rcases hcover t ht with hpbad | hqbad
  · left
    have heq := slow_band_unique hp hpq hδ hsmall hcover hx ht hc hpbad
    simpa only [ndist, ← heq] using hpbad
  · exact Or.inr hqbad

/-- A covered interval extends by at most one fast band at each end of its
unique slow band. -/
theorem covered_length {A B p q δ x : ℝ} {c : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5 * δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p*t) ≤ δ ∨ ndist (q*t) ≤ δ)
    (hx : x ∈ Set.Icc A B) (hc : |p*x-c| ≤ δ) :
    B-A ≤ 2*δ/p + 4*δ/q := by
  have hq := lt_trans hp hpq
  have hsmall' : 2*δ < 1 := by linarith
  have hcov := fixed_slow_band hp hpq hδ hsmall hcover hx hc
  have hAB : A ≤ B := le_trans hx.1 hx.2
  have hleft : (c:ℝ)/p - δ/p - 2*δ/q ≤ A := by
    rcases hcov A ⟨le_rfl,hAB⟩ with ha | ha
    · have h := (abs_le.mp ha).1
      have hh : (c:ℝ)/p - δ/p ≤ A := by
        rw [← sub_div, div_le_iff₀ hp]; linarith
      have : 0 < δ/q := div_pos hδ hq
      try simp only [mul_div_assoc] at *
      linarith
    · obtain ⟨t,ht,hk⟩ := left_overlap hp hq hδ hsmall' hx hc ha hcov
      have hdist := abs_le.mp (overlap_distance hp hq ht hk)
      have ha' := (abs_le.mp ha).1
      have haa : (round (q*A):ℝ)/q - δ/q ≤ A := by
        rw [← sub_div, div_le_iff₀ hq]; linarith
      try simp only [mul_div_assoc] at *
      linarith [hdist.2]
  have hright : B ≤ (c:ℝ)/p + δ/p + 2*δ/q := by
    rcases hcov B ⟨hAB,le_rfl⟩ with hb | hb
    · have h := (abs_le.mp hb).2
      have hh : B ≤ (c:ℝ)/p + δ/p := by
        rw [← add_div, le_div_iff₀ hp]; linarith
      have : 0 < δ/q := div_pos hδ hq
      try simp only [mul_div_assoc] at *
      linarith
    · obtain ⟨t,ht,hk⟩ := right_overlap hp hq hδ hsmall' hx hc hb hcov
      have hdist := abs_le.mp (overlap_distance hp hq ht hk)
      have hb' := (abs_le.mp hb).2
      have hbb : B ≤ (round (q*B):ℝ)/q + δ/q := by
        rw [← add_div, le_div_iff₀ hq]; linarith
      try simp only [mul_div_assoc] at *
      linarith [hdist.1]
  simp only [mul_div_assoc] at *
  linarith



/-- If both speeds have an integer center at x, covering beyond the right end
of the slow band requires a different fast band to reach that slow band. -/
theorem coincident_center_gap {A B p q δ x : ℝ} {c k : ℤ}
    (hp : 0 < p) (hpq : p < q) (hδ : 0 < δ) (hsmall : 5*δ ≤ 1)
    (hcover : ∀ t ∈ Set.Icc A B, ndist (p*t) ≤ δ ∨ ndist (q*t) ≤ δ)
    (hx : x ∈ Set.Icc A B) (hc : p*x = c) (hk : q*x = k)
    (hright : x+δ/p < B) : (1-δ)*p ≤ δ*q := by
  have hq := lt_trans hp hpq
  have hc' : |p*x-c| ≤ δ := by rw [hc,sub_self,abs_zero]; exact hδ.le
  have hcov := fixed_slow_band hp hpq hδ hsmall hcover hx hc'
  have hb : ndist (q*B) ≤ δ := by
    apply (hcov B ⟨le_trans hx.1 hx.2,le_rfl⟩).resolve_left
    intro hh
    have := (abs_le.mp hh).2
    have := mul_lt_mul_of_pos_left hright hp
    rw [mul_add,mul_div_cancel₀ _ hp.ne'] at this
    linarith
  let j := round (q*B)
  have hbj : |q*B-j| ≤ δ := hb
  have hBx : δ < q*(B-x) := by
    have hh : δ < p*(B-x) := by
      have := mul_lt_mul_of_pos_left hright hp
      rw [mul_add,mul_div_cancel₀ _ hp.ne'] at this
      nlinarith only [this]
    nlinarith only [hh,hpq,show 0 < B-x by linarith [div_pos hδ hp]]
  have hkj : k < j := by
    have : (k:ℝ) < j := by
      have := (abs_le.mp hbj).2
      nlinarith only [this,hBx,hk]
    exact_mod_cast this
  have hstep : (k:ℝ)+1 ≤ j := by exact_mod_cast hkj
  obtain ⟨v,hv,hvj⟩ := right_overlap hp hq hδ (by linarith) hx hc' hbj hcov
  have hslow : p*(v-x) ≤ δ := by
    have := (abs_le.mp hv).2
    nlinarith only [this,hc]
  have hfast : 1-δ ≤ q*(v-x) := by
    have := (abs_le.mp hvj).1
    nlinarith only [this,hstep,hk]
  nlinarith only [mul_le_mul_of_nonneg_left hslow hq.le,
    mul_le_mul_of_nonneg_left hfast hp.le]



end LonelyRunner.BadCover

namespace LonelyRunner.MatchingArithmetic

/-- A common multiple's central bad band is shorter than either half of the
single-deletion safe interval. -/
theorem half_width {n r s g w F : ℝ}
    (hg : 0 < g) (hr : 0 < r) (hrn : r < n) (hsn : s+1 ≤ n)
    (hgs : g ≤ s-r) (hw : 0 < w) (hmul : r*s ≤ g*w)
    (hF : 0 < F) (hFn : F ≤ n-1) :
    (1/n)/w < (n-r)/(n*r*F) := by
  have hn : 0 < n := lt_trans hr hrn
  have ha : 0 < n-r := sub_pos.mpr hrn
  have hs : 0 < s := by linarith
  have hnm : 0 ≤ n-1 := by linarith
  have hbase : g*(n-1) < (n-r)*s := by
    nlinarith [mul_nonneg hr.le (show 0 ≤ n-s-1 by linarith),
      mul_le_mul_of_nonneg_right hgs hnm]
  have hprod : g*(r*(n-1)) < g*((n-r)*w) := by
    nlinarith only [mul_lt_mul_of_pos_left hbase hr,
      mul_le_mul_of_nonneg_left hmul ha.le]
  have hprod' := (mul_lt_mul_iff_right₀ hg).mp hprod
  have hnum : r*F < (n-r)*w := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hFn hr.le) hprod'
  rw [div_div,div_lt_div_iff₀ (mul_pos hn hw) (mul_pos (mul_pos hn hr) hF)]
  nlinarith only [mul_lt_mul_of_pos_left hnum hn]



end LonelyRunner.MatchingArithmetic

namespace LonelyRunner.LargeDeletionMatching

open BadCover SingleDeletion



theorem cover_of_no_strict {n r s p q : ℕ} (h : ¬ HasStrictTime n r s p q)
    {t : ℝ} (hret : ∀ v : ℕ, 0 < v → v < n → v ≠ r → v ≠ s →
      (1:ℝ)/n  <  ndist ((v:ℝ)*t)) :
    ndist ((p:ℝ)*t)  ≤  1/n ∨ ndist ((q:ℝ)*t)  ≤  1/n := by
  by_contra! hh
  apply h
  refine ⟨t,fun v hv => ?_⟩
  rcases hv with ⟨hv,hvn,hvr,hvs⟩ | rfl | rfl
  · simpa only [mul_comm] using hret v hv hvn hvr hvs
  · simpa only [mul_comm] using hh.1
  · simpa only [mul_comm] using hh.2

/-- The gcd is a proper divisor of r, and fits in the gap s-r. -/
theorem gcd_bounds {n r s : ℕ} (hr : 0  <  r) (hlarge : n  ≤  2*r)
    (hrs : r < s) (hsn : s < n) :
    2*Nat.gcd r s  ≤  r ∧ r+Nat.gcd r s  ≤  s := by
  let g := Nat.gcd r s
  have hg : 0  <  g := Nat.gcd_pos_of_pos_left s hr
  have hgr : g  ∣  r := Nat.gcd_dvd_left r s
  have hgs : g  ∣  s := Nat.gcd_dvd_right r s
  have hle : g  ≤  r := Nat.le_of_dvd hr hgr
  have hne : g  ≠  r := by
    intro heq
    have hbad : (r:ℤ)  ∣  (s:ℤ) := by exact_mod_cast (heq ▸ hgs)
    exact (Farey.retained_not_dvd (n := (n:ℤ)) (r := (r:ℤ)) (v := (s:ℤ))
      (by exact_mod_cast hr) (by exact_mod_cast hlarge)
      (by exact_mod_cast (lt_trans hr hrs)) (by exact_mod_cast hsn)
      (by exact_mod_cast (ne_of_gt hrs))) hbad
  have hlt : g < r := lt_of_le_of_ne hle hne
  have htwice : 2*g  ≤  r := by
    obtain ⟨k,hk⟩ := hgr
    have hk2 : 2  ≤  k := by
      by_contra! h
      have : k  ≤  1 := by omega
      nlinarith
    nlinarith
  have hgap := Nat.le_of_dvd (Nat.sub_pos_of_lt hrs) (Nat.dvd_sub hgs hgr)
  dsimp [g] at *
  omega

/-- A positive common multiple is at least the lcm. -/
theorem common_product_bound {r s w : ℕ} (hw : 0 < w) (hrw : r ∣ w) (hsw : s ∣ w) :
    (r:ℝ)*s  ≤  (Nat.gcd r s:ℝ)*w := by
  have hle := Nat.le_of_dvd hw (Nat.lcm_dvd hrw hsw)
  have hh := Nat.mul_le_mul_left (Nat.gcd r s) hle
  rw [Nat.gcd_mul_lcm] at hh
  exact_mod_cast hh











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
open LonelyRunner.LargeDeletionMatching
open BadCover SingleDeletion

set_option maxHeartbeats 1200000 in
/-- A slow common insertion is impossible; a fast common insertion cannot
serve both deletions while the slow insertion misses r. -/
theorem solution {n r s p q : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hnp : n ≤ p) (hpq : p < q) (hg : 2 ≤ Nat.gcd r s)
    (hno : ¬ HasStrictTime n r s p q)
    (hcommon : (r ∣ p ∧ s ∣ p) ∨ (r ∣ q ∧ s ∣ q ∧ ¬r ∣ p)) : False := by
  have hrN : 0 < r := by omega
  have hpN : 0 < p := by omega
  have hqN : 0 < q := by omega
  obtain ⟨hrgN,hgsN⟩ := gcd_bounds hrN hlarge hrs hsn
  have hnR : (5:ℝ) ≤ n := by exact_mod_cast hn
  have hgR : (2:ℝ) ≤ Nat.gcd r s := by exact_mod_cast hg
  have hrgR : 2*(Nat.gcd r s:ℝ) ≤ r := by exact_mod_cast hrgN
  have hgsR : (r:ℝ)+(Nat.gcd r s:ℝ) ≤ s := by exact_mod_cast hgsN
  have hsnR : (s:ℝ)+1 ≤ n := by exact_mod_cast (Nat.add_one_le_iff.mpr hsn)
  have hn0 : (0:ℝ) < n := by linarith
  have hr0 : (0:ℝ) < r := by positivity
  have hp0 : (0:ℝ) < p := by positivity
  have hpqR : (p:ℝ) < q := by exact_mod_cast hpq
  have hq0 : (0:ℝ) < q := lt_trans hp0 hpqR
  have hδ : (0:ℝ) < 1/n := by positivity
  have hsmall : 5*((1:ℝ)/n) ≤ 1 := by rw [mul_one_div,div_le_one hn0]; exact hnR
  let F : ℝ := if n < 2*r then (r:ℝ)-1 else 2*r-1
  have hF : ((n:ℝ) ≤ 2*r-1 ∧ F=(r:ℝ)-1) ∨ ((n:ℝ)=2*r ∧ F=2*(r:ℝ)-1) := by
    dsimp [F]
    split_ifs with hh
    · left
      have : (n:ℝ)+1 ≤ 2*r := by exact_mod_cast (show n+1 ≤ 2*r by omega)
      exact ⟨by linarith,rfl⟩
    · right
      exact ⟨by exact_mod_cast (show n=2*r by omega),rfl⟩
  have hF0 : 0 < F := by rcases hF with ⟨_,hh⟩ | ⟨_,hh⟩  <;> rw [hh]  <;> linarith
  have hFn : F ≤ (n:ℝ)-1 := by rcases hF with ⟨_,hh⟩ | ⟨hh',hh⟩  <;> rw [hh]  <;> linarith
  let x : ℝ := 1/r
  let L : ℝ := ((n:ℝ)-r)/(n*r*((r:ℝ)+1))
  let R : ℝ := ((n:ℝ)-r)/(n*r*F)
  let A := x-L
  let B := x+R
  have hnr : (0:ℝ) < (n:ℝ)-r := by linarith
  have hL : 0 < L := by dsimp [L]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hAB : A < B := by dsimp [A,B]; linarith
  have hx : x ∈ Set.Icc A B := ⟨by dsimp [A]; linarith,by dsimp [B]; linarith⟩
  obtain ⟨hA,hA',hB,hB'⟩ := interval_bounds (by linarith : (2:ℝ) ≤ r)
    (by linarith : (r:ℝ)+2 ≤ n) hF
  have hcovOpen : Set.Ioo A B ⊆ {t : ℝ | ndist ((p:ℝ)*t) ≤ 1/n ∨ ndist ((q:ℝ)*t) ≤ 1/n} := by
    intro t ht
    apply cover_of_no_strict hno
    intro v hv hvn hvr _
    apply safe_of_bounds (by linarith : (2:ℝ) < n) (by linarith : (1:ℝ) < r)
      (by exact_mod_cast (show 1 ≤ v by omega))
      (show (v:ℝ) ≤ n-1 from by
        have : (v:ℝ)+1 ≤ n := by exact_mod_cast (Nat.add_one_le_iff.mpr hvn)
        linarith)
    · rcases lt_or_gt_of_ne hvr with hh | hh
      · left
        have : (v:ℝ)+1 ≤ r := by exact_mod_cast (Nat.add_one_le_iff.mpr hh)
        linarith
      · right
        exact_mod_cast (Nat.add_one_le_iff.mpr hh)
    · exact hA.le
    · exact hA'
    · exact hB
    · exact hB'
    · exact ht
  have hclosed : IsClosed {t : ℝ | ndist ((p:ℝ)*t) ≤ 1/n ∨ ndist ((q:ℝ)*t) ≤ 1/n} :=
    (isClosed_le (continuous_ndist.comp (continuous_const.mul continuous_id)) continuous_const).union
      (isClosed_le (continuous_ndist.comp (continuous_const.mul continuous_id)) continuous_const)
  have hcover := closure_minimal hcovOpen hclosed
  rw [closure_Ioo hAB.ne] at hcover
  have hwidth (w : ℕ) (hw : 0 < w) (hrw : r ∣ w) (hsw : s ∣ w) :
      (1/(n:ℝ))/w < L ∧ (1/(n:ℝ))/w < R := by
    have hprod := common_product_bound hw hrw hsw
    have hg0 : (0:ℝ) < Nat.gcd r s := by linarith
    have hrn : (r:ℝ) < n := by linarith
    have hgap : (Nat.gcd r s:ℝ) ≤ (s:ℝ)-r := by linarith
    have hw0 : (0:ℝ) < w := by positivity
    exact ⟨MatchingArithmetic.half_width hg0 hr0 hrn hsnR hgap hw0 hprod
      (by positivity) (by linarith),
      MatchingArithmetic.half_width hg0 hr0 hrn hsnR hgap hw0 hprod hF0 hFn⟩
  have hcenter (w : ℕ) (hrw : r ∣ w) : ∃ c : ℤ, (w:ℝ)*x=c := by
    obtain ⟨k,rfl⟩ := hrw
    refine ⟨(k:ℤ),?_⟩
    dsimp [x]
    push_cast
    field_simp
  rcases hcommon with ⟨hrp,hsp⟩ | ⟨hrq,hsq,hrp⟩
  · obtain ⟨hwl,hwr⟩ := hwidth p hpN hrp hsp
    obtain ⟨c,hc⟩ := hcenter p hrp
    have hleft : A < x-(1/(n:ℝ))/p := by dsimp [A]; linarith
    have hright : x+(1/(n:ℝ))/p < B := by dsimp [B]; linarith
    have hgap : (1-2*(1/(n:ℝ)))*p ≤ 2*(1/(n:ℝ))*q := by
      by_cases hrq : r ∣ q
      · obtain ⟨k,hk⟩ := hcenter q hrq
        have hh := coincident_center_gap hp0 hpqR hδ hsmall hcover hx hc hk hright
        nlinarith only [hh,mul_pos hδ hp0,mul_pos hδ hq0]
      · have hsafe : 1/(n:ℝ) < ndist ((q:ℝ)*x) := by
          by_contra! hh
          exact hrq (dvd_of_bad hrN (lt_trans hrs hsn) hh)
        exact slow_center_gap hp0 hpqR hδ hsmall hcover hc hsafe hleft hright
    have hc' : |(p:ℝ)*x-c| ≤ 1/n := by rw [hc,sub_self,abs_zero]; exact hδ.le
    have hlen := covered_length hp0 hpqR hδ hsmall hcover hx hc'
    have hlong := MatchingArithmetic.full_width hgR hrgR hgsR hsnR hp0
      (common_product_bound hpN hrp hsp) hF
    have hnm : (0:ℝ) < n-2 := by linarith
    have hgap' : ((n:ℝ)-2)*p ≤ 2*q := by
      have hh := mul_le_mul_of_nonneg_left hgap hn0.le
      field_simp at hh
      nlinarith only [hh]
    have hfrac : 4*(1/(n:ℝ))/q  ≤  (2*(1/(n:ℝ))/p)*(4/((n:ℝ)-2)) := by
      apply (div_le_iff₀ hq0).mpr
      field_simp
      nlinarith only [hgap']
    change (2*(1/(n:ℝ))/p)*(1+4/((n:ℝ)-2)) < L+R at hlong
    have heq : (2*(1/(n:ℝ))/p)*(1+4/((n:ℝ)-2)) =
        2*(1/(n:ℝ))/p + (2*(1/(n:ℝ))/p)*(4/((n:ℝ)-2)) := by ring
    dsimp [A,B] at hlen
    rw [heq] at hlong
    linarith
  · obtain ⟨hwl,hwr⟩ := hwidth q hqN hrq hsq
    obtain ⟨k,hk⟩ := hcenter q hrq
    have hsafe : 1/(n:ℝ) < ndist ((p:ℝ)*x) := by
      by_contra! hh
      exact hrp (dvd_of_bad hrN (lt_trans hrs hsn) hh)
    exact fast_center_impossible hp0 hpqR hδ hsmall hcover hk hsafe
      (by dsimp [A]; linarith) (by dsimp [B]; linarith)
