-- Prove2me | solution 1 for LonelyRunner.SmallComponentRigidity.matching_windows
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T19:04:21.054803+00:00
-- url     : https://prove2.me/submissions/4e0e88ae-46d6-4a73-aaad-5eef9940d069

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs
import Theorems.Thm_LonelyRunner_ComponentRestoration_restore_outside_cut
import Theorems.Thm_LonelyRunner_CoprimeReplacements_not_covered
import Theorems.Thm_LonelyRunner_LargeDeletionMatching_common_insertion_obstruction
import Theorems.Thm_LonelyRunner_MixedConverse_matched_slower_window
import Theorems.Thm_LonelyRunner_SeparatedMulti_minimal_multiple_gw
import Theorems.Thm_LonelyRunner_SeparatedReplacements_failed_window_escape_of_boundary

namespace LonelyRunner











/-- `ndist x` is at most the distance from `x` to any integer. -/
theorem ndist_le_abs_sub (x : ℝ) (m : ℤ) : ndist x ≤ |x - m| := round_le x m



































end LonelyRunner

namespace LonelyRunner.BadCover





















end LonelyRunner.BadCover

namespace LonelyRunner.LaminarCover

open Set





end LonelyRunner.LaminarCover

namespace LonelyRunner.Farey

theorem exists_determinant_one {r s : ℤ} (h : Int.gcd r s = 1) :
    ∃ a b : ℤ, b * r - a * s = 1 := by
  refine ⟨-Int.gcdB r s, Int.gcdA r s, ?_⟩
  have hb := Int.gcd_eq_gcd_ab r s
  rw [h] at hb
  norm_num at hb
  linear_combination -hb



theorem determinant_identity {a b r s : ℤ} (h : b * r - a * s = 1) (v c : ℤ) :
    (r * c - a * v) * s + (b * v - s * c) * r = v := by
  linear_combination v * h

/-- A denominator strictly between determinant-one fractions is at least their sum. -/
theorem denominator_bound {a b r s v c : ℤ}
    (h : b * r - a * s = 1) (hr : 0 < r) (hs : 0 < s)
    (hl : 0 < r * c - a * v) (hu : 0 < b * v - s * c) : r + s ≤ v := by
  have hd : 1 ≤ r * c - a * v := hl
  have he : 1 ≤ b * v - s * c := hu
  have hi := determinant_identity h v c
  nlinarith [mul_nonneg (sub_nonneg.mpr hd) (le_of_lt hs),
    mul_nonneg (sub_nonneg.mpr he) (le_of_lt hr)]

theorem no_small_denominator {a b r s v c : ℤ}
    (h : b * r - a * s = 1) (hr : 0 < r) (hs : 0 < s)
    (hv : v < r + s) :
    ¬ ((a : ℝ) / r * v < c ∧ (c : ℝ) < (b : ℝ) / s * v) := by
  rintro ⟨hl, hu⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hl' : (a : ℝ) * v < r * c := by
    have := (mul_lt_mul_iff_right₀ hrR).mpr hl
    field_simp at this
    nlinarith
  have hu' : (s : ℝ) * c < b * v := by
    have := (mul_lt_mul_iff_right₀ hsR).mpr hu
    field_simp at this
    nlinarith
  have hd : 0 < r * c - a * v := by exact_mod_cast sub_pos.mpr hl'
  have he : 0 < b * v - s * c := by exact_mod_cast sub_pos.mpr hu'
  exact (not_le.mpr hv) (denominator_bound h hr hs hd he)

theorem retained_not_dvd {n r v : ℤ} (hr : 0 < r) (hn : n ≤ 2 * r)
    (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) : ¬ r ∣ v := by
  rintro ⟨k, rfl⟩
  have hk : 0 < k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  have : k = 1 := by omega
  simp_all

theorem endpoint_residue_ne {a b r s v c : ℤ}
    (h : b * r - a * s = 1) (hv : ¬ r ∣ v) : a * v - r * c ≠ 0 := by
  intro hz
  apply hv
  refine ⟨b * v - s * c, ?_⟩
  have hi := determinant_identity h v c
  rw [show r * c - a * v = 0 by omega, zero_mul, zero_add] at hi
  simpa only [mul_comm] using hi.symm

theorem endpoint_distance {a b n r s v : ℤ}
    (h : b * r - a * s = 1) (hr : 0 < r) (hrn : r < n)
    (hv : ¬ r ∣ v) (c : ℤ) : (1 : ℝ) / n < |(a : ℝ) / r * v - c| := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_trans hr hrn)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hunit : (1 : ℝ) ≤ |(a : ℝ) * v - r * c| := by
    exact_mod_cast (Int.one_le_abs (endpoint_residue_ne h hv (c := c)))
  have heq : |(a : ℝ) / r * v - c| = |(a : ℝ) * v - r * c| / r := by
    calc
      _ = |((a : ℝ) * v - r * c) / r| := by congr 1; field_simp
      _ = _ := by rw [abs_div, abs_of_pos hrR]
  rw [heq]
  calc
    (1 : ℝ) / n < 1 / r := one_div_lt_one_div_of_lt hrR (by exact_mod_cast hrn)
    _ ≤ |(a : ℝ) * v - r * c| / r := div_le_div_of_nonneg_right hunit hrR.le

/-- Every retained speed is strictly lonely throughout the whole Farey interval. -/
theorem retained_strict {a b n r s v : ℤ} {t : ℝ}
    (h : b * r - a * s = 1) (hr : 0 < r) (hrs : r < s)
    (hsn : s < n) (hn : n ≤ 2 * r)
    (hv : 0 < v) (hvn : v < n) (hvr : v ≠ r) (hvs : v ≠ s)
    (ht : t ∈ Set.Icc ((a : ℝ) / r) ((b : ℝ) / s)) :
    (1 : ℝ) / n < ndist (t * v) := by
  have hs : 0 < s := lt_trans hr hrs
  have hvr' := retained_not_dvd hr hn hv hvn hvr
  have hvs' := retained_not_dvd hs (by omega : n ≤ 2 * s) hv hvn hvs
  have hrev : (-a) * s - (-b) * r = 1 := by nlinarith [h]
  let c : ℤ := round (t * v)
  have hA := endpoint_distance h hr (lt_trans hrs hsn) hvr' c
  have hB := endpoint_distance hrev hs hsn hvs' (-c)
  have hB' : (1 : ℝ) / n < |(b : ℝ) / s * v - c| := by
    convert hB using 1
    rw [← abs_neg ((b : ℝ) / s * v - c)]
    congr 1
    push_cast
    ring
  have hnc := no_small_denominator (c := c) h hr hs (by omega : v < r + s)
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hAt : (a : ℝ) / r * v ≤ t * v := mul_le_mul_of_nonneg_right ht.1 hvR.le
  have htB : t * v ≤ (b : ℝ) / s * v := mul_le_mul_of_nonneg_right ht.2 hvR.le
  change (1 : ℝ) / n < |t * v - c|
  rcases le_or_gt (c : ℝ) ((a : ℝ) / r * v) with hc | hc
  · rw [abs_of_nonneg (by linarith)] at hA ⊢
    linarith
  · have hcB : (b : ℝ) / s * v ≤ c := le_of_not_gt (fun hh => hnc ⟨hc, hh⟩)
    rw [abs_of_nonpos (by linarith)] at hB' ⊢
    linarith

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























/-- Integer form: there is a time strictly safe for every retained and inserted speed. -/
theorem strict_witness {n r s p q : ℤ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2 * r) (hrs : r < s) (hsn : s < n)
    (hcop : Int.gcd r s = 1) (hnp : n ≤ p) (hpq : p < q) :
    ∃ t : ℝ,
      (∀ v : ℤ, 0 < v → v < n → v ≠ r → v ≠ s → (1 : ℝ) / n < ndist (t * v)) ∧
      (1 : ℝ) / n < ndist (t * p) ∧ (1 : ℝ) / n < ndist (t * q) := by
  have hr : 0 < r := by omega
  obtain ⟨a, b, hab⟩ := exists_determinant_one hcop
  have hnc := not_covered hab hn hr hrs hsn hnp hpq
  push Not at hnc
  obtain ⟨t, ht, hpt, hqt⟩ := hnc
  refine ⟨t, ?_, ?_, ?_⟩
  · intro v hv hvn hvr hvs
    exact retained_strict hab hr hrs hsn hlarge hv hvn hvr hvs ht
  · simpa only [mul_comm t] using hpt
  · simpa only [mul_comm t] using hqt

/--
For `n ≥ 5`, deleting coprime `r,s` from `1,…,n-1`, with both deletions larger
than `(n-1)/2`, and inserting any `n ≤ p < q` gives a strictly lonely time.
In particular this configuration is not tight. There is no bound on `p` or `q`.
-/
theorem coprime_large_deletions {n r s p q : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2 * r) (hrs : r < s) (hsn : s < n)
    (hcop : Nat.Coprime r s) (hnp : n ≤ p) (hpq : p < q) :
    ∃ t : ℝ, ∀ v : ℕ,
      ((0 < v ∧ v < n ∧ v ≠ r ∧ v ≠ s) ∨ v = p ∨ v = q) →
      (1 : ℝ) / n < ndist (t * v) := by
  obtain ⟨t, hret, hpt, hqt⟩ := strict_witness
    (n := (n : ℤ)) (r := (r : ℤ)) (s := (s : ℤ)) (p := (p : ℤ)) (q := (q : ℤ))
    (by exact_mod_cast hn) (by exact_mod_cast hlarge)
    (by exact_mod_cast hrs) (by exact_mod_cast hsn)
    (by simpa only [Int.gcd_natCast_natCast] using hcop.gcd_eq_one)
    (by exact_mod_cast hnp) (by exact_mod_cast hpq)
  refine ⟨t, fun v hv => ?_⟩
  rcases hv with ⟨hv, hvn, hvr, hvs⟩ | rfl | rfl
  · have hh := hret v (by exact_mod_cast hv) (by exact_mod_cast hvn)
      (by exact_mod_cast hvr) (by exact_mod_cast hvs)
    simpa only [Int.cast_natCast] using hh
  · simpa only [Int.cast_natCast] using hpt
  · simpa only [Int.cast_natCast] using hqt

end LonelyRunner.CoprimeReplacements

namespace LonelyRunner.SingleDeletion

open BadCover





/-- Badness at 1/r, with r<n, is equivalent to divisibility (the forward half). -/
theorem dvd_of_bad {n r w : ℕ} (hr : 0 < r) (hrn : r < n)
    (h : ndist ((w:ℝ)*(1/r)) ≤ 1/n) : r ∣ w := by
  have hh := CoprimeReplacements.endpoint_exact (a := 1) (n := (n:ℤ))
    (r := (r:ℤ)) (w := (w:ℤ)) (c := round ((w:ℝ)*(1/r)))
    (by exact_mod_cast hr) (by exact_mod_cast hrn) (by simpa [ndist] using h)
  have hd : (r:ℤ) ∣ (w:ℤ) := ⟨round ((w:ℝ)*(1/r)), by linear_combination -hh⟩
  exact_mod_cast hd

/-- Removing a speed at least n/2 makes its reciprocal strictly safe for all
other baseline speeds. -/
theorem reciprocal_safe {n r v : ℕ} (hr : 0 < r) (hrn : r < n)
    (hlarge : n ≤ 2*r) (hv : 0 < v) (hvn : v < n) (hne : v ≠ r) :
    1/(n:ℝ) < ndist ((v:ℝ)*(1/r)) := by
  by_contra! h
  have hd := dvd_of_bad hr hrn h
  have hz := Farey.retained_not_dvd (n := (n:ℤ)) (r := (r:ℤ)) (v := (v:ℤ))
    (by exact_mod_cast hr) (by exact_mod_cast hlarge) (by exact_mod_cast hv)
    (by exact_mod_cast hvn) (by exact_mod_cast hne)
  exact hz (by exact_mod_cast hd)

end LonelyRunner.SingleDeletion

namespace LonelyRunner.BadCover











end LonelyRunner.BadCover

namespace LonelyRunner.MatchingArithmetic





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







/-- Original matching obstruction, retained as a compatibility wrapper. -/
theorem common_insertion_impossible {n r s p q : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hnp : n ≤ p) (hpq : p < q) (hg : 2 ≤ Nat.gcd r s)
    (hno : ¬ HasStrictTime n r s p q)
    (hcommon : (r ∣ p ∧ s ∣ p ∧ ¬r ∣ q) ∨ (r ∣ q ∧ s ∣ q ∧ ¬r ∣ p)) : False := by
  apply common_insertion_obstruction hn hlarge hrs hsn hnp hpq hg hno
  tauto

/-- With no strict time, the slower insertion cannot be divisible by both
large deletions. No separation or speed-ratio assumption is needed. -/
theorem slow_not_common {n r s p q : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hnp : n ≤ p) (hpq : p < q) (hno : ¬ HasStrictTime n r s p q)
    (hrp : r ∣ p) : ¬ s ∣ p := by
  intro hsp
  have hr : 0 < r := by omega
  have hg : 2 ≤ Nat.gcd r s := by
    have hgpos := Nat.gcd_pos_of_pos_left s hr
    by_contra! hh
    have hcop : Nat.Coprime r s := by change Nat.gcd r s=1; omega
    exact hno (CoprimeReplacements.coprime_large_deletions hn hlarge hrs hsn hcop hnp hpq)
  exact common_insertion_obstruction hn hlarge hrs hsn hnp hpq hg hno (Or.inl ⟨hrp,hsp⟩)

/-- Necessary distinct divisibility matching, without any bound on the inserted
speeds and without assuming the lonely runner conjecture. -/
theorem distinct_matching {n r s p q : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hnp : n ≤ p) (hpq : p < q) (hno : ¬ HasStrictTime n r s p q) :
    (r ∣ p ∧ s ∣ q) ∨ (r ∣ q ∧ s ∣ p) := by
  have hr : 0 < r := by omega
  have hs : 0 < s := by omega
  have hg : 2 ≤ Nat.gcd r s := by
    have hgpos := Nat.gcd_pos_of_pos_left s hr
    by_contra! hh
    have hcop : Nat.Coprime r s := by change Nat.gcd r s=1; omega
    exact hno (CoprimeReplacements.coprime_large_deletions hn hlarge hrs hsn hcop hnp hpq)
  have hrcover := cover_of_no_strict hno (t := (1:ℝ)/r) (fun v hv hvn hvr _ =>
    reciprocal_safe hr (lt_trans hrs hsn) hlarge hv hvn hvr)
  have hscover := cover_of_no_strict hno (t := (1:ℝ)/s) (fun v hv hvn _ hvs =>
    reciprocal_safe hs hsn (by omega) hv hvn hvs)
  have hdr : r ∣ p ∨ r ∣ q := hrcover.imp (dvd_of_bad hr (lt_trans hrs hsn)) (dvd_of_bad hr (lt_trans hrs hsn))
  have hds : s ∣ p ∨ s ∣ q := hscover.imp (dvd_of_bad hs hsn) (dvd_of_bad hs hsn)
  by_contra hmatch
  have hcommon : (r ∣ p ∧ s ∣ p ∧ ¬r ∣ q) ∨ (r ∣ q ∧ s ∣ q ∧ ¬r ∣ p) := by tauto
  exact common_insertion_impossible hn hlarge hrs hsn hnp hpq hg hno hcommon



end LonelyRunner.LargeDeletionMatching

namespace LonelyRunner.SeparatedBands

open BadCover









end LonelyRunner.SeparatedBands

namespace LonelyRunner

open Finset



























end LonelyRunner

namespace LonelyRunner

/-- `ndist` is 1-Lipschitz. -/
theorem ndist_le_add (x y : ℝ) : ndist x ≤ |x - y| + ndist y := by
  calc ndist x ≤ |x - round y| := ndist_le_abs_sub x (round y)
    _ = |(x - y) + (y - round y)| := by ring_nf
    _ ≤ |x - y| + |y - round y| := abs_add_le _ _
    _ = |x - y| + ndist y := rfl















end LonelyRunner

namespace LonelyRunner.FailedWindow

open Farey BadCover





/-- A nonintegral phase at a reduced denominator stays at least d/r from
the integers when d divides both the denominator and the other speed. -/
theorem center_distance {r z d a b c : ℤ}
    (hr : 0 < r) (hunit : a*b-c*r=1) (hnot : ¬ r ∣ z)
    (hdr : d ∣ r) (hdz : d ∣ z) :
    (d:ℝ)/r ≤ ndist ((z:ℝ)*((a:ℝ)/r)) := by
  let j := round ((z:ℝ)*((a:ℝ)/r))
  have hne : z*a-r*j ≠ 0 := by
    intro hh
    apply hnot
    refine ⟨b*j-c*z,?_⟩
    linear_combination -z*hunit+b*hh
  have hd : d ∣ z*a-r*j :=
    dvd_sub (dvd_mul_of_dvd_left hdz a) (dvd_mul_of_dvd_left hdr j)
  have hb : (d:ℝ) ≤ |(z:ℝ)*a-r*j| := by
    exact_mod_cast Int.le_abs_of_dvd hne hd
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have heq : ndist ((z:ℝ)*((a:ℝ)/r)) = |(z:ℝ)*a-r*j|/r := by
    change |(z:ℝ)*((a:ℝ)/r)-j| = _
    rw [← abs_of_pos hrR,← abs_div]
    congr 1
    rw [abs_of_pos hrR]
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right hb hrR.le

/-- A local arithmetic separation condition using a divisor of the deletion
and the other insertion makes a failed-window boundary safe. -/
theorem boundary_safe_of_common_divisor {n r m z d a b c : ℤ}
    (hn : 0 < n) (hr : 0 < r) (hm : 0 < m) (hz : 0 < z)
    (hunit : a*b-c*r=1) (hnot : ¬ r ∣ z) (hdr : d ∣ r) (hdz : d ∣ z)
    (hgap : m*r+z < n*m*d) :
    (1:ℝ)/n < ndist ((z:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hzR : (0:ℝ) < z := by exact_mod_cast hz
  have hden := mul_pos (mul_pos hnR hmR) hrR
  have hgapR : (1:ℝ)/n+(z:ℝ)/((n:ℝ)*m*r) < (d:ℝ)/r := by
    apply (mul_lt_mul_iff_right₀ hden).mp
    field_simp
    exact_mod_cast hgap
  have hdist := ndist_le_add ((z:ℝ)*((a:ℝ)/r))
    ((z:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r)))
  have heq : |(z:ℝ)*((a:ℝ)/r)-(z:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))| =
      (z:ℝ)/((n:ℝ)*m*r) := by
    have hh : (z:ℝ)*((a:ℝ)/r)-(z:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r)) =
        (z:ℝ)/((n:ℝ)*m*r) := by ring
    rw [hh,abs_of_pos (div_pos hzR hden)]
  rw [heq] at hdist
  have hcenter := center_distance hr hunit hnot hdr hdz
  linarith

end LonelyRunner.FailedWindow

namespace LonelyRunner.SeparatedReplacements

open LargeDeletionMatching SeparatedBands



theorem strict_swap_deletions {n r s p q : ℕ} :
    HasStrictTime n r s p q ↔ HasStrictTime n s r p q := by
  constructor <;> rintro ⟨t,ht⟩ <;> refine ⟨t,fun v hv => ht v ?_⟩ <;> tauto

theorem strict_swap_insertions {n r s p q : ℕ} :
    HasStrictTime n r s p q ↔ HasStrictTime n r s q p := by
  constructor <;> rintro ⟨t,ht⟩ <;> refine ⟨t,fun v hv => ht v ?_⟩ <;> tauto

















end LonelyRunner.SeparatedReplacements

namespace LonelyRunner.MixedReplacements

open LargeDeletionMatching SeparatedReplacements

/-- A divisor of the deletion and the other insertion gives a local
failed-window obstruction. -/
theorem gw_of_local_gap {n r s m z d : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrn : r < n) (hm : 2 ≤ m) (hz : 0 < z)
    (hnot : ¬ r ∣ z) (hdr : d ∣ r) (hdz : d ∣ z)
    (hgap : m*r+z < n*m*d) (hno : ¬ HasStrictTime n r s (m*r) z) : GW n r m := by
  intro b hab hfail hcop
  apply hno
  apply failed_window_escape_of_boundary hn hlarge hrn hm hab hfail hcop
  intro a c hunit
  apply FailedWindow.boundary_safe_of_common_divisor
    (d := (d:ℤ)) (by omega) (by omega) (by omega) (by exact_mod_cast hz) hunit
  · exact_mod_cast hnot
  · exact_mod_cast hdr
  · exact_mod_cast hdz
  · exact_mod_cast hgap

/-- In a matched configuration without a strict time, the faster insertion
must satisfy its own GW condition, for arbitrary distinct mixed multipliers.
The matched deletions may be in either order. -/
theorem matched_faster_window {n r s m k : ℕ}
    (hn : 5 ≤ n) (hrlarge : n ≤ 2*r) (hslarge : n ≤ 2*s)
    (hrn : r < n) (hsn : s < n) (hrs : r ≠ s)
    (hnp : n ≤ m*r) (hpq : m*r < k*s)
    (hno : ¬ HasStrictTime n r s (m*r) (k*s)) : GW n s k := by
  have hr : 0 < r := by omega
  have hk : 2 ≤ k := by
    by_contra! hh
    have : k ≤ 1 := by omega
    nlinarith
  have hswap : ¬ HasStrictTime n s r (m*r) (k*s) := fun ht =>
    hno (strict_swap_deletions.mpr ht)
  have hnot : ¬ s ∣ m*r := by
    rcases lt_or_gt_of_ne hrs with hh | hh
    · exact LargeDeletionMatching.slow_not_common hn hrlarge hh hsn hnp hpq hno
        (dvd_mul_left _ _)
    · intro hd
      exact LargeDeletionMatching.slow_not_common hn hslarge hh hrn hnp hpq hswap hd
        (dvd_mul_left _ _)
  have hg : 2 ≤ Nat.gcd r s := by
    have hgpos := Nat.gcd_pos_of_pos_left s hr
    by_contra! hh
    have hcop : Nat.Coprime r s := by change Nat.gcd r s=1; omega
    rcases lt_or_gt_of_ne hrs with hh | hh
    · exact hno (CoprimeReplacements.coprime_large_deletions hn hrlarge hh hsn hcop hnp hpq)
    · exact hswap (CoprimeReplacements.coprime_large_deletions hn hslarge hh hrn hcop.symm hnp hpq)
  have hgap : k*s+m*r < n*k*Nat.gcd r s := by
    have hks := Nat.mul_lt_mul_of_pos_left hsn (show 0 < k by omega)
    have hg' := Nat.mul_le_mul_left (n*k) hg
    nlinarith only [hpq,hks,hg']
  apply gw_of_local_gap (s := r) hn hslarge hsn hk (by omega) hnot
    (Nat.gcd_dvd_right r s)
    (dvd_mul_of_dvd_right (Nat.gcd_dvd_left r s) m) hgap
  intro ht
  exact hswap (strict_swap_insertions.mpr ht)

/-- For arbitrary insertions p<q, some distinct matching makes the faster
insertion q an individually valid GW acceleration. -/
theorem faster_matching_window {n r s p q : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hnp : n ≤ p) (hpq : p < q) (hno : ¬ HasStrictTime n r s p q) :
    ∃ m k : ℕ, (p=m*r ∧ q=k*s ∧ GW n s k) ∨
      (p=k*s ∧ q=m*r ∧ GW n r m) := by
  rcases distinct_matching hn hlarge hrs hsn hnp hpq hno with ⟨hrp,hsq⟩ | ⟨hrq,hsp⟩
  · obtain ⟨m,hm⟩ := hrp
    obtain ⟨k,hk⟩ := hsq
    have hm' : p=m*r := by simpa [mul_comm] using hm
    have hk' : q=k*s := by simpa [mul_comm] using hk
    refine ⟨m,k,Or.inl ⟨hm',hk',?_⟩⟩
    apply matched_faster_window (m := m) hn hlarge (by omega) (lt_trans hrs hsn) hsn hrs.ne
    · simpa only [← hm'] using hnp
    · simpa only [← hm',← hk'] using hpq
    · simpa only [← hm',← hk'] using hno
  · obtain ⟨m,hm⟩ := hrq
    obtain ⟨k,hk⟩ := hsp
    have hm' : q=m*r := by simpa [mul_comm] using hm
    have hk' : p=k*s := by simpa [mul_comm] using hk
    refine ⟨m,k,Or.inr ⟨hk',hm',?_⟩⟩
    apply matched_faster_window (m := k) hn (by omega) hlarge hsn (lt_trans hrs hsn) hrs.ne'
    · simpa only [← hk'] using hnp
    · simpa only [← hk',← hm'] using hpq
    · intro ht
      apply hno
      simpa only [← hk',← hm'] using strict_swap_deletions.mpr ht

/-- A valid GW window ends no later than r-1. At n=2r even the window
with multiplier two contains the unit r+1, so equality is impossible. -/
theorem gw_window_bound {n r m : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrn : r < n) (hm : 2 ≤ m)
    (hgw : GW n r m) : m*(n-r) ≤ r-1 := by
  have hr : 2 ≤ r := by omega
  have hfirst : m*(n-r) ≤ r+1 := by
    by_contra! hh
    exact hgw (r+1) (by omega) hh (by simp)
  have hstrict : n < 2*r := by
    by_contra! hh
    have heq : n-r=r := by omega
    rw [heq] at hfirst
    nlinarith
  have hcop : Nat.Coprime r (r-1) :=
    (Nat.coprime_self_sub_right (show 1 ≤ r by omega)).mpr (by simp)
  by_contra! hh
  exact hgw (r-1) (by omega) hh hcop





end LonelyRunner.MixedReplacements

namespace LonelyRunner.SeparatedMulti

open SeparatedReplacements SeparatedBands SingleDeletion





theorem exists_multiple {n r : ℕ} {R W : Finset ℕ}
    (_hn : 5 ≤ n) (hrR : r ∈ R) (hrlarge : n ≤ 2*r) (hrn : r < n)
    (hno : ¬ HasStrictTime n R W) : ∃ p, p ∈ W ∧ r ∣ p := by
  have hr : 0 < r := by omega
  by_contra! hh
  apply hno
  refine ⟨1/r,fun v hv => ?_⟩
  rcases hv with ⟨hv,hvn,hvR⟩ | hvW
  · exact reciprocal_safe hr hrn hrlarge hv hvn (by rintro rfl; exact hvR hrR)
  · by_contra! hbad
    exact hh v hvW (dvd_of_bad hr hrn hbad)





/-- Each deletion has an individually valid inserted multiple, without a bound on |R|. -/
theorem individual_repairs {n : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hR : ∀ r ∈ R, n ≤ 2*r ∧ r < n)
    (hW : ∀ q ∈ W, n ≤ q) (hsep : Separated n W)
    (hno : ¬ HasStrictTime n R W) :
    ∀ r ∈ R, ∃ p ∈ W, ∃ m : ℕ, 2 ≤ m ∧ p=m*r ∧ GW n r m := by
  intro r hrR
  obtain ⟨hrlarge,hrn⟩ := hR r hrR
  have hex := exists_multiple hn hrR hrlarge hrn hno
  let p := Nat.find hex
  have hpW : p ∈ W := (Nat.find_spec hex).1
  have hrp : r ∣ p := (Nat.find_spec hex).2
  obtain ⟨m,hm⟩ := hrp
  have hpm : p=m*r := by simpa [mul_comm] using hm
  have hm2 : 2 ≤ m := by
    have hnp := hW p hpW
    by_contra! hh
    have hle := Nat.mul_le_mul_right r (show m ≤ 1 by omega)
    omega
  refine ⟨p,hpW,m,hm2,hpm,?_⟩
  apply minimal_multiple_gw hn hrR hrlarge hrn hm2 (hpm ▸ hpW) hW hsep _ hno
  intro q hqW hrq
  rw [← hpm]
  exact Nat.find_min' hex ⟨hqW,hrq⟩

theorem distinct_valid_repairs {n r s m k : ℕ}
    (hn : 5 ≤ n) (hrlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hm : 2 ≤ m) (hk : 2 ≤ k) (hgw : GW n r m) : m*r ≠ k*s := by
  intro heq
  have hr : 0 < r := by omega
  have hkm : k < m := by
    by_contra! hh
    have hle := Nat.mul_le_mul_right r hh
    have hlt := Nat.mul_lt_mul_of_pos_left hrs (show 0 < k by omega)
    omega
  have hwin := MixedReplacements.gw_window_bound hn hrlarge (lt_trans hrs hsn) hm hgw
  have hrsub : r+(s-r)=s := Nat.add_sub_of_le hrs.le
  have hmul := Nat.mul_le_mul_right r (show k+1 ≤ m by omega)
  have hlow : r ≤ k*(s-r) := by nlinarith only [hrsub,hmul,heq]
  have hhigh : k*(s-r) ≤ m*(n-r) :=
    Nat.mul_le_mul hkm.le (Nat.sub_le_sub_right hsn.le r)
  omega









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





/-- The full two-large-deletion necessity theorem. Every configuration with
no strict lonely time has a distinct divisibility matching, and both matched
accelerations satisfy their individual Goddyn–Wong conditions. -/
theorem matching_windows {n r s p q : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hnp : n ≤ p) (hpq : p < q) (hno : ¬ HasStrictTime n r s p q) :
    ∃ m k : ℕ, ((p=m*r ∧ q=k*s) ∨ (p=k*s ∧ q=m*r)) ∧ GW n r m ∧ GW n s k := by
  obtain ⟨m,k,hmatch⟩ := faster_matching_window hn hlarge hrs hsn hnp hpq hno
  rcases hmatch with ⟨hpm,hqk,hgw⟩ | ⟨hpk,hqm,hgw⟩
  · refine ⟨m,k,Or.inl ⟨hpm,hqk⟩,?_,hgw⟩
    exact matched_slower_window (m := m) (k := k) hn hlarge (by omega) (by omega) hsn hrs.ne
      (by simpa [← hpm] using hnp) (by simpa [← hpm,← hqk] using hpq)
      (by simpa [← hpm,← hqk] using hno)
  · refine ⟨m,k,Or.inr ⟨hpk,hqm⟩,hgw,?_⟩
    have hswap : ¬ HasStrictTime n s r (k*s) (m*r) := by
      intro hh
      apply hno
      rw [hpk,hqm]
      exact strict_swap_deletions.mpr hh
    exact matched_slower_window (m := k) (k := m) hn (by omega) hlarge hsn (by omega) hrs.ne'
      (by simpa [← hpk] using hnp) (by simpa [← hpk,← hqm] using hpq) hswap



end LonelyRunner.MixedConverse

namespace LonelyRunner.SmallComponentRigidity

open SeparatedMulti SeparatedReplacements InteractionComponents



/-- Restoring deleted baseline speeds preserves the absence of strict times. -/
theorem no_strict_of_subset {n : ℕ} {D R W : Finset ℕ}
    (hD : D ⊆ R) (hno : ¬ HasStrictTime n R W) : ¬ HasStrictTime n D W := by
  rintro ⟨t,ht⟩
  apply hno
  refine ⟨t,fun v hv => ?_⟩
  rcases hv with ⟨hv,hvn,hvR⟩ | hvW
  · exact ht v (Or.inl ⟨hv,hvn,fun hvD => hvR (hD hvD)⟩)
  · exact ht v (Or.inr hvW)

/-- Individual valid repairs are automatically injective. -/
theorem repair_map {n : ℕ} {D C : Finset ℕ}
    (hn : 5 ≤ n) (hD : ∀ r ∈ D, n ≤ 2*r ∧ r < n)
    (hrep : HasRepairs n D C) :
    ∃ f : ℕ → ℕ, Set.MapsTo f (D : Set ℕ) (C : Set ℕ) ∧
      Set.InjOn f (D : Set ℕ) ∧
      ∀ r ∈ D, ∃ m : ℕ, 2 ≤ m ∧ f r=m*r ∧ GW n r m := by
  classical
  have hall : ∀ r : ℕ, ∃ p : ℕ, r ∈ D →
      p ∈ C ∧ ∃ m : ℕ, 2 ≤ m ∧ p=m*r ∧ GW n r m := by
    intro r
    by_cases hr : r ∈ D
    · obtain ⟨p,hp,m,hm,heq,hgw⟩ := hrep r hr
      exact ⟨p,fun _ => ⟨hp,m,hm,heq,hgw⟩⟩
    · exact ⟨0,fun h => (hr h).elim⟩
  choose f hf using hall
  refine ⟨f,fun r hr => (hf r hr).1,?_,fun r hr => (hf r hr).2⟩
  intro r hr s hs heq
  obtain ⟨m,hm,hfr,hgwr⟩ := (hf r hr).2
  obtain ⟨k,hk,hfs,hgws⟩ := (hf s hs).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hrs | hsr
  · exact distinct_valid_repairs hn (hD r hr).1 hrs (hD s hs).2 hm hk hgwr
      (by rw [← hfr,← hfs]; exact heq)
  · exact distinct_valid_repairs hn (hD s hs).1 hsr (hD r hr).2 hk hm hgws
      (by rw [← hfs,← hfr]; exact heq.symm)

theorem card_le_of_repairs {n : ℕ} {D C : Finset ℕ}
    (hn : 5 ≤ n) (hD : ∀ r ∈ D, n ≤ 2*r ∧ r < n)
    (hrep : HasRepairs n D C) : D.card ≤ C.card := by
  obtain ⟨f,hmap,hinj,_⟩ := repair_map hn hD hrep
  exact Finset.card_le_card_of_injOn f hmap hinj

theorem multiplier_ge_two {n r p m : ℕ} (hrn : r < n) (hnp : n ≤ p)
    (heq : p=m*r) : 2 ≤ m := by
  by_contra! hh
  have hle := Nat.mul_le_mul_right r (show m ≤ 1 by omega)
  omega

/-- The existing two-deletion theorem in finite-set form. -/
theorem ordered_pair_repairs {n r s p q : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrs : r < s) (hsn : s < n)
    (hnp : n ≤ p) (hpq : p < q)
    (hno : ¬ HasStrictTime n {r,s} {p,q}) : HasRepairs n {r,s} {p,q} := by
  have hno' : ¬ LargeDeletionMatching.HasStrictTime n r s p q := by
    simpa only [HasStrictTime,LargeDeletionMatching.HasStrictTime,
      Finset.mem_insert,Finset.mem_singleton,not_or,mul_comm] using hno
  obtain ⟨m,k,hmatch,hgwr,hgws⟩ :=
    MixedConverse.matching_windows hn hlarge hrs hsn hnp hpq hno'
  have hrn : r < n := lt_trans hrs hsn
  have hnq : n ≤ q := le_trans hnp hpq.le
  intro u hu
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu
  rcases hmatch with ⟨hpm,hqk⟩ | ⟨hpk,hqm⟩
  · rcases hu with rfl | rfl
    · exact ⟨p,by simp,m,multiplier_ge_two hrn hnp hpm,hpm,hgwr⟩
    · exact ⟨q,by simp,k,multiplier_ge_two hsn hnq hqk,hqk,hgws⟩
  · rcases hu with rfl | rfl
    · exact ⟨q,by simp,m,multiplier_ge_two hrn hnq hqm,hqm,hgwr⟩
    · exact ⟨p,by simp,k,multiplier_ge_two hsn hnp hpk,hpk,hgws⟩

/-- A component with at most two insertions, assigned at least as many
deletions, forces a valid individual repair for each deletion. -/
theorem small_component_repairs {n : ℕ} {D C : Finset ℕ}
    (hn : 5 ≤ n) (hD : ∀ r ∈ D, n ≤ 2*r ∧ r < n)
    (hC : ∀ p ∈ C, n ≤ p) (hsize : C.card ≤ 2) (hcard : C.card ≤ D.card)
    (hno : ¬ HasStrictTime n D C) : HasRepairs n D C := by
  by_cases hsmall : C.card ≤ 1
  · apply individual_repairs hn hD hC _ hno
    intro p hp q hq hne
    exact (hne (Finset.card_le_one.mp hsmall p hp q hq)).elim
  have htwo : C.card=2 := by omega
  have hDtwo : 2 ≤ D.card := by omega
  obtain ⟨p',q',hne,hCeq⟩ := Finset.card_eq_two.mp htwo
  have hsorted : ∃ p q : ℕ, p < q ∧ C={p,q} := by
    rcases lt_or_gt_of_ne hne with hh | hh
    · exact ⟨p',q',hh,hCeq⟩
    · exact ⟨q',p',hh,by simpa only [Finset.pair_comm] using hCeq⟩
  obtain ⟨p,q,hpq,rfl⟩ := hsorted
  intro r hrD
  have hex : ∃ s ∈ D, s ≠ r := by
    by_contra! hh
    have hle : D.card ≤ 1 := Finset.card_le_one.mpr
      (fun u hu v hv => (hh u hu).trans (hh v hv).symm)
    omega
  obtain ⟨s,hsD,hsr⟩ := hex
  have hpair : ({r,s} : Finset ℕ) ⊆ D := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hrD
    · exact (Finset.mem_singleton.mp hu) ▸ hsD
  have hpairno := no_strict_of_subset hpair hno
  rcases lt_or_gt_of_ne hsr.symm with hrs | hsr'
  · exact ordered_pair_repairs hn (hD r hrD).1 hrs (hD s hsD).2
      (hC p (by simp)) hpq hpairno r (by simp)
  · have hswap : ¬ HasStrictTime n {s,r} {p,q} := by
      simpa only [Finset.pair_comm] using hpairno
    exact ordered_pair_repairs hn (hD s hsD).1 hsr' (hD r hrD).2
      (hC p (by simp)) hpq hswap r (by simp)

/-- No component of size at most two can carry more deletions than insertions. -/
theorem small_component_capacity {n : ℕ} {D C : Finset ℕ}
    (hn : 5 ≤ n) (hD : ∀ r ∈ D, n ≤ 2*r ∧ r < n)
    (hC : ∀ p ∈ C, n ≤ p) (hsize : C.card ≤ 2)
    (hno : ¬ HasStrictTime n D C) : D.card ≤ C.card := by
  by_cases hcard : C.card ≤ D.card
  · exact card_le_of_repairs hn hD (small_component_repairs hn hD hC hsize hcard hno)
  · omega





















end LonelyRunner.SmallComponentRigidity

open LonelyRunner
open LonelyRunner.SmallComponentRigidity
open SeparatedMulti SeparatedReplacements InteractionComponents

/-- Balanced upper-half replacements with components of size at most two
and no strict lonely time admit a bijective Goddyn--Wong matching.
Neither a divisibility matching nor a bound on n is assumed. -/
theorem solution {n : ℕ} {R W : Finset ℕ}
    (hn : 5 ≤ n) (hR : ∀ r ∈ R, n ≤ 2*r ∧ r < n)
    (hW : ∀ p ∈ W, n ≤ p) (hparts : PairComponents n W)
    (hcard : R.card=W.card) (hno : ¬ HasStrictTime n R W) :
    ∃ f : ℕ → ℕ, Set.BijOn f (R : Set ℕ) (W : Set ℕ) ∧
      ∀ r ∈ R, ∃ m : ℕ, 2 ≤ m ∧ f r=m*r ∧ GW n r m := by
  classical
  obtain ⟨B,hunion,hdisj,hB⟩ := hparts
  have hsub (C : Finset ℕ) (hCB : C ∈ B) : C ⊆ W := by
    intro p hp
    rw [← hunion]
    exact Finset.mem_biUnion.mpr ⟨C,hCB,hp⟩
  have hown : ∀ r : ℕ, ∃ C : Finset ℕ, r ∈ R → C ∈ B ∧
      ∃ m : ℕ, 0 < m ∧ m*r ∈ C ∧ ∀ q ∈ W, r ∣ q → m*r ≤ q := by
    intro r
    by_cases hrR : r ∈ R
    · have hex := exists_multiple hn hrR (hR r hrR).1 (hR r hrR).2 hno
      let p := Nat.find hex
      have hpW : p ∈ W := (Nat.find_spec hex).1
      obtain ⟨m,hm⟩ := (Nat.find_spec hex).2
      have hpm : p=m*r := by simpa only [mul_comm] using hm
      have hm2 := multiplier_ge_two (hR r hrR).2 (hW p hpW) hpm
      have hpB : p ∈ B.biUnion id := by rw [hunion]; exact hpW
      obtain ⟨C,hCB,hpC⟩ := Finset.mem_biUnion.mp hpB
      refine ⟨C,fun _ => ⟨hCB,m,by omega,?_,?_⟩⟩
      · simpa only [id_eq,hpm] using hpC
      · intro q hqW hrq
        rw [← hpm]
        exact Nat.find_min' hex ⟨hqW,hrq⟩
    · exact ⟨∅,fun hh => (hrR hh).elim⟩
  choose owner howner using hown
  let D : Finset ℕ → Finset ℕ := fun C => R.filter (fun r => owner r=C)
  have hDsub (C : Finset ℕ) : D C ⊆ R := Finset.filter_subset _ _
  have hlocal (C : Finset ℕ) (hCB : C ∈ B) : ¬ HasStrictTime n (D C) C := by
    apply ComponentRestoration.restore_outside_cut hn hR (hDsub C) (hsub C hCB)
      (fun p hp => lt_of_lt_of_le (by omega : 0 < n) (hW p hp)) (hB C hCB).2 _ hno
    intro r hrD
    obtain ⟨hrR,hrC⟩ := Finset.mem_filter.mp hrD
    have hh := (howner r hrR).2
    simpa only [hrC] using hh
  have hcap (C : Finset ℕ) (hCB : C ∈ B) : (D C).card ≤ C.card :=
    small_component_capacity hn (fun r hr => hR r (hDsub C hr))
      (fun p hp => hW p (hsub C hCB hp)) (hB C hCB).1 (hlocal C hCB)
  have hsumD : R.card = ∑ C ∈ B, (D C).card :=
    Finset.card_eq_sum_card_fiberwise (fun r hr => (howner r hr).1)
  have hsumC : W.card = ∑ C ∈ B, C.card := by
    rw [← hunion,Finset.card_biUnion hdisj]
    rfl
  have heq (C : Finset ℕ) (hCB : C ∈ B) : (D C).card=C.card := by
    by_contra hh
    have hlt : (D C).card < C.card := by have := hcap C hCB; omega
    have hsumlt := Finset.sum_lt_sum hcap ⟨C,hCB,hlt⟩
    omega
  have hrep : HasRepairs n R W := by
    intro r hrR
    let C := owner r
    have hCB : C ∈ B := (howner r hrR).1
    have hrD : r ∈ D C := Finset.mem_filter.mpr ⟨hrR,rfl⟩
    have hrepC := small_component_repairs hn (fun s hs => hR s (hDsub C hs))
      (fun p hp => hW p (hsub C hCB hp)) (hB C hCB).1 (heq C hCB).ge (hlocal C hCB)
    obtain ⟨p,hp,m,hm,hpm,hgw⟩ := hrepC r hrD
    exact ⟨p,hsub C hCB hp,m,hm,hpm,hgw⟩
  obtain ⟨f,hmap,hinj,hf⟩ := repair_map hn hR hrep
  have himage : R.image f=W := by
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
      exact hmap hr
    · rw [Finset.card_image_of_injOn hinj,hcard]
  refine ⟨f,⟨hmap,hinj,?_⟩,hf⟩
  intro p hp
  have hp' : p ∈ R.image f := by rw [himage]; exact hp
  exact Finset.mem_image.mp hp'
