-- Prove2me | solution 1 for LonelyRunner.MixedConverse.matched_slower_window
-- status  : ACCEPTED   (prove)
-- author  : @Whunt003
-- created : 2026-10-07T19:01:42.668218+00:00
-- url     : https://prove2.me/submissions/14961424-8c2e-45f1-85f5-8f259f8d3037

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs
import Theorems.Thm_LonelyRunner_CoprimeReplacements_not_covered
import Theorems.Thm_LonelyRunner_FailedFlank_covered_flank_band
import Theorems.Thm_LonelyRunner_LargeDeletionMatching_common_insertion_obstruction
import Theorems.Thm_LonelyRunner_MixedArithmetic_contradiction
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









end LonelyRunner.SingleDeletion

namespace LonelyRunner.BadCover











end LonelyRunner.BadCover

namespace LonelyRunner.MatchingArithmetic





end LonelyRunner.MatchingArithmetic

namespace LonelyRunner.LargeDeletionMatching

open BadCover SingleDeletion













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























end LonelyRunner.SeparatedMulti

namespace LonelyRunner.InteractionComponents

open Set























end LonelyRunner.InteractionComponents

namespace LonelyRunner.GWArithmetic

open SeparatedReplacements

/-- A positive multiplicative interval of ratio p contains a power of p. -/
theorem power_in_window {c p : ℕ} (hc : 0 < c) (hp : 2 ≤ p) :
    ∃ j : ℕ, c ≤ p^j ∧ p^j < p*c := by
  by_cases hc1 : c=1
  · exact ⟨0,by simp [hc1],by simp [hc1]; omega⟩
  have hc2 : 1 < c := by omega
  have hp1 : 1 < p := by omega
  refine ⟨Nat.clog p c,Nat.le_pow_clog hp1 c,?_⟩
  have hh := Nat.mul_lt_mul_of_pos_left (Nat.pow_pred_clog_lt_self hp1 hc2)
    (show 0 < p by omega)
  have hlog := Nat.clog_pos hp1 hc2
  simpa [← pow_succ',Nat.pred_eq_sub_one,Nat.sub_add_cancel (show 1 ≤ Nat.clog p c by omega)] using hh

theorem deficit_at_least_two {n s k : ℕ} (hsn : s < n) (hk : 2 ≤ k)
    (hgw : GW n s k) : 2 ≤ n-s := by
  by_contra! hh
  have heq : n-s=1 := by omega
  exact hgw 1 (by omega) (by simpa [heq] using (show 1 < k by omega)) (by simp)

/-- Every prime at most the multiplier divides the accelerated speed. -/
theorem small_prime_dvd {n s k p : ℕ} (hsn : s < n)
    (hgw : GW n s k) (hp : Nat.Prime p) (hpk : p ≤ k) : p ∣ s := by
  by_contra hnot
  obtain ⟨j,hlo,hhi⟩ := power_in_window (Nat.sub_pos_of_lt hsn) hp.two_le
  apply hgw (p^j) hlo (lt_of_lt_of_le hhi (Nat.mul_le_mul_right (n-s) hpk))
  exact hp.coprime_pow_of_not_dvd hnot

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

theorem prime_in_window_dvd {n s k p : ℕ} (hgw : GW n s k)
    (hp : Nat.Prime p) (hlo : n-s ≤ p) (hhi : p < k*(n-s)) : p ∣ s := by
  by_contra hh
  exact hgw p hlo hhi (hp.coprime_iff_not_dvd.mpr hh).symm

theorem primorial_dvd {n s k : ℕ} (hsn : s < n) (hgw : GW n s k) :
    primorial k ∣ s := by
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.prime
  · intro p hp
    obtain ⟨hpk,hprime⟩ := Finset.mem_filter.mp hp
    exact small_prime_dvd hsn hgw hprime (by simpa using hpk)

/-- Apart from k=4, the product of primes up to k is at least 2k. -/
theorem twice_le_primorial {k : ℕ} (hk : 3 ≤ k) (hk4 : k ≠ 4) :
    2*k ≤ primorial k := by
  by_cases hk3 : k=3
  · subst k
    decide
  have hk5 : 5 ≤ k := by omega
  have hP30 : 30 ≤ primorial k := by
    have hh := primorial_mono hk5
    norm_num [primorial,Finset.prod_range_succ] at hh ⊢
    exact hh
  have hd2 : 2 ∣ primorial k := Nat.prime_two.dvd_primorial_iff.mpr (by omega)
  obtain ⟨H,hH⟩ := hd2
  have hH15 : 15 ≤ H := by omega
  have hnot2 : ¬ 2 ∣ H := by
    intro hh
    apply (Nat.squarefree_iff_prime_squarefree.mp (squarefree_primorial k)) 2 Nat.prime_two
    rw [hH]
    exact Nat.mul_dvd_mul_left 2 hh
  have hco2 : Nat.Coprime 2 H := Nat.prime_two.coprime_iff_not_dvd.mpr hnot2
  have hzP : Nat.Coprime (H-2) (primorial k) := by
    rw [hH,Nat.coprime_mul_iff_right]
    exact ⟨(Nat.coprime_sub_self_left (by omega)).mpr hco2.symm,
      (Nat.coprime_self_sub_left (by omega)).mpr hco2⟩
  obtain ⟨p,hp,hpz⟩ := Nat.exists_prime_and_dvd (show H-2 ≠ 1 by omega)
  have hkp : k < p := by
    by_contra! hh
    have hpP := hp.dvd_primorial_iff.mpr hh
    have hone := Nat.eq_one_of_dvd_coprimes hzP hpz hpP
    exact hp.ne_one hone
  have hpzle := Nat.le_of_dvd (show 0 < H-2 by omega) hpz
  omega

/-- Bertrand supplies a prime strictly between half of kc and kc, and this
prime is beyond k and at least c. -/
theorem half_window_prime {k c : ℕ} (hk : 3 ≤ k) (hc : 2 ≤ c) :
    ∃ t : ℕ, Nat.Prime t ∧ k < t ∧ c ≤ t ∧ k*c < 2*t ∧ t < k*c := by
  obtain ⟨t,ht,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (k*c/2)
    (by
      have : 6 ≤ k*c := by nlinarith
      omega)
  have hmod := Nat.mod_lt (k*c) (by norm_num : 0 < 2)
  have hdiv := Nat.mod_add_div (k*c) 2
  have hkc : 2*k ≤ k*c := by nlinarith
  have hcc : 2*c ≤ k*c := by nlinarith
  have htlt : t < k*c := by
    have htle : t ≤ k*c := by omega
    by_contra! hh
    have heq : t=k*c := by omega
    have hkd : k ∣ t := by rw [heq]; exact dvd_mul_right k c
    rcases ht.eq_one_or_self_of_dvd k hkd with h | h
    · omega
    · nlinarith
  exact ⟨t,ht,by omega,by omega,by omega,htlt⟩

/-- General growth away from the exceptional primorial value k=4. -/
theorem growth_ne_four {n s k : ℕ} (hs : 0 < s) (hsn : s < n)
    (hk : 3 ≤ k) (hk4 : k ≠ 4) (hgw : GW n s k) : k*k*(n-s) < s := by
  have hc := deficit_at_least_two hsn (by omega) hgw
  obtain ⟨t,ht,hkt,hct,hhalf,hend⟩ := half_window_prime hk hc
  have htd : t ∣ s := prime_in_window_dvd hgw ht hct hend
  have hcop : Nat.Coprime (primorial k) t := by
    apply Nat.Coprime.symm
    apply ht.coprime_iff_not_dvd.mpr
    intro hh
    have : t ≤ k := ht.dvd_primorial_iff.mp hh
    omega
  have hprod := hcop.mul_dvd_of_dvd_of_dvd (primorial_dvd hsn hgw) htd
  have hle := Nat.le_of_dvd hs hprod
  have hP := twice_le_primorial hk hk4
  have hmul := Nat.mul_le_mul_right t hP
  nlinarith [Nat.mul_lt_mul_of_pos_left hhalf (show 0 < k by omega)]

/-- Strict version of Bertrand for an integer lower endpoint at least two. -/
theorem prime_double {c : ℕ} (hc : 2 ≤ c) :
    ∃ p : ℕ, Nat.Prime p ∧ c < p ∧ p < 2*c := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul c (by omega)
  refine ⟨p,hp,hlo,?_⟩
  by_contra! hh
  have heq : p=2*c := by omega
  have htwo : 2 ∣ p := by rw [heq]; exact dvd_mul_right 2 c
  rcases hp.eq_one_or_self_of_dvd 2 htwo with hh | hh
  · omega
  · omega

theorem coprime_six {p : ℕ} (hp : Nat.Prime p) (hbig : 3 < p) :
    Nat.Coprime 6 p := by
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  rw [show (6:ℕ)=2*3 by norm_num,hp.dvd_mul] at hd
  rcases hd with hd | hd
  · have := Nat.le_of_dvd (by norm_num : 0 < (2:ℕ)) hd
    omega
  · have := Nat.le_of_dvd (by norm_num : 0 < (3:ℕ)) hd
    omega

theorem six_dvd {n s k : ℕ} (hsn : s < n) (hk : 3 ≤ k) (hgw : GW n s k) :
    6 ∣ s := by
  have h2 := small_prime_dvd hsn hgw Nat.prime_two (show 2 ≤ k by omega)
  have h3 := small_prime_dvd hsn hgw Nat.prime_three hk
  exact (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2 h3

theorem growth_four {n s : ℕ} (hs : 0 < s) (hsn : s < n) (hgw : GW n s 4) :
    4*4*(n-s) < s := by
  have hc := deficit_at_least_two hsn (by norm_num) hgw
  have h6 := six_dvd hsn (by norm_num : 3 ≤ 4) hgw
  by_cases hc4 : 4 ≤ n-s
  · obtain ⟨u,hu,hclu,huc⟩ := prime_double (show 2 ≤ n-s by omega)
    obtain ⟨v,hv,hcv,hvc⟩ := prime_double (show 2 ≤ 2*(n-s) by omega)
    have hud := prime_in_window_dvd hgw hu (by omega) (by omega)
    have hvd := prime_in_window_dvd hgw hv (by omega) (by omega)
    have h6u := coprime_six hu (by omega)
    have h6v := coprime_six hv (by omega)
    have huv : Nat.Coprime u v := (hu.coprime_iff_not_dvd).mpr (by
      intro hh
      rcases hv.eq_one_or_self_of_dvd u hh with hh | hh
      · exact hu.ne_one hh
      · omega)
    have h6ud := h6u.mul_dvd_of_dvd_of_dvd h6 hud
    have hprod := (h6v.mul_left huv).mul_dvd_of_dvd_of_dvd h6ud hvd
    have hle := Nat.le_of_dvd hs hprod
    have hmul := Nat.mul_lt_mul_of_pos_left hcv hu.pos
    nlinarith [Nat.mul_lt_mul_of_pos_right hclu (show 0 < n-s by omega)]
  · have h5 := prime_in_window_dvd hgw (by decide : Nat.Prime 5)
      (by omega) (by omega)
    have h7 := prime_in_window_dvd hgw (by decide : Nat.Prime 7)
      (by omega) (by omega)
    have h30 := (show Nat.Coprime 6 5 by decide).mul_dvd_of_dvd_of_dvd h6 h5
    have h210 := (show Nat.Coprime 30 7 by decide).mul_dvd_of_dvd_of_dvd h30 h7
    have hle := Nat.le_of_dvd hs h210
    omega

/-- A valid acceleration by k≥3 forces the deleted speed beyond k² times
its deficit. This is unconditional and uses only proved prime arithmetic. -/
theorem quadratic_growth {n s k : ℕ} (hs : 0 < s) (hsn : s < n)
    (hk : 3 ≤ k) (hgw : GW n s k) : k*k*(n-s) < s := by
  by_cases hk4 : k=4
  · subst k
    exact growth_four hs hsn hgw
  · exact growth_ne_four hs hsn hk hk4 hgw





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



/-- The two ends of a covered failed flank yield simultaneous integer
constraints. The far-end inequality is stronger than endpoint blocking. -/
theorem flank_arithmetic {n r m b a c q j : ℤ}
    (hn : 0 < n) (hr : 0 < r) (hm : 0 < m) (hb : 0 < b)
    (hunit : a*b-c*r=1)
    (hnear : |(q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j| ≤ 1/n)
    (hfar : |(q:ℝ)*((a:ℝ)/r-((n:ℝ)-r)/((n:ℝ)*r*b))-j| ≤ 1/n) :
    let D := q*a-r*j
    let h := j*b-q*c
    D*b=q-r*h ∧ |n*m*D-q| ≤ m*r ∧ |q-n*h| ≤ b := by
  dsimp
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hunitR : (a:ℝ)*b-(c:ℝ)*r=1 := by exact_mod_cast hunit
  refine ⟨by linear_combination q*hunit,?_,?_⟩
  · have heq : (n:ℝ)*m*r*((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j) =
        (n:ℝ)*m*((q:ℝ)*a-r*j)-q := by field_simp; ring
    have hh : |(n:ℝ)*m*((q:ℝ)*a-r*j)-q| ≤ (m:ℝ)*r := by
      calc
        _ = ((n:ℝ)*m*r)*|(q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j| := by
          rw [← heq,abs_mul,abs_of_pos (mul_pos (mul_pos hnR hmR) hrR)]
        _ ≤ ((n:ℝ)*m*r)*(1/n) :=
          mul_le_mul_of_nonneg_left hnear (mul_pos (mul_pos hnR hmR) hrR).le
        _ = _ := by field_simp
    exact_mod_cast hh
  · have heq : (n:ℝ)*b*((q:ℝ)*((a:ℝ)/r-((n:ℝ)-r)/((n:ℝ)*r*b))-j) =
        (q:ℝ)-n*((j:ℝ)*b-q*c) := by
      field_simp
      nlinarith only [congrArg (fun x : ℝ => (n:ℝ)*q*x) hunitR]
    have hh : |(q:ℝ)-n*((j:ℝ)*b-q*c)| ≤ (b:ℝ) := by
      calc
        _ = ((n:ℝ)*b)*|(q:ℝ)*((a:ℝ)/r-((n:ℝ)-r)/((n:ℝ)*r*b))-j| := by
          rw [← heq,abs_mul,abs_of_pos (mul_pos hnR hbR)]
        _ ≤ ((n:ℝ)*b)*(1/n) := mul_le_mul_of_nonneg_left hfar (mul_pos hnR hbR).le
        _ = _ := by field_simp
    exact_mod_cast hh



/-- Actual no-strict-time instances supply the full integer constraints for
each failed unit. The determinant retains any common divisor of r and q. -/
theorem arithmetic_of_no_strict {n r s m b q g : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrn : r < n)
    (hm : 2 ≤ m) (hmn : m+1 ≤ n) (hq : 0 < q)
    (hab : n-r ≤ b) (hfail : b < m*(n-r)) (hcop : Nat.Coprime r b)
    (hgr : g ∣ r) (hgq : g ∣ q)
    (hno : ¬ HasStrictTime n r s (m*r) q) :
    ∃ D h : ℤ, (g:ℤ) ∣ D ∧ D*b=(q:ℤ)-(r:ℤ)*h ∧
      |(n:ℤ)*m*D-q| ≤ (m:ℤ)*r ∧ |(q:ℤ)-n*h| ≤ b := by
  obtain ⟨a',c',hunit'⟩ := Farey.exists_determinant_one
    (r := (r:ℤ)) (s := (b:ℤ)) (by simpa using hcop.gcd_eq_one)
  let a := -a'
  let c := -c'
  have hunit : a*(b:ℤ)-c*(r:ℤ)=1 := by dsimp [a,c]; nlinarith only [hunit']
  obtain ⟨j,hnear,hfar⟩ := covered_flank_band hn hlarge hrn hm hmn hq hab hfail hunit hno
  have hh := flank_arithmetic (n := (n:ℤ)) (r := (r:ℤ)) (m := (m:ℤ))
    (b := (b:ℤ)) (q := (q:ℤ)) (a := a) (c := c) (j := j)
    (by omega) (by omega) (by omega) (by omega) hunit
    (by simpa using hnear) (by simpa using hfar)
  refine ⟨(q:ℤ)*a-(r:ℤ)*j,j*(b:ℤ)-(q:ℤ)*c,?_,hh⟩
  exact dvd_sub (dvd_mul_of_dvd_left (by exact_mod_cast hgq) a)
    (dvd_mul_of_dvd_left (by exact_mod_cast hgr) j)

end LonelyRunner.FailedFlank

namespace LonelyRunner.FlankReduction

/-- A common divisor of size at least two makes the near-end determinant
unique, because its permitted interval has length less than two. -/
theorem near_unique {n r m q g D E : ℤ}
    (hr : 0 < r) (hrn : r < n) (hm : 0 < m) (hg : 2 ≤ g)
    (hgD : g ∣ D) (hgE : g ∣ E)
    (hD : |n*m*D-q| ≤ m*r) (hE : |n*m*E-q| ≤ m*r) : D=E := by
  have hnm : 0 < n*m := mul_pos (lt_trans hr hrn) hm
  have impossible (A B : ℤ) (hAB : A < B) (hga : g ∣ A) (hgb : g ∣ B)
      (ha : |n*m*A-q| ≤ m*r) (hb : |n*m*B-q| ≤ m*r) : False := by
    have hge := Int.le_abs_of_dvd (by omega : B-A ≠ 0) (dvd_sub hgb hga)
    rw [abs_of_pos (by omega : 0 < B-A)] at hge
    have hstep : 2 ≤ B-A := by omega
    have hh := mul_le_mul_of_nonneg_left hstep hnm.le
    have hleft := (abs_le.mp ha).1
    have hright := (abs_le.mp hb).2
    have hstrict := mul_lt_mul_of_pos_left hrn hm
    nlinarith only [hh,hleft,hright,hstrict]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hh | hh
  · exact impossible D E hh hgD hgE hD hE
  · exact impossible E D hh hgE hgD hE hD

/-- At the far end, the band index can differ from k by at most one. -/
theorem far_index {n k c b h : ℤ}
    (hn : 0 < n) (hkc : 0 < k*c) (hkcn : k*c < n) (hbn : b < n)
    (hfar : |k*(n-c)-n*h| ≤ b) : h=k-1 ∨ h=k := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hfar
  have hlow : k-1 ≤ h := by
    by_contra! hh
    have hh' : h ≤ k-2 := by omega
    have hmul := mul_le_mul_of_nonneg_left hh' hn.le
    nlinarith only [hmul,hhi,hkcn,hbn]
  have hhigh : h ≤ k := by
    by_contra! hh
    have hh' : k+1 ≤ h := by omega
    have hmul := mul_le_mul_of_nonneg_left hh' hn.le
    nlinarith only [hmul,hlo,hkc,hbn]
  omega

/-- The wrapped index k-1 is impossible at the least failed unit once the
GW growth bound S>k²c is supplied. -/
theorem no_wrap {n r s a c m k b D : ℤ}
    (hna : n=r+a) (hnc : n=s+c) (ha : 0 < a) (hc : 0 < c)
    (hm : 2 ≤ m) (hmk : m < k) (hD : 0 < D)
    (hbr : b < r) (hbfail : b < m*a) (hfar : n-k*c ≤ b)
    (hnear : m*D < k+m) (hid : D*b=k*s-(k-1)*r)
    (hgrowth : k*k*c < s) : False := by
  have hak : a < k*c := by omega
  have hstep : m*D-k+1 ≤ m := by omega
  have hstep' := mul_le_mul_of_nonneg_right hstep ha.le
  have hbfail' := mul_lt_mul_of_pos_left hbfail hD
  have hak' := mul_lt_mul_of_pos_left hak (show 0 < m by omega)
  have hkc : 0 < k*c := mul_pos (by omega) hc
  have hmk' := mul_le_mul_of_nonneg_right (show m+1 ≤ k by omega) hkc.le
  have hnlt : n < (m*D-k+1)*a+k*c := by
    nlinarith only [hbfail',hid,hna,hnc,
      congrArg (fun x : ℤ => k*x) hna,congrArg (fun x : ℤ => k*x) hnc]
  nlinarith only [hnlt,hstep',hak',hmk',hgrowth,hnc,hc]



/-- The half-way deletion is incompatible with the near determinant and the
GW growth bound. For b=r+1, its inverse is 1, giving r ∣ D+kc. -/
theorem exclude_halfway {r c m k D : ℤ}
    (hc : 2 ≤ c) (hm : 2 ≤ m) (hk : 3 ≤ k) (hD : 2 ≤ D)
    (hnear : m*D < k+m) (hdiv : r ∣ D+k*c)
    (hgrowth : k*k*c < 2*r-c) : False := by
  have hDk : D < k := by
    nlinarith [mul_nonneg (show 0 ≤ m-2 by omega) (show 0 ≤ D-1 by omega)]
  have hpos : 0 < D+k*c := by nlinarith
  have hle := Int.le_abs_of_dvd hpos.ne' hdiv
  rw [abs_of_pos hpos] at hle
  have hbase : 2 ≤ (k-1)*c := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbase (show 0 ≤ k-1 by omega)
  nlinarith only [hDk,hle,hgrowth,hmul]







end LonelyRunner.FlankReduction

namespace LonelyRunner.MixedNormalize

open SeparatedReplacements SecondUnit GWArithmetic



end LonelyRunner.MixedNormalize

namespace LonelyRunner.MixedArithmetic

open SeparatedReplacements GWArithmetic GWGrowth FlankReduction SecondUnit



end LonelyRunner.MixedArithmetic

namespace LonelyRunner.NearData

open LargeDeletionMatching SeparatedReplacements

theorem band {n r s m q b : ℕ}
    (hn : 5 ≤ n) (hlarge : n ≤ 2*r) (hrn : r < n) (hm : 2 ≤ m)
    (hab : n-r ≤ b) (hfail : b < m*(n-r)) (hcop : Nat.Coprime r b)
    (hno : ¬ HasStrictTime n r s (m*r) q) :
    ∃ a c j : ℤ, a*(b:ℤ)-c*(r:ℤ)=1 ∧
      |(q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j| ≤ 1/n := by
  have hex : ∃ a c : ℤ, a*(b:ℤ)-c*(r:ℤ)=1 ∧
      ndist ((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))) ≤ 1/n := by
    by_contra! hh
    exact hno (failed_window_escape_of_boundary hn hlarge hrn hm hab hfail hcop hh)
  obtain ⟨a,c,hu,hbad⟩ := hex
  exact ⟨a,c,round ((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))),hu,hbad⟩

theorem scale {n r m q a j : ℤ} (hn : 0 < n) (hr : 0 < r) (hm : 0 < m)
    (hnear : |(q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j| ≤ 1/n) :
    |n*m*(q*a-r*j)-q| ≤ m*r := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have heq : (n:ℝ)*m*r*((q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j) =
      (n:ℝ)*m*((q:ℝ)*a-r*j)-q := by field_simp; ring
  have hh : |(n:ℝ)*m*((q:ℝ)*a-r*j)-q| ≤ (m:ℝ)*r := by
    calc
      _ = ((n:ℝ)*m*r)*|(q:ℝ)*((a:ℝ)/r-1/((n:ℝ)*m*r))-j| := by
        rw [← heq,abs_mul,abs_of_pos (mul_pos (mul_pos hnR hmR) hrR)]
      _ ≤ ((n:ℝ)*m*r)*(1/n) :=
        mul_le_mul_of_nonneg_left hnear (mul_pos (mul_pos hnR hmR) hrR).le
      _ = _ := by field_simp
  exact_mod_cast hh

theorem order {n r s m k D g : ℤ}
    (hn : 0 < n) (hrn : r < n) (hsn : s < n) (hm : 0 < m) (hk : 0 < k)
    (hpq : m*r < k*s) (hg : 2 ≤ g) (hgD : g ∣ D)
    (hnear : |n*m*D-k*s| ≤ m*r) : 2 ≤ D ∧ m*D < k+m := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp hnear
  have hDpos : 0 < D := by
    by_contra! hh
    have hmul := mul_nonpos_of_nonneg_of_nonpos (mul_pos hn hm).le hh
    nlinarith only [hmul,hlo,hpq]
  have hDg := Int.le_abs_of_dvd hDpos.ne' hgD
  rw [abs_of_pos hDpos] at hDg
  refine ⟨by omega,?_⟩
  have hr' := mul_lt_mul_of_pos_left hrn hm
  have hs' := mul_lt_mul_of_pos_left hsn hk
  have hineq : n*(m*D) < n*(k+m) := by nlinarith only [hhi,hr',hs']
  exact (mul_lt_mul_iff_right₀ hn).mp (by simpa [mul_comm] using hineq)

end LonelyRunner.NearData

namespace LonelyRunner.MixedConverse

open LargeDeletionMatching SeparatedReplacements MixedReplacements
open GWArithmetic GWGrowth FlankReduction









end LonelyRunner.MixedConverse

namespace LonelyRunner.SmallComponentRigidity

open SeparatedMulti SeparatedReplacements InteractionComponents





































end LonelyRunner.SmallComponentRigidity

open LonelyRunner
open LonelyRunner.MixedConverse
open LargeDeletionMatching SeparatedReplacements MixedReplacements
open GWArithmetic GWGrowth FlankReduction

set_option maxHeartbeats 3000000 in
/-- Unconditional slower-window necessity for arbitrary mixed multipliers. -/
theorem solution {n r s m k : ℕ}
    (hn : 5 ≤ n) (hrlarge : n ≤ 2*r) (hslarge : n ≤ 2*s)
    (hrn : r < n) (hsn : s < n) (hrs : r ≠ s)
    (hnp : n ≤ m*r) (hpq : m*r < k*s)
    (hno : ¬ HasStrictTime n r s (m*r) (k*s)) : GW n r m := by
  classical
  have hr : 3 ≤ r := by omega
  have hs : 3 ≤ s := by omega
  have hm : 2 ≤ m := by
    by_contra! hh
    have hh' : m ≤ 1 := by omega
    nlinarith only [Nat.mul_le_mul_right r hh',hnp,hrn]
  have hk2 : 2 ≤ k := by
    by_contra! hh
    have hh' : k ≤ 1 := by omega
    nlinarith only [Nat.mul_le_mul_right s hh',hpq,hnp,hsn]
  have hgw := matched_faster_window hn hrlarge hslarge hrn hsn hrs hnp hpq hno
  have hc := deficit_at_least_two hsn hk2 hgw
  have hwin := gw_window_bound hn hslarge hsn hk2 hgw
  have hnotcop : ¬ Nat.Coprime r s := by
    intro hcop
    rcases lt_or_gt_of_ne hrs with h | h
    · exact hno (CoprimeReplacements.coprime_large_deletions hn hrlarge h hsn hcop hnp hpq)
    · have hh := CoprimeReplacements.coprime_large_deletions hn hslarge h hrn hcop.symm hnp hpq
      exact hno (strict_swap_deletions.mpr hh)
  let g := Nat.gcd r s
  have hg : 2 ≤ g := by
    have hgpos := Nat.gcd_pos_of_pos_left s (show 0 < r by omega)
    have hgne : g ≠ 1 := hnotcop
    omega
  have hgr : g ∣ r := Nat.gcd_dvd_left r s
  have hgs : g ∣ s := Nat.gcd_dvd_right r s
  have hgq : g ∣ k*s := dvd_mul_of_dvd_right hgs k
  by_contra hslow
  obtain ⟨b₀,hb₀,hfail₀,hcop₀⟩ : ∃ b, n-r ≤ b ∧ b < m*(n-r) ∧ Nat.Coprime r b := by
    simpa only [GW,not_forall,Classical.not_imp,not_not,exists_prop] using hslow
  have hex : ∃ b, n-r ≤ b ∧ Nat.Coprime r b := ⟨b₀,hb₀,hcop₀⟩
  let B := Nat.find hex
  have hBlo : n-r ≤ B := (Nat.find_spec hex).1
  have hBcop : Nat.Coprime r B := (Nat.find_spec hex).2
  have hmin (b : ℕ) (hb : n-r ≤ b) (hcop : Nat.Coprime r b) : B ≤ b := Nat.find_min' hex ⟨hb,hcop⟩
  have hBfail : B < m*(n-r) := lt_of_le_of_lt (hmin b₀ hb₀ hcop₀) hfail₀
  have hBpos : 0 < B := by omega
  have hrprev : Nat.Coprime r (r-1) := (Nat.coprime_self_sub_right (show 1 ≤ r by omega)).mpr (by simp)
  have hBn : B < n := by
    by_cases hstrict : n < 2*r
    · have hh := hmin (r-1) (by omega) hrprev
      omega
    · have hh := hmin (r+1) (by omega) (by simp)
      omega
  obtain ⟨a,c,j,hunit,hband⟩ := NearData.band hn hrlarge hrn hm hBlo hBfail hBcop hno
  let Z : ℤ := (k*s:ℕ)*a-(r:ℤ)*j
  have hnearZ : |(n:ℤ)*m*Z-(k*s:ℕ)| ≤ (m:ℤ)*r := by
    exact NearData.scale (n := (n:ℤ)) (r := (r:ℤ)) (m := (m:ℤ))
      (q := ((k*s:ℕ):ℤ)) (a := a) (j := j) (by omega) (by omega) (by omega)
      (by simpa using hband)
  have hgZ : (g:ℤ) ∣ Z := dvd_sub
    (dvd_mul_of_dvd_left (by exact_mod_cast hgq) a)
    (dvd_mul_of_dvd_left (by exact_mod_cast hgr) j)
  have horder := NearData.order (n := (n:ℤ)) (r := (r:ℤ)) (s := (s:ℤ))
    (m := (m:ℤ)) (k := (k:ℤ)) (D := Z) (g := (g:ℤ))
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by exact_mod_cast hpq) (by exact_mod_cast hg) hgZ (by simpa using hnearZ)
  let D := Z.toNat
  have hDZ : (D:ℤ)=Z := Int.toNat_of_nonneg (by omega)
  have hD2 : 2 ≤ D := by exact_mod_cast (show (2:ℤ) ≤ D by omega)
  have hnear : m*D < k+m := by exact_mod_cast (show (m:ℤ)*D < k+m by simpa [hDZ] using horder.2)
  have hmk : m < k := by nlinarith only [hnear,Nat.mul_le_mul_left m hD2]
  have hk : 3 ≤ k := by omega
  have hmn : m+1 ≤ n := by
    have hh := Nat.mul_le_mul_left k (show 1 ≤ n-s by omega)
    have hkbound : k ≤ s-1 := by nlinarith only [hh,hwin]
    omega
  have hgrowth := quadratic_growth (show 0 < s by omega) hsn hk hgw
  have hnc : n=s+(n-s) := by omega
  have hna : n=r+(n-r) := by omega
  have hncZ : (n:ℤ)=(s:ℤ)+(n-s:ℕ) := by exact_mod_cast hnc
  have hnaZ : (n:ℤ)=(r:ℤ)+(n-r:ℕ) := by exact_mod_cast hna
  have hstrict : n < 2*r := by
    by_contra! hh
    have hnr : n=2*r := by omega
    have hBle := hmin (r+1) (by omega) (by simp)
    have hBne : B ≠ r := by
      intro heq
      have hh := Nat.coprime_self r |>.mp (heq ▸ hBcop)
      omega
    have hBeq : B=r+1 := by omega
    have hunit' : a*((r:ℤ)+1)-c*r=1 := by simpa [hBeq] using hunit
    have hdivA : (r:ℤ) ∣ a-1 := ⟨c-a,by nlinarith only [hunit']⟩
    have hqrel : ((k*s:ℕ):ℤ)+(k:ℤ)*(n-s:ℕ)=(r:ℤ)*(2*k) := by
      push_cast
      have hnrZ : (n:ℤ)=2*r := by exact_mod_cast hnr
      nlinarith only [congrArg (fun z : ℤ => (k:ℤ)*z) hncZ,
        congrArg (fun z : ℤ => (k:ℤ)*z) hnrZ]
    have hdivq : (r:ℤ) ∣ ((k*s:ℕ):ℤ)+(k:ℤ)*(n-s:ℕ) := ⟨2*k,hqrel⟩
    have hdiv : (r:ℤ) ∣ Z+(k:ℤ)*(n-s:ℕ) := by
      have hd := dvd_sub (dvd_add (dvd_mul_of_dvd_right hdivA ((k*s:ℕ):ℤ)) hdivq)
        (dvd_mul_right (r:ℤ) j)
      have heq : Z+(k:ℤ)*(n-s:ℕ) =
          ((k*s:ℕ):ℤ)*(a-1)+(((k*s:ℕ):ℤ)+(k:ℤ)*(n-s:ℕ))-(r:ℤ)*j := by
        dsimp only [Z]
        ring
      rw [heq]
      exact hd
    exact exclude_halfway (r := (r:ℤ)) (c := ((n-s:ℕ):ℤ)) (m := (m:ℤ))
      (k := (k:ℤ)) (D := Z) (by exact_mod_cast hc) (by exact_mod_cast hm)
      (by exact_mod_cast hk) horder.1 horder.2 hdiv (by
        have hhZ : (k:ℤ)*k*(n-s:ℕ) < s := by exact_mod_cast hgrowth
        have hnrZ : (n:ℤ)=2*r := by exact_mod_cast hnr
        omega)
  have hBr : B < r := by
    have hh := hmin (r-1) (by omega) hrprev
    omega
  have hkc : 0 < k*(n-s) := by positivity
  have hkcn : k*(n-s) < n := by omega
  have hsys (w : ℕ) (hlo : n-r ≤ w) (hfail : w < m*(n-r)) (hcop : Nat.Coprime r w) :
      ∃ h : ℤ, (D:ℤ)*w=(k:ℤ)*s-(r:ℤ)*h ∧ |(k:ℤ)*s-(n:ℤ)*h| ≤ w := by
    obtain ⟨E,h,hgE,hid,hE,hfar⟩ := FailedFlank.arithmetic_of_no_strict
      hn hrlarge hrn hm hmn (show 0 < k*s by positivity) hlo hfail hcop hgr hgq hno
    have hEZ := near_unique (n := (n:ℤ)) (r := (r:ℤ)) (m := (m:ℤ))
      (q := ((k*s:ℕ):ℤ)) (g := (g:ℤ)) (D := E) (E := Z)
      (by omega) (by omega) (by omega) (by exact_mod_cast hg) hgE hgZ hE hnearZ
    exact ⟨h,by simpa [hEZ,← hDZ] using hid,by simpa using hfar⟩
  obtain ⟨h,hDBZ,hfar⟩ := hsys B hBlo hBfail hBcop
  have hfar' : |(k:ℤ)*((n:ℤ)-(n-s:ℕ))-(n:ℤ)*h| ≤ B := by
    simpa [show (n:ℤ)-(n-s:ℕ)=s by omega] using hfar
  have hidx := far_index (n := (n:ℤ)) (k := (k:ℤ)) (c := ((n-s:ℕ):ℤ))
    (b := (B:ℤ)) (h := h) (by omega) (by exact_mod_cast hkc)
    (by exact_mod_cast hkcn) (by exact_mod_cast hBn) hfar'
  have hh : h=(k:ℤ) := by
    rcases hidx with hh | hh
    · subst h
      have hleft : (n:ℤ)-(k:ℤ)*(n-s:ℕ) ≤ B := by
        have hh := (abs_le.mp hfar).2
        nlinarith only [hh,congrArg (fun z : ℤ => (k:ℤ)*z) hncZ]
      exact False.elim (no_wrap (n := (n:ℤ)) (r := (r:ℤ)) (s := (s:ℤ))
        (a := ((n-r:ℕ):ℤ)) (c := ((n-s:ℕ):ℤ)) (m := (m:ℤ)) (k := (k:ℤ))
        (b := (B:ℤ)) (D := (D:ℤ)) hnaZ hncZ (by omega) (by omega)
        (by exact_mod_cast hm) (by exact_mod_cast hmk) (by omega)
        (by exact_mod_cast hBr) (by exact_mod_cast hBfail) hleft (by exact_mod_cast hnear)
        (by nlinarith only [hDBZ]) (by exact_mod_cast hgrowth))
    · exact hh
  subst h
  have hsr : r < s := by
    have hprod : (0:ℤ) < (D:ℤ)*B := mul_pos (by omega) (by omega)
    have hkZ : (0:ℤ) < k := by omega
    have hd : (k:ℤ)*r < (k:ℤ)*s := by nlinarith only [hprod,hDBZ]
    have hh : (r:ℤ) < s := (mul_lt_mul_iff_right₀ hkZ).mp (by simpa [mul_comm] using hd)
    exact_mod_cast hh
  have hDB : D*B=k*(s-r) := by
    have hh : (D:ℤ)*B=(k:ℤ)*((s:ℤ)-r) := by nlinarith only [hDBZ]
    rw [← Nat.cast_sub hsr.le] at hh
    exact_mod_cast hh
  have hBkc : k*(n-s) ≤ B := by
    have hh := (abs_le.mp hfar).1
    have hh' : (k:ℤ)*(n-s:ℕ) ≤ B := by
      nlinarith only [hh,congrArg (fun z : ℤ => (k:ℤ)*z) hncZ]
    exact_mod_cast hh'
  apply MixedArithmetic.contradiction hsr hsn hm hD2 hnear hgw hBr hDB hBkc hBlo hBcop hmin
  intro w hlo hhi hcop hwcut
  have hwfail : w < m*(n-r) := by nlinarith only [hhi,Nat.mul_le_mul_right (n-r) hm]
  obtain ⟨h,hid,hfarw⟩ := hsys w hlo hwfail hcop
  have hwZ : (w:ℤ) < (n:ℤ)-(k:ℤ)*(n-s:ℕ) := by
    have hh : w+k*(n-s) < n := by omega
    have hhZ : (w:ℤ)+(k:ℤ)*(n-s:ℕ) < n := by exact_mod_cast hh
    linarith only [hhZ]
  have hidxw := far_index (n := (n:ℤ)) (k := (k:ℤ)) (c := ((n-s:ℕ):ℤ))
    (b := (w:ℤ)) (h := h) (by omega) (by exact_mod_cast hkc)
    (by exact_mod_cast hkcn) (by omega)
    (by simpa [show (n:ℤ)-(n-s:ℕ)=s by omega] using hfarw)
  have hhk : h=(k:ℤ) := by
    rcases hidxw with hh | hh
    · subst h
      have hh := (abs_le.mp hfarw).2
      nlinarith only [hh,hwZ,congrArg (fun z : ℤ => (k:ℤ)*z) hncZ]
    · exact hh
  subst h
  have hwB : (w:ℤ)=B := by nlinarith only [hid,hDBZ,show (0:ℤ) < D by omega]
  exact_mod_cast hwB
