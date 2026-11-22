-- Prove2me | solution 1 for MasulloRH.height_one_exponential_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T16:40:46.636192+00:00
-- url     : https://prove2.me/submissions/74d47552-3c47-4107-8a53-790c6b7567f5

import Definitions.Def_MasulloRH_HeightOneExponentialTable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000


set_option autoImplicit false

open scoped BigOperators

namespace MasulloRH.HeightOneExponentialProof

/-- A finite rational certificate for an exponential on the unit interval. -/
theorem enclosure_of_taylor {x a b : ℝ} {n : ℕ}
    (hx : |x| ≤ 1) (hn : 0 < n)
    (hlo : a ≤ (∑ m ∈ Finset.range n, x ^ m / m.factorial) -
      |x| ^ n * ((n + 1 : ℕ) : ℝ) / (n.factorial * n))
    (hhi : (∑ m ∈ Finset.range n, x ^ m / m.factorial) +
      |x| ^ n * ((n + 1 : ℕ) : ℝ) / (n.factorial * n) ≤ b) :
    a ≤ Real.exp x ∧ Real.exp x ≤ b := by
  have h := Real.exp_bound hx hn
  have h' : |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / m.factorial| ≤
      |x| ^ n * ((n + 1 : ℕ) : ℝ) / (n.factorial * n) := by
    simpa only [Nat.succ_eq_add_one, mul_div_assoc] using h
  constructor <;> linarith [(abs_le.mp h').1, (abs_le.mp h').2]

/-- Scaling, powering and reciprocation preserve certified rational endpoints.
The powers in the two final hypotheses are rational arithmetic only. -/
theorem neg_enclosure_of_scaled {t x a b l u : ℝ} {n : ℕ}
    (ht : t = n * x) (ha : 0 < a)
    (hsmall : a ≤ Real.exp x ∧ Real.exp x ≤ b)
    (hl : l ≤ 1 / b ^ n) (hu : 1 / a ^ n ≤ u) :
    l ≤ Real.exp (-t) ∧ Real.exp (-t) ≤ u := by
  have hlow := pow_le_pow_left₀ ha.le hsmall.1 n
  have hupp := pow_le_pow_left₀ (Real.exp_pos x).le hsmall.2 n
  rw [Real.exp_neg, ht, Real.exp_nat_mul, ← one_div]
  exact ⟨hl.trans (one_div_le_one_div_of_le (pow_pos (Real.exp_pos x) n) hupp),
    (one_div_le_one_div_of_le (pow_pos ha n) hlow).trans hu⟩

theorem enclosure_of_scaled {t x a b l u : ℝ} {n : ℕ}
    (ht : t = n * x) (ha : 0 ≤ a)
    (hsmall : a ≤ Real.exp x ∧ Real.exp x ≤ b)
    (hl : l ≤ a ^ n) (hu : b ^ n ≤ u) :
    l ≤ Real.exp t ∧ Real.exp t ≤ u := by
  rw [ht, Real.exp_nat_mul]
  exact ⟨hl.trans (pow_le_pow_left₀ ha hsmall.1 n),
    (pow_le_pow_left₀ (Real.exp_pos x).le hsmall.2 n).trans hu⟩

/-- A cheap enclosure for every sufficiently negative Gaussian exponent. -/
theorem neg_enclosure_of_twenty_le {t : ℝ} (ht : 20 ≤ t) :
    0 ≤ Real.exp (-t) ∧ Real.exp (-t) ≤ 1 / 1048576 := by
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbase 20
  have hexp : Real.exp 1 ^ (20 : ℕ) = Real.exp 20 := by
    simpa only [Nat.cast_ofNat, mul_one] using (Real.exp_nat_mul (1 : ℝ) 20).symm
  rw [hexp] at hpow
  norm_num at hpow
  have ht' := hpow.trans (Real.exp_le_exp.mpr ht)
  refine ⟨(Real.exp_pos _).le, ?_⟩
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) ht'

theorem enclosure_of_argument_interval {x a b l u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hl : l ≤ Real.exp a) (hu : Real.exp b ≤ u) :
    l ≤ Real.exp x ∧ Real.exp x ≤ u :=
  ⟨hl.trans (Real.exp_le_exp.mpr hx.1), (Real.exp_le_exp.mpr hx.2).trans hu⟩


end MasulloRH.HeightOneExponentialProof


set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MasulloRH.HeightOneExponentialProof

theorem n1_exp_000 :
    (1570953301 / 5000000 : ℝ) ≤ Real.exp (23 / 4 : ℝ) ∧
    Real.exp (23 / 4 : ℝ) ≤ (3141906603 / 10000000 : ℝ) := by
  have hsmall : (59842164557381 / 50000000000000 : ℝ) ≤ Real.exp (23 / 128 : ℝ) ∧
      Real.exp (23 / 128 : ℝ) ≤ (119684329114763 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (23 / 128 : ℝ))
    (a := (59842164557381 / 50000000000000 : ℝ)) (b := (119684329114763 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_001 :
    (16699658537 / 1250000 : ℝ) ≤ Real.exp (19 / 2 : ℝ) ∧
    Real.exp (19 / 2 : ℝ) ≤ (133597268297 / 10000000 : ℝ) := by
  have hsmall : (134564708304941 / 100000000000000 : ℝ) ≤ Real.exp (19 / 64 : ℝ) ∧
      Real.exp (19 / 64 : ℝ) ≤ (67282354152471 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (19 / 64 : ℝ))
    (a := (134564708304941 / 100000000000000 : ℝ)) (b := (67282354152471 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_002 :
    (0 : ℝ) ≤ Real.exp (-(13115882591 / 5000000 : ℝ)) ∧
    Real.exp (-(13115882591 / 5000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_003 :
    (0 : ℝ) ≤ Real.exp (-(61691179 / 1000000 : ℝ)) ∧
    Real.exp (-(61691179 / 1000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_004 :
    (177254241 / 10000000 : ℝ) ≤ Real.exp (23 / 8 : ℝ) ∧
    Real.exp (23 / 8 : ℝ) ≤ (88627121 / 5000000 : ℝ) := by
  have hsmall : (10940033323293 / 10000000000000 : ℝ) ≤ Real.exp (23 / 256 : ℝ) ∧
      Real.exp (23 / 256 : ℝ) ≤ (109400333232931 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (23 / 256 : ℝ))
    (a := (10940033323293 / 10000000000000 : ℝ)) (b := (109400333232931 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_005 :
    (231168569 / 2000000 : ℝ) ≤ Real.exp (19 / 4 : ℝ) ∧
    Real.exp (19 / 4 : ℝ) ≤ (577921423 / 5000000 : ℝ) := by
  have hsmall : (3625063419501 / 3125000000000 : ℝ) ≤ Real.exp (19 / 128 : ℝ) ∧
      Real.exp (19 / 128 : ℝ) ≤ (116002029424033 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (19 / 128 : ℝ))
    (a := (3625063419501 / 3125000000000 : ℝ)) (b := (116002029424033 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_006 :
    (0 : ℝ) ≤ Real.exp (-(64 / 1 : ℝ)) ∧
    Real.exp (-(64 / 1 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_007 :
    (0 / 1 : ℝ) ≤ Real.exp (-(289 / 16 : ℝ)) ∧
    Real.exp (-(289 / 16 : ℝ)) ≤ (1 / 10000000 : ℝ) := by
  have hsmall : (8792429229 / 5000000000 : ℝ) ≤ Real.exp (289 / 512 : ℝ) ∧
      Real.exp (289 / 512 : ℝ) ≤ (17584858479 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (289 / 512 : ℝ))
    (a := (8792429229 / 5000000000 : ℝ)) (b := (17584858479 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_008 :
    (104579 / 1000000 : ℝ) ≤ Real.exp (-(289 / 128 : ℝ)) ∧
    Real.exp (-(289 / 128 : ℝ)) ≤ (1045791 / 10000000 : ℝ) := by
  have hsmall : (1073105349 / 1000000000 : ℝ) ≤ Real.exp (289 / 4096 : ℝ) ∧
      Real.exp (289 / 4096 : ℝ) ≤ (10731053491 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (289 / 4096 : ℝ))
    (a := (1073105349 / 1000000000 : ℝ)) (b := (10731053491 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_009 :
    (240913491 / 5000000 : ℝ) ≤ Real.exp (31 / 8 : ℝ) ∧
    Real.exp (31 / 8 : ℝ) ≤ (481826983 / 10000000 : ℝ) := by
  have hsmall : (112873072591281 / 100000000000000 : ℝ) ≤ Real.exp (31 / 256 : ℝ) ∧
      Real.exp (31 / 256 : ℝ) ≤ (56436536295641 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 256 : ℝ))
    (a := (112873072591281 / 100000000000000 : ℝ)) (b := (56436536295641 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_010 :
    (0 : ℝ) ≤ Real.exp (-(616911987 / 10000000 : ℝ)) ∧
    Real.exp (-(616911987 / 10000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_011 :
    (389 / 5000000 : ℝ) ≤ Real.exp (-(94606487 / 10000000 : ℝ)) ∧
    Real.exp (-(94606487 / 10000000 : ℝ)) ≤ (779 / 10000000 : ℝ) := by
  have hsmall : (33599833 / 25000000 : ℝ) ≤ Real.exp (94606487 / 320000000 : ℝ) ∧
      Real.exp (94606487 / 320000000 : ℝ) ≤ (13439933201 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (94606487 / 320000000 : ℝ))
    (a := (33599833 / 25000000 : ℝ)) (b := (13439933201 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_012 :
    (34706879 / 5000000 : ℝ) ≤ Real.exp (31 / 16 : ℝ) ∧
    Real.exp (31 / 16 : ℝ) ≤ (69413759 / 10000000 : ℝ) := by
  have hsmall : (106241739721863 / 100000000000000 : ℝ) ≤ Real.exp (31 / 512 : ℝ) ∧
      Real.exp (31 / 512 : ℝ) ≤ (13280217465233 / 12500000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 512 : ℝ))
    (a := (106241739721863 / 100000000000000 : ℝ)) (b := (13280217465233 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_013 :
    (17753 / 5000000 : ℝ) ≤ Real.exp (-(361 / 64 : ℝ)) ∧
    Real.exp (-(361 / 64 : ℝ)) ≤ (35507 / 10000000 : ℝ) := by
  have hsmall : (2981898753 / 2500000000 : ℝ) ≤ Real.exp (361 / 2048 : ℝ) ∧
      Real.exp (361 / 2048 : ℝ) ≤ (11927595013 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (361 / 2048 : ℝ))
    (a := (2981898753 / 2500000000 : ℝ)) (b := (11927595013 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_014 :
    (2831669 / 10000000 : ℝ) ≤ Real.exp (-(323 / 256 : ℝ)) ∧
    Real.exp (-(323 / 256 : ℝ)) ≤ (283167 / 1000000 : ℝ) := by
  have hsmall : (10402163401 / 10000000000 : ℝ) ≤ Real.exp (323 / 8192 : ℝ) ∧
      Real.exp (323 / 8192 : ℝ) ≤ (5201081701 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (323 / 8192 : ℝ))
    (a := (10402163401 / 10000000000 : ℝ)) (b := (5201081701 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_015 :
    (301519621 / 10000000 : ℝ) ≤ Real.exp (109 / 32 : ℝ) ∧
    Real.exp (109 / 32 : ℝ) ≤ (150759811 / 5000000 : ℝ) := by
  have hsmall : (2780792737353 / 2500000000000 : ℝ) ≤ Real.exp (109 / 1024 : ℝ) ∧
      Real.exp (109 / 1024 : ℝ) ≤ (111231709494121 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (109 / 1024 : ℝ))
    (a := (2780792737353 / 2500000000000 : ℝ)) (b := (111231709494121 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_016 :
    (389 / 5000000 : ℝ) ≤ Real.exp (-(47303259 / 5000000 : ℝ)) ∧
    Real.exp (-(47303259 / 5000000 : ℝ)) ≤ (779 / 10000000 : ℝ) := by
  have hsmall : (6719967251 / 5000000000 : ℝ) ≤ Real.exp (47303259 / 160000000 : ℝ) ∧
      Real.exp (47303259 / 160000000 : ℝ) ≤ (13439934503 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (47303259 / 160000000 : ℝ))
    (a := (6719967251 / 5000000000 : ℝ)) (b := (13439934503 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_017 :
    (26843 / 10000000 : ℝ) ≤ Real.exp (-(29601613 / 5000000 : ℝ)) ∧
    Real.exp (-(29601613 / 5000000 : ℝ)) ≤ (6711 / 2500000 : ℝ) := by
  have hsmall : (12032305701 / 10000000000 : ℝ) ≤ Real.exp (29601613 / 160000000 : ℝ) ∧
      Real.exp (29601613 / 160000000 : ℝ) ≤ (6016152851 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29601613 / 160000000 : ℝ))
    (a := (12032305701 / 10000000000 : ℝ)) (b := (6016152851 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_018 :
    (27455401 / 5000000 : ℝ) ≤ Real.exp (109 / 64 : ℝ) ∧
    Real.exp (109 / 64 : ℝ) ≤ (54910803 / 10000000 : ℝ) := by
  have hsmall : (52733222330453 / 50000000000000 : ℝ) ≤ Real.exp (109 / 2048 : ℝ) ∧
      Real.exp (109 / 2048 : ℝ) ≤ (105466444660907 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (109 / 2048 : ℝ))
    (a := (52733222330453 / 50000000000000 : ℝ)) (b := (105466444660907 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_019 :
    (264159 / 10000000 : ℝ) ≤ Real.exp (-(3721 / 1024 : ℝ)) ∧
    Real.exp (-(3721 / 1024 : ℝ)) ≤ (1651 / 62500 : ℝ) := by
  have hsmall : (2240509037 / 2000000000 : ℝ) ≤ Real.exp (3721 / 32768 : ℝ) ∧
      Real.exp (3721 / 32768 : ℝ) ≤ (5601272593 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3721 / 32768 : ℝ))
    (a := (2240509037 / 2000000000 : ℝ)) (b := (5601272593 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_020 :
    (1816193 / 5000000 : ℝ) ≤ Real.exp (-(1037 / 1024 : ℝ)) ∧
    Real.exp (-(1037 / 1024 : ℝ)) ≤ (3632387 / 10000000 : ℝ) := by
  have hsmall : (10321528107 / 10000000000 : ℝ) ≤ Real.exp (1037 / 32768 : ℝ) ∧
      Real.exp (1037 / 32768 : ℝ) ≤ (2580382027 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1037 / 32768 : ℝ))
    (a := (10321528107 / 10000000000 : ℝ)) (b := (2580382027 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_021 :
    (59630413 / 2500000 : ℝ) ≤ Real.exp (203 / 64 : ℝ) ∧
    Real.exp (203 / 64 : ℝ) ≤ (238521653 / 10000000 : ℝ) := by
  have hsmall : (110420000318251 / 100000000000000 : ℝ) ≤ Real.exp (203 / 2048 : ℝ) ∧
      Real.exp (203 / 2048 : ℝ) ≤ (27605000079563 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (203 / 2048 : ℝ))
    (a := (110420000318251 / 100000000000000 : ℝ)) (b := (27605000079563 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_022 :
    (26843 / 10000000 : ℝ) ≤ Real.exp (-(29601623 / 5000000 : ℝ)) ∧
    Real.exp (-(29601623 / 5000000 : ℝ)) ≤ (6711 / 2500000 : ℝ) := by
  have hsmall : (12032306453 / 10000000000 : ℝ) ≤ Real.exp (29601623 / 160000000 : ℝ) ∧
      Real.exp (29601623 / 160000000 : ℝ) ≤ (6016153227 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29601623 / 160000000 : ℝ))
    (a := (12032306453 / 10000000000 : ℝ)) (b := (6016153227 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_023 :
    (46239 / 5000000 : ℝ) ≤ Real.exp (-(46833607 / 10000000 : ℝ)) ∧
    Real.exp (-(46833607 / 10000000 : ℝ)) ≤ (92479 / 10000000 : ℝ) := by
  have hsmall : (11576070909 / 10000000000 : ℝ) ≤ Real.exp (46833607 / 320000000 : ℝ) ∧
      Real.exp (46833607 / 320000000 : ℝ) ≤ (1157607091 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (46833607 / 320000000 : ℝ))
    (a := (11576070909 / 10000000000 : ℝ)) (b := (1157607091 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_024 :
    (24419339 / 5000000 : ℝ) ≤ Real.exp (203 / 128 : ℝ) ∧
    Real.exp (203 / 128 : ℝ) ≤ (48838679 / 10000000 : ℝ) := by
  have hsmall : (52540460675143 / 50000000000000 : ℝ) ≤ Real.exp (203 / 4096 : ℝ) ∧
      Real.exp (203 / 4096 : ℝ) ≤ (105080921350287 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (203 / 4096 : ℝ))
    (a := (52540460675143 / 50000000000000 : ℝ)) (b := (105080921350287 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_025 :
    (611047 / 10000000 : ℝ) ≤ Real.exp (-(11449 / 4096 : ℝ)) ∧
    Real.exp (-(11449 / 4096 : ℝ)) ≤ (76381 / 1250000 : ℝ) := by
  have hsmall : (5456387007 / 5000000000 : ℝ) ≤ Real.exp (11449 / 131072 : ℝ) ∧
      Real.exp (11449 / 131072 : ℝ) ≤ (2182554803 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11449 / 131072 : ℝ))
    (a := (5456387007 / 5000000000 : ℝ)) (b := (2182554803 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_026 :
    (4114023 / 10000000 : ℝ) ≤ Real.exp (-(1819 / 2048 : ℝ)) ∧
    Real.exp (-(1819 / 2048 : ℝ)) ≤ (514253 / 1250000 : ℝ) := by
  have hsmall : (10281445163 / 10000000000 : ℝ) ≤ Real.exp (1819 / 65536 : ℝ) ∧
      Real.exp (1819 / 65536 : ℝ) ≤ (2570361291 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1819 / 65536 : ℝ))
    (a := (10281445163 / 10000000000 : ℝ)) (b := (2570361291 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_027 :
    (212145549 / 10000000 : ℝ) ≤ Real.exp (391 / 128 : ℝ) ∧
    Real.exp (391 / 128 : ℝ) ≤ (4242911 / 200000 : ℝ) := by
  have hsmall : (6876023107543 / 6250000000000 : ℝ) ≤ Real.exp (391 / 4096 : ℝ) ∧
      Real.exp (391 / 4096 : ℝ) ≤ (110016369720689 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (391 / 4096 : ℝ))
    (a := (6876023107543 / 6250000000000 : ℝ)) (b := (110016369720689 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_028 :
    (46239 / 5000000 : ℝ) ≤ Real.exp (-(46833623 / 10000000 : ℝ)) ∧
    Real.exp (-(46833623 / 10000000 : ℝ)) ≤ (92479 / 10000000 : ℝ) := by
  have hsmall : (180876117 / 156250000 : ℝ) ≤ Real.exp (46833623 / 320000000 : ℝ) ∧
      Real.exp (46833623 / 320000000 : ℝ) ≤ (11576071489 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (46833623 / 320000000 : ℝ))
    (a := (180876117 / 156250000 : ℝ)) (b := (11576071489 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_029 :
    (19403 / 1250000 : ℝ) ≤ Real.exp (-(2603417 / 625000 : ℝ)) ∧
    Real.exp (-(2603417 / 625000 : ℝ)) ≤ (6209 / 400000 : ℝ) := by
  have hsmall : (11390229687 / 10000000000 : ℝ) ≤ Real.exp (2603417 / 20000000 : ℝ) ∧
      Real.exp (2603417 / 20000000 : ℝ) ≤ (1423778711 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2603417 / 20000000 : ℝ))
    (a := (11390229687 / 10000000000 : ℝ)) (b := (1423778711 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_030 :
    (2302963 / 500000 : ℝ) ≤ Real.exp (391 / 256 : ℝ) ∧
    Real.exp (391 / 256 : ℝ) ≤ (46059261 / 10000000 : ℝ) := by
  have hsmall : (20977737696967 / 20000000000000 : ℝ) ≤ Real.exp (391 / 8192 : ℝ) ∧
      Real.exp (391 / 8192 : ℝ) ≤ (26222172121209 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (391 / 8192 : ℝ))
    (a := (20977737696967 / 20000000000000 : ℝ)) (b := (26222172121209 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_031 :
    (2787 / 31250 : ℝ) ≤ Real.exp (-(39601 / 16384 : ℝ)) ∧
    Real.exp (-(39601 / 16384 : ℝ)) ≤ (891841 / 10000000 : ℝ) := by
  have hsmall : (5392293613 / 5000000000 : ℝ) ≤ Real.exp (39601 / 524288 : ℝ) ∧
      Real.exp (39601 / 524288 : ℝ) ≤ (10784587227 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (39601 / 524288 : ℝ))
    (a := (5392293613 / 5000000000 : ℝ)) (b := (10784587227 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_032 :
    (2189143 / 5000000 : ℝ) ≤ Real.exp (-(3383 / 4096 : ℝ)) ∧
    Real.exp (-(3383 / 4096 : ℝ)) ≤ (4378287 / 10000000 : ℝ) := by
  have hsmall : (5130731051 / 5000000000 : ℝ) ≤ Real.exp (3383 / 131072 : ℝ) ∧
      Real.exp (3383 / 131072 : ℝ) ≤ (10261462103 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3383 / 131072 : ℝ))
    (a := (5130731051 / 5000000000 : ℝ)) (b := (10261462103 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_033 :
    (188686157 / 10000000 : ℝ) ≤ Real.exp (47 / 16 : ℝ) ∧
    Real.exp (47 / 16 : ℝ) ≤ (94343079 / 5000000 : ℝ) := by
  have hsmall : (109614214559267 / 100000000000000 : ℝ) ≤ Real.exp (47 / 512 : ℝ) ∧
      Real.exp (47 / 512 : ℝ) ≤ (27403553639817 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (47 / 512 : ℝ))
    (a := (109614214559267 / 100000000000000 : ℝ)) (b := (27403553639817 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_034 :
    (19403 / 1250000 : ℝ) ≤ Real.exp (-(20827343 / 5000000 : ℝ)) ∧
    Real.exp (-(20827343 / 5000000 : ℝ)) ≤ (6209 / 400000 : ℝ) := by
  have hsmall : (5695115093 / 5000000000 : ℝ) ≤ Real.exp (20827343 / 160000000 : ℝ) ∧
      Real.exp (20827343 / 160000000 : ℝ) ≤ (11390230187 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (20827343 / 160000000 : ℝ))
    (a := (5695115093 / 5000000000 : ℝ)) (b := (11390230187 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_035 :
    (6151 / 250000 : ℝ) ≤ Real.exp (-(2315527 / 625000 : ℝ)) ∧
    Real.exp (-(2315527 / 625000 : ℝ)) ≤ (246041 / 10000000 : ℝ) := by
  have hsmall : (11227447421 / 10000000000 : ℝ) ≤ Real.exp (2315527 / 20000000 : ℝ) ∧
      Real.exp (2315527 / 20000000 : ℝ) ≤ (5613723711 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2315527 / 20000000 : ℝ))
    (a := (11227447421 / 10000000000 : ℝ)) (b := (5613723711 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_036 :
    (43438019 / 10000000 : ℝ) ≤ Real.exp (47 / 32 : ℝ) ∧
    Real.exp (47 / 32 : ℝ) ≤ (2171901 / 500000 : ℝ) := by
  have hsmall : (52348403643107 / 50000000000000 : ℝ) ≤ Real.exp (47 / 1024 : ℝ) ∧
      Real.exp (47 / 1024 : ℝ) ≤ (20939361457243 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (47 / 1024 : ℝ))
    (a := (52348403643107 / 50000000000000 : ℝ)) (b := (20939361457243 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_037 :
    (1583 / 12500 : ℝ) ≤ Real.exp (-(529 / 256 : ℝ)) ∧
    Real.exp (-(529 / 256 : ℝ)) ≤ (1266401 / 10000000 : ℝ) := by
  have hsmall : (2133411573 / 2000000000 : ℝ) ≤ Real.exp (529 / 8192 : ℝ) ∧
      Real.exp (529 / 8192 : ℝ) ≤ (5333528933 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (529 / 8192 : ℝ))
    (a := (2133411573 / 2000000000 : ℝ)) (b := (5333528933 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_038 :
    (4659523 / 10000000 : ℝ) ≤ Real.exp (-(391 / 512 : ℝ)) ∧
    Real.exp (-(391 / 512 : ℝ)) ≤ (1164881 / 2500000 : ℝ) := by
  have hsmall : (10241517879 / 10000000000 : ℝ) ≤ Real.exp (391 / 16384 : ℝ) ∧
      Real.exp (391 / 16384 : ℝ) ≤ (256037947 / 250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (391 / 16384 : ℝ))
    (a := (10241517879 / 10000000000 : ℝ)) (b := (256037947 / 250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_039 :
    (83910471 / 5000000 : ℝ) ≤ Real.exp (361 / 128 : ℝ) ∧
    Real.exp (361 / 128 : ℝ) ≤ (167820943 / 10000000 : ℝ) := by
  have hsmall : (54606764720331 / 50000000000000 : ℝ) ≤ Real.exp (361 / 4096 : ℝ) ∧
      Real.exp (361 / 4096 : ℝ) ≤ (109213529440663 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (361 / 4096 : ℝ))
    (a := (54606764720331 / 50000000000000 : ℝ)) (b := (109213529440663 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_040 :
    (6151 / 250000 : ℝ) ≤ Real.exp (-(7409689 / 2000000 : ℝ)) ∧
    Real.exp (-(7409689 / 2000000 : ℝ)) ≤ (246041 / 10000000 : ℝ) := by
  have hsmall : (5613723939 / 5000000000 : ℝ) ≤ Real.exp (7409689 / 64000000 : ℝ) ∧
      Real.exp (7409689 / 64000000 : ℝ) ≤ (11227447879 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7409689 / 64000000 : ℝ))
    (a := (5613723939 / 5000000000 : ℝ)) (b := (11227447879 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_041 :
    (185311 / 5000000 : ℝ) ≤ Real.exp (-(16475779 / 5000000 : ℝ)) ∧
    Real.exp (-(16475779 / 5000000 : ℝ)) ≤ (370623 / 10000000 : ℝ) := by
  have hsmall : (554231083 / 500000000 : ℝ) ≤ Real.exp (16475779 / 160000000 : ℝ) ∧
      Real.exp (16475779 / 160000000 : ℝ) ≤ (11084621661 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (16475779 / 160000000 : ℝ))
    (a := (554231083 / 500000000 : ℝ)) (b := (11084621661 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_042 :
    (20482977 / 5000000 : ℝ) ≤ Real.exp (361 / 256 : ℝ) ∧
    Real.exp (361 / 256 : ℝ) ≤ (8193191 / 2000000 : ℝ) := by
  have hsmall : (26126319277773 / 25000000000000 : ℝ) ≤ Real.exp (361 / 8192 : ℝ) ∧
      Real.exp (361 / 8192 : ℝ) ≤ (104505277111093 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (361 / 8192 : ℝ))
    (a := (26126319277773 / 25000000000000 : ℝ)) (b := (104505277111093 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_043 :
    (109347 / 625000 : ℝ) ≤ Real.exp (-(28561 / 16384 : ℝ)) ∧
    Real.exp (-(28561 / 16384 : ℝ)) ≤ (1749553 / 10000000 : ℝ) := by
  have hsmall : (5279934523 / 5000000000 : ℝ) ≤ Real.exp (28561 / 524288 : ℝ) ∧
      Real.exp (28561 / 524288 : ℝ) ≤ (10559869047 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (28561 / 524288 : ℝ))
    (a := (5279934523 / 5000000000 : ℝ)) (b := (10559869047 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_044 :
    (2479413 / 5000000 : ℝ) ≤ Real.exp (-(2873 / 4096 : ℝ)) ∧
    Real.exp (-(2873 / 4096 : ℝ)) ≤ (4958827 / 10000000 : ℝ) := by
  have hsmall : (10221612421 / 10000000000 : ℝ) ≤ Real.exp (2873 / 131072 : ℝ) ∧
      Real.exp (2873 / 131072 : ℝ) ≤ (5110806211 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2873 / 131072 : ℝ))
    (a := (10221612421 / 10000000000 : ℝ)) (b := (5110806211 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_045 :
    (79135111 / 5000000 : ℝ) ≤ Real.exp (707 / 256 : ℝ) ∧
    Real.exp (707 / 256 : ℝ) ≤ (158270223 / 10000000 : ℝ) := by
  have hsmall : (109013736467393 / 100000000000000 : ℝ) ≤ Real.exp (707 / 8192 : ℝ) ∧
      Real.exp (707 / 8192 : ℝ) ≤ (54506868233697 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (707 / 8192 : ℝ))
    (a := (109013736467393 / 100000000000000 : ℝ)) (b := (54506868233697 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_046 :
    (185311 / 5000000 : ℝ) ≤ Real.exp (-(32951569 / 10000000 : ℝ)) ∧
    Real.exp (-(32951569 / 10000000 : ℝ)) ≤ (370623 / 10000000 : ℝ) := by
  have hsmall : (11084622041 / 10000000000 : ℝ) ≤ Real.exp (32951569 / 320000000 : ℝ) ∧
      Real.exp (32951569 / 320000000 : ℝ) ≤ (5542311021 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (32951569 / 320000000 : ℝ))
    (a := (11084622041 / 10000000000 : ℝ)) (b := (5542311021 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_047 :
    (111767 / 2500000 : ℝ) ≤ Real.exp (-(15538139 / 5000000 : ℝ)) ∧
    Real.exp (-(15538139 / 5000000 : ℝ)) ≤ (447069 / 10000000 : ℝ) := by
  have hsmall : (2754963243 / 2500000000 : ℝ) ≤ Real.exp (15538139 / 160000000 : ℝ) ∧
      Real.exp (15538139 / 160000000 : ℝ) ≤ (11019852973 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15538139 / 160000000 : ℝ))
    (a := (2754963243 / 2500000000 : ℝ)) (b := (11019852973 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_048 :
    (3978319 / 1000000 : ℝ) ≤ Real.exp (707 / 512 : ℝ) ∧
    Real.exp (707 / 512 : ℝ) ≤ (39783191 / 10000000 : ℝ) := by
  have hsmall : (104409643456623 / 100000000000000 : ℝ) ≤ Real.exp (707 / 16384 : ℝ) ∧
      Real.exp (707 / 16384 : ℝ) ≤ (6525602716039 / 6250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (707 / 16384 : ℝ))
    (a := (104409643456623 / 100000000000000 : ℝ)) (b := (6525602716039 / 6250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_049 :
    (407063 / 2000000 : ℝ) ≤ Real.exp (-(104329 / 65536 : ℝ)) ∧
    Real.exp (-(104329 / 65536 : ℝ)) ≤ (508829 / 2500000 : ℝ) := by
  have hsmall : (164219711 / 156250000 : ℝ) ≤ Real.exp (104329 / 2097152 : ℝ) ∧
      Real.exp (104329 / 2097152 : ℝ) ≤ (2102012301 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (104329 / 2097152 : ℝ))
    (a := (164219711 / 156250000 : ℝ)) (b := (2102012301 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_050 :
    (5115611 / 10000000 : ℝ) ≤ Real.exp (-(5491 / 8192 : ℝ)) ∧
    Real.exp (-(5491 / 8192 : ℝ)) ≤ (1278903 / 2500000 : ℝ) := by
  have hsmall : (2552918551 / 2500000000 : ℝ) ≤ Real.exp (5491 / 262144 : ℝ) ∧
      Real.exp (5491 / 262144 : ℝ) ≤ (2042334841 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5491 / 262144 : ℝ))
    (a := (2552918551 / 2500000000 : ℝ)) (b := (2042334841 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_051 :
    (37315759 / 2500000 : ℝ) ≤ Real.exp (173 / 64 : ℝ) ∧
    Real.exp (173 / 64 : ℝ) ≤ (149263037 / 10000000 : ℝ) := by
  have hsmall : (108814308991259 / 100000000000000 : ℝ) ≤ Real.exp (173 / 2048 : ℝ) ∧
      Real.exp (173 / 2048 : ℝ) ≤ (5440715449563 / 5000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (173 / 2048 : ℝ))
    (a := (108814308991259 / 100000000000000 : ℝ)) (b := (5440715449563 / 5000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_052 :
    (111767 / 2500000 : ℝ) ≤ Real.exp (-(3107629 / 1000000 : ℝ)) ∧
    Real.exp (-(3107629 / 1000000 : ℝ)) ≤ (447069 / 10000000 : ℝ) := by
  have hsmall : (2203970677 / 2000000000 : ℝ) ≤ Real.exp (3107629 / 32000000 : ℝ) ∧
      Real.exp (3107629 / 32000000 : ℝ) ≤ (5509926693 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3107629 / 32000000 : ℝ))
    (a := (2203970677 / 2000000000 : ℝ)) (b := (5509926693 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_053 :
    (266779 / 5000000 : ℝ) ≤ Real.exp (-(14653861 / 5000000 : ℝ)) ∧
    Real.exp (-(14653861 / 5000000 : ℝ)) ≤ (533559 / 10000000 : ℝ) := by
  have hsmall : (10959117127 / 10000000000 : ℝ) ≤ Real.exp (14653861 / 160000000 : ℝ) ∧
      Real.exp (14653861 / 160000000 : ℝ) ≤ (1369889641 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (14653861 / 160000000 : ℝ))
    (a := (10959117127 / 10000000000 : ℝ)) (b := (1369889641 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_054 :
    (19317287 / 5000000 : ℝ) ≤ Real.exp (173 / 128 : ℝ) ∧
    Real.exp (173 / 128 : ℝ) ≤ (1545383 / 400000 : ℝ) := by
  have hsmall : (104314097317313 / 100000000000000 : ℝ) ≤ Real.exp (173 / 4096 : ℝ) ∧
      Real.exp (173 / 4096 : ℝ) ≤ (52157048658657 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (173 / 4096 : ℝ))
    (a := (104314097317313 / 100000000000000 : ℝ)) (b := (52157048658657 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_055 :
    (2351551 / 10000000 : ℝ) ≤ Real.exp (-(5929 / 4096 : ℝ)) ∧
    Real.exp (-(5929 / 4096 : ℝ)) ≤ (36743 / 156250 : ℝ) := by
  have hsmall : (10462733707 / 10000000000 : ℝ) ≤ Real.exp (5929 / 131072 : ℝ) ∧
      Real.exp (5929 / 131072 : ℝ) ≤ (2615683427 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5929 / 131072 : ℝ))
    (a := (10462733707 / 10000000000 : ℝ)) (b := (2615683427 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_056 :
    (2638677 / 5000000 : ℝ) ≤ Real.exp (-(1309 / 2048 : ℝ)) ∧
    Real.exp (-(1309 / 2048 : ℝ)) ≤ (1055471 / 2000000 : ℝ) := by
  have hsmall : (204034913 / 200000000 : ℝ) ≤ Real.exp (1309 / 65536 : ℝ) ∧
      Real.exp (1309 / 65536 : ℝ) ≤ (10201745651 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1309 / 65536 : ℝ))
    (a := (204034913 / 200000000 : ℝ)) (b := (10201745651 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_057 :
    (2815369 / 200000 : ℝ) ≤ Real.exp (677 / 256 : ℝ) ∧
    Real.exp (677 / 256 : ℝ) ≤ (140768451 / 10000000 : ℝ) := by
  have hsmall : (27153811585907 / 25000000000000 : ℝ) ≤ Real.exp (677 / 8192 : ℝ) ∧
      Real.exp (677 / 8192 : ℝ) ≤ (108615246343629 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (677 / 8192 : ℝ))
    (a := (27153811585907 / 25000000000000 : ℝ)) (b := (108615246343629 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_058 :
    (533557 / 10000000 : ℝ) ≤ Real.exp (-(29307733 / 10000000 : ℝ)) ∧
    Real.exp (-(29307733 / 10000000 : ℝ)) ≤ (266779 / 5000000 : ℝ) := by
  have hsmall : (171236211 / 156250000 : ℝ) ≤ Real.exp (29307733 / 320000000 : ℝ) ∧
      Real.exp (29307733 / 320000000 : ℝ) ≤ (2191823501 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29307733 / 320000000 : ℝ))
    (a := (171236211 / 156250000 : ℝ)) (b := (2191823501 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_059 :
    (315201 / 5000000 : ℝ) ≤ Real.exp (-(13819907 / 5000000 : ℝ)) ∧
    Real.exp (-(13819907 / 5000000 : ℝ)) ≤ (630403 / 10000000 : ℝ) := by
  have hsmall : (5451072243 / 5000000000 : ℝ) ≤ Real.exp (13819907 / 160000000 : ℝ) ∧
      Real.exp (13819907 / 160000000 : ℝ) ≤ (10902144487 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13819907 / 160000000 : ℝ))
    (a := (5451072243 / 5000000000 : ℝ)) (b := (10902144487 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_060 :
    (37519121 / 10000000 : ℝ) ≤ Real.exp (677 / 512 : ℝ) ∧
    Real.exp (677 / 512 : ℝ) ≤ (18759561 / 5000000 : ℝ) := by
  have hsmall : (4168745544523 / 4000000000000 : ℝ) ≤ Real.exp (677 / 16384 : ℝ) ∧
      Real.exp (677 / 16384 : ℝ) ≤ (26054659653269 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (677 / 16384 : ℝ))
    (a := (4168745544523 / 4000000000000 : ℝ)) (b := (26054659653269 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_061 :
    (269833 / 1000000 : ℝ) ≤ Real.exp (-(85849 / 65536 : ℝ)) ∧
    Real.exp (-(85849 / 65536 : ℝ)) ≤ (2698331 / 10000000 : ℝ) := by
  have hsmall : (520892711 / 500000000 : ℝ) ≤ Real.exp (85849 / 2097152 : ℝ) ∧
      Real.exp (85849 / 2097152 : ℝ) ≤ (10417854221 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (85849 / 2097152 : ℝ))
    (a := (520892711 / 500000000 : ℝ)) (b := (10417854221 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_062 :
    (5444211 / 10000000 : ℝ) ≤ Real.exp (-(4981 / 8192 : ℝ)) ∧
    Real.exp (-(4981 / 8192 : ℝ)) ≤ (1361053 / 2500000 : ℝ) := by
  have hsmall : (40767307 / 40000000 : ℝ) ≤ Real.exp (4981 / 262144 : ℝ) ∧
      Real.exp (4981 / 262144 : ℝ) ≤ (10191826751 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4981 / 262144 : ℝ))
    (a := (40767307 / 40000000 : ℝ)) (b := (10191826751 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_063 :
    (33189323 / 2500000 : ℝ) ≤ Real.exp (331 / 128 : ℝ) ∧
    Real.exp (331 / 128 : ℝ) ≤ (132757293 / 10000000 : ℝ) := by
  have hsmall : (10841654785709 / 10000000000000 : ℝ) ≤ Real.exp (331 / 4096 : ℝ) ∧
      Real.exp (331 / 4096 : ℝ) ≤ (108416547857091 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (331 / 4096 : ℝ))
    (a := (10841654785709 / 10000000000000 : ℝ)) (b := (108416547857091 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_064 :
    (315201 / 5000000 : ℝ) ≤ Real.exp (-(1727489 / 625000 : ℝ)) ∧
    Real.exp (-(1727489 / 625000 : ℝ)) ≤ (630403 / 10000000 : ℝ) := by
  have hsmall : (5451072413 / 5000000000 : ℝ) ≤ Real.exp (1727489 / 20000000 : ℝ) ∧
      Real.exp (1727489 / 20000000 : ℝ) ≤ (10902144827 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1727489 / 20000000 : ℝ))
    (a := (5451072413 / 5000000000 : ℝ)) (b := (10902144827 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_065 :
    (184447 / 2500000 : ℝ) ≤ Real.exp (-(26066827 / 10000000 : ℝ)) ∧
    Real.exp (-(26066827 / 10000000 : ℝ)) ≤ (737789 / 10000000 : ℝ) := by
  have hsmall : (10848685573 / 10000000000 : ℝ) ≤ Real.exp (26066827 / 320000000 : ℝ) ∧
      Real.exp (26066827 / 320000000 : ℝ) ≤ (5424342787 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (26066827 / 320000000 : ℝ))
    (a := (10848685573 / 10000000000 : ℝ)) (b := (5424342787 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_066 :
    (18217937 / 5000000 : ℝ) ≤ Real.exp (331 / 256 : ℝ) ∧
    Real.exp (331 / 256 : ℝ) ≤ (291487 / 80000 : ℝ) := by
  have hsmall : (104123267263897 / 100000000000000 : ℝ) ≤ Real.exp (331 / 8192 : ℝ) ∧
      Real.exp (331 / 8192 : ℝ) ≤ (52061633631949 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (331 / 8192 : ℝ))
    (a := (104123267263897 / 100000000000000 : ℝ)) (b := (52061633631949 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_067 :
    (3075061 / 10000000 : ℝ) ≤ Real.exp (-(19321 / 16384 : ℝ)) ∧
    Real.exp (-(19321 / 16384 : ℝ)) ≤ (1537531 / 5000000 : ℝ) := by
  have hsmall : (10375393321 / 10000000000 : ℝ) ≤ Real.exp (19321 / 524288 : ℝ) ∧
      Real.exp (19321 / 524288 : ℝ) ≤ (5187696661 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (19321 / 524288 : ℝ))
    (a := (10375393321 / 10000000000 : ℝ)) (b := (5187696661 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_068 :
    (5616343 / 10000000 : ℝ) ≤ Real.exp (-(2363 / 4096 : ℝ)) ∧
    Real.exp (-(2363 / 4096 : ℝ)) ≤ (702043 / 1250000 : ℝ) := by
  have hsmall : (10181917493 / 10000000000 : ℝ) ≤ Real.exp (2363 / 131072 : ℝ) ∧
      Real.exp (2363 / 131072 : ℝ) ≤ (5090958747 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2363 / 131072 : ℝ))
    (a := (10181917493 / 10000000000 : ℝ)) (b := (5090958747 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_069 :
    (125202051 / 10000000 : ℝ) ≤ Real.exp (647 / 256 : ℝ) ∧
    Real.exp (647 / 256 : ℝ) ≤ (31300513 / 2500000 : ℝ) := by
  have hsmall : (6763638304091 / 6250000000000 : ℝ) ≤ Real.exp (647 / 8192 : ℝ) ∧
      Real.exp (647 / 8192 : ℝ) ≤ (108218212865457 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (647 / 8192 : ℝ))
    (a := (6763638304091 / 6250000000000 : ℝ)) (b := (108218212865457 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_070 :
    (184447 / 2500000 : ℝ) ≤ Real.exp (-(26066837 / 10000000 : ℝ)) ∧
    Real.exp (-(26066837 / 10000000 : ℝ)) ≤ (737789 / 10000000 : ℝ) := by
  have hsmall : (1356085739 / 1250000000 : ℝ) ≤ Real.exp (26066837 / 320000000 : ℝ) ∧
      Real.exp (26066837 / 320000000 : ℝ) ≤ (10848685913 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (26066837 / 320000000 : ℝ))
    (a := (1356085739 / 1250000000 : ℝ)) (b := (10848685913 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_071 :
    (213943 / 2500000 : ℝ) ≤ Real.exp (-(76823 / 31250 : ℝ)) ∧
    Real.exp (-(76823 / 31250 : ℝ)) ≤ (855773 / 10000000 : ℝ) := by
  have hsmall : (5399254629 / 5000000000 : ℝ) ≤ Real.exp (76823 / 1000000 : ℝ) ∧
      Real.exp (76823 / 1000000 : ℝ) ≤ (10798509259 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (76823 / 1000000 : ℝ))
    (a := (5399254629 / 5000000000 : ℝ)) (b := (10798509259 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_072 :
    (35383901 / 10000000 : ℝ) ≤ Real.exp (647 / 512 : ℝ) ∧
    Real.exp (647 / 512 : ℝ) ≤ (17691951 / 5000000 : ℝ) := by
  have hsmall : (104027983189839 / 100000000000000 : ℝ) ≤ Real.exp (647 / 16384 : ℝ) ∧
      Real.exp (647 / 16384 : ℝ) ≤ (1300349789873 / 1250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (647 / 16384 : ℝ))
    (a := (104027983189839 / 100000000000000 : ℝ)) (b := (1300349789873 / 1250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_073 :
    (3480409 / 10000000 : ℝ) ≤ Real.exp (-(69169 / 65536 : ℝ)) ∧
    Real.exp (-(69169 / 65536 : ℝ)) ≤ (348041 / 1000000 : ℝ) := by
  have hsmall : (5167661483 / 5000000000 : ℝ) ≤ Real.exp (69169 / 2097152 : ℝ) ∧
      Real.exp (69169 / 2097152 : ℝ) ≤ (10335322967 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (69169 / 2097152 : ℝ))
    (a := (5167661483 / 5000000000 : ℝ)) (b := (10335322967 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_074 :
    (5793917 / 10000000 : ℝ) ≤ Real.exp (-(4471 / 8192 : ℝ)) ∧
    Real.exp (-(4471 / 8192 : ℝ)) ≤ (2896959 / 5000000 : ℝ) := by
  have hsmall : (10172017871 / 10000000000 : ℝ) ≤ Real.exp (4471 / 262144 : ℝ) ∧
      Real.exp (4471 / 262144 : ℝ) ≤ (635751117 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4471 / 262144 : ℝ))
    (a := (10172017871 / 10000000000 : ℝ)) (b := (635751117 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_075 :
    (5903839 / 500000 : ℝ) ≤ Real.exp (79 / 32 : ℝ) ∧
    Real.exp (79 / 32 : ℝ) ≤ (118076781 / 10000000 : ℝ) := by
  have hsmall : (27005060175939 / 25000000000000 : ℝ) ≤ Real.exp (79 / 1024 : ℝ) ∧
      Real.exp (79 / 1024 : ℝ) ≤ (108020240703757 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (79 / 1024 : ℝ))
    (a := (27005060175939 / 25000000000000 : ℝ)) (b := (108020240703757 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_076 :
    (855771 / 10000000 : ℝ) ≤ Real.exp (-(24583369 / 10000000 : ℝ)) ∧
    Real.exp (-(24583369 / 10000000 : ℝ)) ≤ (213943 / 2500000 : ℝ) := by
  have hsmall : (5399254781 / 5000000000 : ℝ) ≤ Real.exp (24583369 / 320000000 : ℝ) ∧
      Real.exp (24583369 / 320000000 : ℝ) ≤ (10798509563 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (24583369 / 320000000 : ℝ))
    (a := (5399254781 / 5000000000 : ℝ)) (b := (10798509563 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_077 :
    (492139 / 5000000 : ℝ) ≤ Real.exp (-(5796079 / 2500000 : ℝ)) ∧
    Real.exp (-(5796079 / 2500000 : ℝ)) ≤ (984279 / 10000000 : ℝ) := by
  have hsmall : (5375700547 / 5000000000 : ℝ) ≤ Real.exp (5796079 / 80000000 : ℝ) ∧
      Real.exp (5796079 / 80000000 : ℝ) ≤ (2150280219 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5796079 / 80000000 : ℝ))
    (a := (5375700547 / 5000000000 : ℝ)) (b := (2150280219 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_078 :
    (17181151 / 5000000 : ℝ) ≤ Real.exp (79 / 64 : ℝ) ∧
    Real.exp (79 / 64 : ℝ) ≤ (34362303 / 10000000 : ℝ) := by
  have hsmall : (25983196577759 / 25000000000000 : ℝ) ≤ Real.exp (79 / 2048 : ℝ) ∧
      Real.exp (79 / 2048 : ℝ) ≤ (103932786311037 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (79 / 2048 : ℝ))
    (a := (25983196577759 / 25000000000000 : ℝ)) (b := (103932786311037 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_079 :
    (3912233 / 10000000 : ℝ) ≤ Real.exp (-(961 / 1024 : ℝ)) ∧
    Real.exp (-(961 / 1024 : ℝ)) ≤ (1956117 / 5000000 : ℝ) := by
  have hsmall : (2574404189 / 2500000000 : ℝ) ≤ Real.exp (961 / 32768 : ℝ) ∧
      Real.exp (961 / 32768 : ℝ) ≤ (10297616757 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (961 / 32768 : ℝ))
    (a := (2574404189 / 2500000000 : ℝ)) (b := (10297616757 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_080 :
    (2988553 / 5000000 : ℝ) ≤ Real.exp (-(527 / 1024 : ℝ)) ∧
    Real.exp (-(527 / 1024 : ℝ)) ≤ (5977107 / 10000000 : ℝ) := by
  have hsmall : (5081063937 / 5000000000 : ℝ) ≤ Real.exp (527 / 32768 : ℝ) ∧
      Real.exp (527 / 32768 : ℝ) ≤ (81297023 / 80000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (527 / 32768 : ℝ))
    (a := (5081063937 / 5000000000 : ℝ)) (b := (81297023 / 80000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_081 :
    (111357009 / 10000000 : ℝ) ≤ Real.exp (617 / 256 : ℝ) ∧
    Real.exp (617 / 256 : ℝ) ≤ (11135701 / 1000000 : ℝ) := by
  have hsmall : (26955657677059 / 25000000000000 : ℝ) ≤ Real.exp (617 / 8192 : ℝ) ∧
      Real.exp (617 / 8192 : ℝ) ≤ (107822630708237 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (617 / 8192 : ℝ))
    (a := (26955657677059 / 25000000000000 : ℝ)) (b := (107822630708237 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_082 :
    (984277 / 10000000 : ℝ) ≤ Real.exp (-(927373 / 400000 : ℝ)) ∧
    Real.exp (-(927373 / 400000 : ℝ)) ≤ (492139 / 5000000 : ℝ) := by
  have hsmall : (10751401397 / 10000000000 : ℝ) ≤ Real.exp (927373 / 12800000 : ℝ) ∧
      Real.exp (927373 / 12800000 : ℝ) ≤ (5375700699 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (927373 / 12800000 : ℝ))
    (a := (10751401397 / 10000000000 : ℝ)) (b := (5375700699 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_083 :
    (1123103 / 10000000 : ℝ) ≤ Real.exp (-(21864893 / 10000000 : ℝ)) ∧
    Real.exp (-(21864893 / 10000000 : ℝ)) ≤ (35097 / 312500 : ℝ) := by
  have hsmall : (10707162217 / 10000000000 : ℝ) ≤ Real.exp (21864893 / 320000000 : ℝ) ∧
      Real.exp (21864893 / 320000000 : ℝ) ≤ (5353581109 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (21864893 / 320000000 : ℝ))
    (a := (10707162217 / 10000000000 : ℝ)) (b := (5353581109 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_084 :
    (33370197 / 10000000 : ℝ) ≤ Real.exp (617 / 512 : ℝ) ∧
    Real.exp (617 / 512 : ℝ) ≤ (16685099 / 5000000 : ℝ) := by
  have hsmall : (51918838273847 / 50000000000000 : ℝ) ≤ Real.exp (617 / 16384 : ℝ) ∧
      Real.exp (617 / 16384 : ℝ) ≤ (20767535309539 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (617 / 16384 : ℝ))
    (a := (51918838273847 / 50000000000000 : ℝ)) (b := (20767535309539 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_085 :
    (4367543 / 10000000 : ℝ) ≤ Real.exp (-(54289 / 65536 : ℝ)) ∧
    Real.exp (-(54289 / 65536 : ℝ)) ≤ (545943 / 1250000 : ℝ) := by
  have hsmall : (10262249913 / 10000000000 : ℝ) ≤ Real.exp (54289 / 2097152 : ℝ) ∧
      Real.exp (54289 / 2097152 : ℝ) ≤ (5131124957 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (54289 / 2097152 : ℝ))
    (a := (10262249913 / 10000000000 : ℝ)) (b := (5131124957 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_086 :
    (6166087 / 10000000 : ℝ) ≤ Real.exp (-(3961 / 8192 : ℝ)) ∧
    Real.exp (-(3961 / 8192 : ℝ)) ≤ (770761 / 1250000 : ℝ) := by
  have hsmall : (10152247493 / 10000000000 : ℝ) ≤ Real.exp (3961 / 262144 : ℝ) ∧
      Real.exp (3961 / 262144 : ℝ) ≤ (5076123747 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3961 / 262144 : ℝ))
    (a := (10152247493 / 10000000000 : ℝ)) (b := (5076123747 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_087 :
    (52509831 / 5000000 : ℝ) ≤ Real.exp (301 / 128 : ℝ) ∧
    Real.exp (301 / 128 : ℝ) ≤ (105019663 / 10000000 : ℝ) := by
  have hsmall : (107625382216357 / 100000000000000 : ℝ) ≤ Real.exp (301 / 4096 : ℝ) ∧
      Real.exp (301 / 4096 : ℝ) ≤ (53812691108179 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (301 / 4096 : ℝ))
    (a := (107625382216357 / 100000000000000 : ℝ)) (b := (53812691108179 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_088 :
    (561551 / 5000000 : ℝ) ≤ Real.exp (-(21864901 / 10000000 : ℝ)) ∧
    Real.exp (-(21864901 / 10000000 : ℝ)) ≤ (1123103 / 10000000 : ℝ) := by
  have hsmall : (2676790621 / 2500000000 : ℝ) ≤ Real.exp (21864901 / 320000000 : ℝ) ∧
      Real.exp (21864901 / 320000000 : ℝ) ≤ (2141432497 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (21864901 / 320000000 : ℝ))
    (a := (2676790621 / 2500000000 : ℝ)) (b := (2141432497 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_089 :
    (635961 / 5000000 : ℝ) ≤ Real.exp (-(10310279 / 5000000 : ℝ)) ∧
    Real.exp (-(10310279 / 5000000 : ℝ)) ≤ (1271923 / 10000000 : ℝ) := by
  have hsmall : (133320097 / 125000000 : ℝ) ≤ Real.exp (10310279 / 160000000 : ℝ) ∧
      Real.exp (10310279 / 160000000 : ℝ) ≤ (10665607761 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10310279 / 160000000 : ℝ))
    (a := (133320097 / 125000000 : ℝ)) (b := (10665607761 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_090 :
    (32406737 / 10000000 : ℝ) ≤ Real.exp (301 / 256 : ℝ) ∧
    Real.exp (301 / 256 : ℝ) ≤ (16203369 / 5000000 : ℝ) := by
  have hsmall : (103742653820093 / 100000000000000 : ℝ) ≤ Real.exp (301 / 8192 : ℝ) ∧
      Real.exp (301 / 8192 : ℝ) ≤ (51871326910047 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (301 / 8192 : ℝ))
    (a := (103742653820093 / 100000000000000 : ℝ)) (b := (51871326910047 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_091 :
    (4842477 / 10000000 : ℝ) ≤ Real.exp (-(11881 / 16384 : ℝ)) ∧
    Real.exp (-(11881 / 16384 : ℝ)) ≤ (2421239 / 5000000 : ℝ) := by
  have hsmall : (639324953 / 625000000 : ℝ) ≤ Real.exp (11881 / 524288 : ℝ) ∧
      Real.exp (11881 / 524288 : ℝ) ≤ (10229199249 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11881 / 524288 : ℝ))
    (a := (639324953 / 625000000 : ℝ)) (b := (10229199249 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_092 :
    (6361043 / 10000000 : ℝ) ≤ Real.exp (-(1853 / 4096 : ℝ)) ∧
    Real.exp (-(1853 / 4096 : ℝ)) ≤ (1272209 / 2000000 : ℝ) := by
  have hsmall : (5071188359 / 5000000000 : ℝ) ≤ Real.exp (1853 / 131072 : ℝ) ∧
      Real.exp (1853 / 131072 : ℝ) ≤ (10142376719 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1853 / 131072 : ℝ))
    (a := (5071188359 / 5000000000 : ℝ)) (b := (10142376719 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_093 :
    (49521487 / 5000000 : ℝ) ≤ Real.exp (587 / 256 : ℝ) ∧
    Real.exp (587 / 256 : ℝ) ≤ (3961719 / 400000 : ℝ) := by
  have hsmall : (107428494566793 / 100000000000000 : ℝ) ≤ Real.exp (587 / 8192 : ℝ) ∧
      Real.exp (587 / 8192 : ℝ) ≤ (53714247283397 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (587 / 8192 : ℝ))
    (a := (107428494566793 / 100000000000000 : ℝ)) (b := (53714247283397 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_094 :
    (1271921 / 10000000 : ℝ) ≤ Real.exp (-(4124113 / 2000000 : ℝ)) ∧
    Real.exp (-(4124113 / 2000000 : ℝ)) ≤ (635961 / 5000000 : ℝ) := by
  have hsmall : (10665607993 / 10000000000 : ℝ) ≤ Real.exp (4124113 / 64000000 : ℝ) ∧
      Real.exp (4124113 / 64000000 : ℝ) ≤ (5332803997 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4124113 / 64000000 : ℝ))
    (a := (10665607993 / 10000000000 : ℝ)) (b := (5332803997 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_095 :
    (286059 / 2000000 : ℝ) ≤ Real.exp (-(9723519 / 5000000 : ℝ)) ∧
    Real.exp (-(9723519 / 5000000 : ℝ)) ≤ (178787 / 1250000 : ℝ) := by
  have hsmall : (5313282971 / 5000000000 : ℝ) ≤ Real.exp (9723519 / 160000000 : ℝ) ∧
      Real.exp (9723519 / 160000000 : ℝ) ≤ (10626565943 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9723519 / 160000000 : ℝ))
    (a := (5313282971 / 5000000000 : ℝ)) (b := (10626565943 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_096 :
    (31471093 / 10000000 : ℝ) ≤ Real.exp (587 / 512 : ℝ) ∧
    Real.exp (587 / 512 : ℝ) ≤ (15735547 / 5000000 : ℝ) := by
  have hsmall : (51823859024293 / 50000000000000 : ℝ) ≤ Real.exp (587 / 16384 : ℝ) ∧
      Real.exp (587 / 16384 : ℝ) ≤ (103647718048587 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (587 / 16384 : ℝ))
    (a := (51823859024293 / 50000000000000 : ℝ)) (b := (103647718048587 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_097 :
    (1066463 / 2000000 : ℝ) ≤ Real.exp (-(41209 / 65536 : ℝ)) ∧
    Real.exp (-(41209 / 65536 : ℝ)) ≤ (1333079 / 2500000 : ℝ) := by
  have hsmall : (10198443141 / 10000000000 : ℝ) ≤ Real.exp (41209 / 2097152 : ℝ) ∧
      Real.exp (41209 / 2097152 : ℝ) ≤ (5099221571 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (41209 / 2097152 : ℝ))
    (a := (10198443141 / 10000000000 : ℝ)) (b := (5099221571 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_098 :
    (1640541 / 2500000 : ℝ) ≤ Real.exp (-(3451 / 8192 : ℝ)) ∧
    Real.exp (-(3451 / 8192 : ℝ)) ≤ (1312433 / 2000000 : ℝ) := by
  have hsmall : (506625777 / 500000000 : ℝ) ≤ Real.exp (3451 / 262144 : ℝ) ∧
      Real.exp (3451 / 262144 : ℝ) ≤ (10132515541 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3451 / 262144 : ℝ))
    (a := (506625777 / 500000000 : ℝ)) (b := (10132515541 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_099 :
    (96183417 / 10000000 : ℝ) ≤ Real.exp (1159 / 512 : ℝ) ∧
    Real.exp (1159 / 512 : ℝ) ≤ (48091709 / 5000000 : ℝ) := by
  have hsmall : (13416273231443 / 12500000000000 : ℝ) ≤ Real.exp (1159 / 16384 : ℝ) ∧
      Real.exp (1159 / 16384 : ℝ) ≤ (21466037170309 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1159 / 16384 : ℝ))
    (a := (13416273231443 / 12500000000000 : ℝ)) (b := (21466037170309 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_100 :
    (715147 / 5000000 : ℝ) ≤ Real.exp (-(3889409 / 2000000 : ℝ)) ∧
    Real.exp (-(3889409 / 2000000 : ℝ)) ≤ (286059 / 2000000 : ℝ) := by
  have hsmall : (5313283087 / 5000000000 : ℝ) ≤ Real.exp (3889409 / 64000000 : ℝ) ∧
      Real.exp (3889409 / 64000000 : ℝ) ≤ (425062647 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3889409 / 64000000 : ℝ))
    (a := (5313283087 / 5000000000 : ℝ)) (b := (425062647 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_101 :
    (15129 / 100000 : ℝ) ≤ Real.exp (-(3777113 / 2000000 : ℝ)) ∧
    Real.exp (-(3777113 / 2000000 : ℝ)) ≤ (1512901 / 10000000 : ℝ) := by
  have hsmall : (2651984221 / 2500000000 : ℝ) ≤ Real.exp (3777113 / 64000000 : ℝ) ∧
      Real.exp (3777113 / 64000000 : ℝ) ≤ (2121587377 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3777113 / 64000000 : ℝ))
    (a := (2651984221 / 2500000000 : ℝ)) (b := (2121587377 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_102 :
    (31013451 / 10000000 : ℝ) ≤ Real.exp (1159 / 1024 : ℝ) ∧
    Real.exp (1159 / 1024 : ℝ) ≤ (7753363 / 2500000 : ℝ) := by
  have hsmall : (51800141373249 / 50000000000000 : ℝ) ≤ Real.exp (1159 / 32768 : ℝ) ∧
      Real.exp (1159 / 32768 : ℝ) ≤ (103600282746499 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1159 / 32768 : ℝ))
    (a := (51800141373249 / 50000000000000 : ℝ)) (b := (103600282746499 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_103 :
    (1395281 / 2500000 : ℝ) ≤ Real.exp (-(152881 / 262144 : ℝ)) ∧
    Real.exp (-(152881 / 262144 : ℝ)) ≤ (44649 / 80000 : ℝ) := by
  have hsmall : (2545979803 / 2500000000 : ℝ) ≤ Real.exp (152881 / 8388608 : ℝ) ∧
      Real.exp (152881 / 8388608 : ℝ) ≤ (10183919213 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (152881 / 8388608 : ℝ))
    (a := (2545979803 / 2500000000 : ℝ)) (b := (10183919213 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_104 :
    (833137 / 1250000 : ℝ) ≤ Real.exp (-(6647 / 16384 : ℝ)) ∧
    Real.exp (-(6647 / 16384 : ℝ)) ≤ (6665097 / 10000000 : ℝ) := by
  have hsmall : (10127588547 / 10000000000 : ℝ) ≤ Real.exp (6647 / 524288 : ℝ) ∧
      Real.exp (6647 / 524288 : ℝ) ≤ (2531897137 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6647 / 524288 : ℝ))
    (a := (10127588547 / 10000000000 : ℝ)) (b := (2531897137 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_105 :
    (93406421 / 10000000 : ℝ) ≤ Real.exp (143 / 64 : ℝ) ∧
    Real.exp (143 / 64 : ℝ) ≤ (46703211 / 5000000 : ℝ) := by
  have hsmall : (4289278683977 / 4000000000000 : ℝ) ≤ Real.exp (143 / 2048 : ℝ) ∧
      Real.exp (143 / 2048 : ℝ) ≤ (53615983549713 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (143 / 2048 : ℝ))
    (a := (4289278683977 / 4000000000000 : ℝ)) (b := (53615983549713 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_106 :
    (1512899 / 10000000 : ℝ) ≤ Real.exp (-(18885573 / 10000000 : ℝ)) ∧
    Real.exp (-(18885573 / 10000000 : ℝ)) ≤ (15129 / 100000 : ℝ) := by
  have hsmall : (10607937149 / 10000000000 : ℝ) ≤ Real.exp (18885573 / 320000000 : ℝ) ∧
      Real.exp (18885573 / 320000000 : ℝ) ≤ (212158743 / 200000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (18885573 / 320000000 : ℝ))
    (a := (10607937149 / 10000000000 : ℝ)) (b := (212158743 / 200000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_107 :
    (1597683 / 10000000 : ℝ) ≤ Real.exp (-(1146269 / 625000 : ℝ)) ∧
    Real.exp (-(1146269 / 625000 : ℝ)) ≤ (399421 / 2500000 : ℝ) := by
  have hsmall : (529493849 / 500000000 : ℝ) ≤ Real.exp (1146269 / 20000000 : ℝ) ∧
      Real.exp (1146269 / 20000000 : ℝ) ≤ (10589876981 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1146269 / 20000000 : ℝ))
    (a := (529493849 / 500000000 : ℝ)) (b := (10589876981 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_108 :
    (955077 / 312500 : ℝ) ≤ Real.exp (143 / 128 : ℝ) ∧
    Real.exp (143 / 128 : ℝ) ≤ (6112493 / 2000000 : ℝ) := by
  have hsmall : (103552869153599 / 100000000000000 : ℝ) ≤ Real.exp (143 / 4096 : ℝ) ∧
      Real.exp (143 / 4096 : ℝ) ≤ (64720543221 / 62500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (143 / 4096 : ℝ))
    (a := (103552869153599 / 100000000000000 : ℝ)) (b := (64720543221 / 62500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_109 :
    (1457881 / 2500000 : ℝ) ≤ Real.exp (-(2209 / 4096 : ℝ)) ∧
    Real.exp (-(2209 / 4096 : ℝ)) ≤ (233261 / 400000 : ℝ) := by
  have hsmall : (10169961511 / 10000000000 : ℝ) ≤ Real.exp (2209 / 131072 : ℝ) ∧
      Real.exp (2209 / 131072 : ℝ) ≤ (1271245189 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2209 / 131072 : ℝ))
    (a := (10169961511 / 10000000000 : ℝ)) (b := (1271245189 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_110 :
    (6769643 / 10000000 : ℝ) ≤ Real.exp (-(799 / 2048 : ℝ)) ∧
    Real.exp (-(799 / 2048 : ℝ)) ≤ (1692411 / 2500000 : ℝ) := by
  have hsmall : (202453279 / 200000000 : ℝ) ≤ Real.exp (799 / 65536 : ℝ) ∧
      Real.exp (799 / 65536 : ℝ) ≤ (10122663951 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (799 / 65536 : ℝ))
    (a := (202453279 / 200000000 : ℝ)) (b := (10122663951 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_111 :
    (45354801 / 5000000 : ℝ) ≤ Real.exp (1129 / 512 : ℝ) ∧
    Real.exp (1129 / 512 : ℝ) ≤ (90709603 / 10000000 : ℝ) := by
  have hsmall : (26783459557027 / 25000000000000 : ℝ) ≤ Real.exp (1129 / 16384 : ℝ) ∧
      Real.exp (1129 / 16384 : ℝ) ≤ (107133838228109 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1129 / 16384 : ℝ))
    (a := (26783459557027 / 25000000000000 : ℝ)) (b := (107133838228109 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_112 :
    (798841 / 5000000 : ℝ) ≤ Real.exp (-(18340311 / 10000000 : ℝ)) ∧
    Real.exp (-(18340311 / 10000000 : ℝ)) ≤ (1597683 / 10000000 : ℝ) := by
  have hsmall : (2647469303 / 2500000000 : ℝ) ≤ Real.exp (18340311 / 320000000 : ℝ) ∧
      Real.exp (18340311 / 320000000 : ℝ) ≤ (10589877213 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (18340311 / 320000000 : ℝ))
    (a := (2647469303 / 2500000000 : ℝ)) (b := (10589877213 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_113 :
    (1684563 / 10000000 : ℝ) ≤ Real.exp (-(556587 / 312500 : ℝ)) ∧
    Real.exp (-(556587 / 312500 : ℝ)) ≤ (421141 / 2500000 : ℝ) := by
  have hsmall : (10324578 / 9765625 : ℝ) ≤ Real.exp (556587 / 10000000 : ℝ) ∧
      Real.exp (556587 / 10000000 : ℝ) ≤ (10572367873 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (556587 / 10000000 : ℝ))
    (a := (10324578 / 9765625 : ℝ)) (b := (10572367873 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_114 :
    (15059017 / 5000000 : ℝ) ≤ Real.exp (1129 / 1024 : ℝ) ∧
    Real.exp (1129 / 1024 : ℝ) ≤ (6023607 / 2000000 : ℝ) := by
  have hsmall : (103505477259953 / 100000000000000 : ℝ) ≤ Real.exp (1129 / 32768 : ℝ) ∧
      Real.exp (1129 / 32768 : ℝ) ≤ (51752738629977 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1129 / 32768 : ℝ))
    (a := (103505477259953 / 100000000000000 : ℝ)) (b := (51752738629977 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_115 :
    (6082707 / 10000000 : ℝ) ≤ Real.exp (-(130321 / 262144 : ℝ)) ∧
    Real.exp (-(130321 / 262144 : ℝ)) ≤ (1520677 / 2500000 : ℝ) := by
  have hsmall : (5078283883 / 5000000000 : ℝ) ≤ Real.exp (130321 / 8388608 : ℝ) ∧
      Real.exp (130321 / 8388608 : ℝ) ≤ (10156567767 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (130321 / 8388608 : ℝ))
    (a := (5078283883 / 5000000000 : ℝ)) (b := (10156567767 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_116 :
    (6875829 / 10000000 : ℝ) ≤ Real.exp (-(6137 / 16384 : ℝ)) ∧
    Real.exp (-(6137 / 16384 : ℝ)) ≤ (687583 / 1000000 : ℝ) := by
  have hsmall : (2529435437 / 2500000000 : ℝ) ≤ Real.exp (6137 / 524288 : ℝ) ∧
      Real.exp (6137 / 524288 : ℝ) ≤ (10117741749 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6137 / 524288 : ℝ))
    (a := (2529435437 / 2500000000 : ℝ)) (b := (10117741749 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_117 :
    (17618129 / 2000000 : ℝ) ≤ Real.exp (557 / 256 : ℝ) ∧
    Real.exp (557 / 256 : ℝ) ≤ (44045323 / 5000000 : ℝ) := by
  have hsmall : (107035799155343 / 100000000000000 : ℝ) ≤ Real.exp (557 / 8192 : ℝ) ∧
      Real.exp (557 / 8192 : ℝ) ≤ (6689737447209 / 6250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (557 / 8192 : ℝ))
    (a := (107035799155343 / 100000000000000 : ℝ)) (b := (6689737447209 / 6250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_118 :
    (842281 / 5000000 : ℝ) ≤ Real.exp (-(17810791 / 10000000 : ℝ)) ∧
    Real.exp (-(17810791 / 10000000 : ℝ)) ≤ (1684563 / 10000000 : ℝ) := by
  have hsmall : (10572368103 / 10000000000 : ℝ) ≤ Real.exp (17810791 / 320000000 : ℝ) ∧
      Real.exp (17810791 / 320000000 : ℝ) ≤ (1321546013 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17810791 / 320000000 : ℝ))
    (a := (10572368103 / 10000000000 : ℝ)) (b := (1321546013 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_119 :
    (354691 / 2000000 : ℝ) ≤ Real.exp (-(8648277 / 5000000 : ℝ)) ∧
    Real.exp (-(8648277 / 5000000 : ℝ)) ≤ (110841 / 625000 : ℝ) := by
  have hsmall : (10555392051 / 10000000000 : ℝ) ≤ Real.exp (8648277 / 160000000 : ℝ) ∧
      Real.exp (8648277 / 160000000 : ℝ) ≤ (2638848013 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8648277 / 160000000 : ℝ))
    (a := (10555392051 / 10000000000 : ℝ)) (b := (2638848013 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_120 :
    (7420017 / 2500000 : ℝ) ≤ Real.exp (557 / 512 : ℝ) ∧
    Real.exp (557 / 512 : ℝ) ≤ (29680069 / 10000000 : ℝ) := by
  have hsmall : (10345810705563 / 10000000000000 : ℝ) ≤ Real.exp (557 / 16384 : ℝ) ∧
      Real.exp (557 / 16384 : ℝ) ≤ (103458107055631 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (557 / 16384 : ℝ))
    (a := (10345810705563 / 10000000000000 : ℝ)) (b := (103458107055631 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_121 :
    (1583457 / 2500000 : ℝ) ≤ Real.exp (-(29929 / 65536 : ℝ)) ∧
    Real.exp (-(29929 / 65536 : ℝ)) ≤ (6333829 / 10000000 : ℝ) := by
  have hsmall : (5071867899 / 5000000000 : ℝ) ≤ Real.exp (29929 / 2097152 : ℝ) ∧
      Real.exp (29929 / 2097152 : ℝ) ≤ (10143735799 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29929 / 2097152 : ℝ))
    (a := (5071867899 / 5000000000 : ℝ)) (b := (10143735799 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_122 :
    (3491841 / 5000000 : ℝ) ≤ Real.exp (-(2941 / 8192 : ℝ)) ∧
    Real.exp (-(2941 / 8192 : ℝ)) ≤ (6983683 / 10000000 : ℝ) := by
  have hsmall : (10112821939 / 10000000000 : ℝ) ≤ Real.exp (2941 / 262144 : ℝ) ∧
      Real.exp (2941 / 262144 : ℝ) ≤ (505641097 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2941 / 262144 : ℝ))
    (a := (10112821939 / 10000000000 : ℝ)) (b := (505641097 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_123 :
    (42773651 / 5000000 : ℝ) ≤ Real.exp (1099 / 512 : ℝ) ∧
    Real.exp (1099 / 512 : ℝ) ≤ (85547303 / 10000000 : ℝ) := by
  have hsmall : (21387569959791 / 20000000000000 : ℝ) ≤ Real.exp (1099 / 16384 : ℝ) ∧
      Real.exp (1099 / 16384 : ℝ) ≤ (26734462449739 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1099 / 16384 : ℝ))
    (a := (21387569959791 / 20000000000000 : ℝ)) (b := (26734462449739 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_124 :
    (886727 / 5000000 : ℝ) ≤ Real.exp (-(216207 / 125000 : ℝ)) ∧
    Real.exp (-(216207 / 125000 : ℝ)) ≤ (354691 / 2000000 : ℝ) := by
  have hsmall : (1319424031 / 1250000000 : ℝ) ≤ Real.exp (216207 / 4000000 : ℝ) ∧
      Real.exp (216207 / 4000000 : ℝ) ≤ (10555392249 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (216207 / 4000000 : ℝ))
    (a := (1319424031 / 1250000000 : ℝ)) (b := (10555392249 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_125 :
    (1864267 / 10000000 : ℝ) ≤ Real.exp (-(16797169 / 10000000 : ℝ)) ∧
    Real.exp (-(16797169 / 10000000 : ℝ)) ≤ (466067 / 2500000 : ℝ) := by
  have hsmall : (10538932383 / 10000000000 : ℝ) ≤ Real.exp (16797169 / 320000000 : ℝ) ∧
      Real.exp (16797169 / 320000000 : ℝ) ≤ (329341637 / 312500000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (16797169 / 320000000 : ℝ))
    (a := (10538932383 / 10000000000 : ℝ)) (b := (329341637 / 312500000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_126 :
    (2924847 / 1000000 : ℝ) ≤ Real.exp (1099 / 1024 : ℝ) ∧
    Real.exp (1099 / 1024 : ℝ) ≤ (29248471 / 10000000 : ℝ) := by
  have hsmall : (103410758530703 / 100000000000000 : ℝ) ≤ Real.exp (1099 / 32768 : ℝ) ∧
      Real.exp (1099 / 32768 : ℝ) ≤ (6463172408169 / 6250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1099 / 32768 : ℝ))
    (a := (103410758530703 / 100000000000000 : ℝ)) (b := (6463172408169 / 6250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_127 :
    (6584003 / 10000000 : ℝ) ≤ Real.exp (-(109561 / 262144 : ℝ)) ∧
    Real.exp (-(109561 / 262144 : ℝ)) ≤ (1646001 / 2500000 : ℝ) := by
  have hsmall : (10131463523 / 10000000000 : ℝ) ≤ Real.exp (109561 / 8388608 : ℝ) ∧
      Real.exp (109561 / 8388608 : ℝ) ≤ (2532865881 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (109561 / 8388608 : ℝ))
    (a := (10131463523 / 10000000000 : ℝ)) (b := (2532865881 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_128 :
    (3546613 / 5000000 : ℝ) ≤ Real.exp (-(5627 / 16384 : ℝ)) ∧
    Real.exp (-(5627 / 16384 : ℝ)) ≤ (7093227 / 10000000 : ℝ) := by
  have hsmall : (5053952261 / 5000000000 : ℝ) ≤ Real.exp (5627 / 524288 : ℝ) ∧
      Real.exp (5627 / 524288 : ℝ) ≤ (10107904523 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5627 / 524288 : ℝ))
    (a := (5053952261 / 5000000000 : ℝ)) (b := (10107904523 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_129 :
    (8307739 / 1000000 : ℝ) ≤ Real.exp (271 / 128 : ℝ) ∧
    Real.exp (271 / 128 : ℝ) ≤ (83077391 / 10000000 : ℝ) := by
  have hsmall : (106839990076843 / 100000000000000 : ℝ) ≤ Real.exp (271 / 4096 : ℝ) ∧
      Real.exp (271 / 4096 : ℝ) ≤ (26709997519211 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (271 / 4096 : ℝ))
    (a := (106839990076843 / 100000000000000 : ℝ)) (b := (26709997519211 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_130 :
    (932133 / 5000000 : ℝ) ≤ Real.exp (-(2099647 / 1250000 : ℝ)) ∧
    Real.exp (-(2099647 / 1250000 : ℝ)) ≤ (1864267 / 10000000 : ℝ) := by
  have hsmall : (5269466307 / 5000000000 : ℝ) ≤ Real.exp (2099647 / 40000000 : ℝ) ∧
      Real.exp (2099647 / 40000000 : ℝ) ≤ (2107786523 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2099647 / 40000000 : ℝ))
    (a := (5269466307 / 5000000000 : ℝ)) (b := (2107786523 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_131 :
    (978453 / 5000000 : ℝ) ≤ Real.exp (-(16312203 / 10000000 : ℝ)) ∧
    Real.exp (-(16312203 / 10000000 : ℝ)) ≤ (1956907 / 10000000 : ℝ) := by
  have hsmall : (1052297253 / 1000000000 : ℝ) ≤ Real.exp (16312203 / 320000000 : ℝ) ∧
      Real.exp (16312203 / 320000000 : ℝ) ≤ (10522972531 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (16312203 / 320000000 : ℝ))
    (a := (1052297253 / 1000000000 : ℝ)) (b := (10522972531 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_132 :
    (7205787 / 2500000 : ℝ) ≤ Real.exp (271 / 256 : ℝ) ∧
    Real.exp (271 / 256 : ℝ) ≤ (28823149 / 10000000 : ℝ) := by
  have hsmall : (103363431675251 / 100000000000000 : ℝ) ≤ Real.exp (271 / 8192 : ℝ) ∧
      Real.exp (271 / 8192 : ℝ) ≤ (25840857918813 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (271 / 8192 : ℝ))
    (a := (103363431675251 / 100000000000000 : ℝ)) (b := (25840857918813 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_133 :
    (3416161 / 5000000 : ℝ) ≤ Real.exp (-(6241 / 16384 : ℝ)) ∧
    Real.exp (-(6241 / 16384 : ℝ)) ≤ (6832323 / 10000000 : ℝ) := by
  have hsmall : (2023949789 / 2000000000 : ℝ) ≤ Real.exp (6241 / 524288 : ℝ) ∧
      Real.exp (6241 / 524288 : ℝ) ≤ (5059874473 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6241 / 524288 : ℝ))
    (a := (2023949789 / 2000000000 : ℝ)) (b := (5059874473 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_134 :
    (900561 / 1250000 : ℝ) ≤ Real.exp (-(1343 / 4096 : ℝ)) ∧
    Real.exp (-(1343 / 4096 : ℝ)) ≤ (7204489 / 10000000 : ℝ) := by
  have hsmall : (1262873687 / 1250000000 : ℝ) ≤ Real.exp (1343 / 131072 : ℝ) ∧
      Real.exp (1343 / 131072 : ℝ) ≤ (10102989497 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1343 / 131072 : ℝ))
    (a := (1262873687 / 1250000000 : ℝ)) (b := (10102989497 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_135 :
    (8067879 / 1000000 : ℝ) ≤ Real.exp (1069 / 512 : ℝ) ∧
    Real.exp (1069 / 512 : ℝ) ≤ (80678791 / 10000000 : ℝ) := by
  have hsmall : (106742219906983 / 100000000000000 : ℝ) ≤ Real.exp (1069 / 16384 : ℝ) ∧
      Real.exp (1069 / 16384 : ℝ) ≤ (13342777488373 / 12500000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1069 / 16384 : ℝ))
    (a := (106742219906983 / 100000000000000 : ℝ)) (b := (13342777488373 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_136 :
    (244613 / 1250000 : ℝ) ≤ Real.exp (-(1631221 / 1000000 : ℝ)) ∧
    Real.exp (-(1631221 / 1000000 : ℝ)) ≤ (391381 / 2000000 : ℝ) := by
  have hsmall : (10522972761 / 10000000000 : ℝ) ≤ Real.exp (1631221 / 32000000 : ℝ) ∧
      Real.exp (1631221 / 32000000 : ℝ) ≤ (5261486381 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1631221 / 32000000 : ℝ))
    (a := (10522972761 / 10000000000 : ℝ)) (b := (5261486381 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_137 :
    (1025637 / 5000000 : ℝ) ≤ Real.exp (-(396031 / 250000 : ℝ)) ∧
    Real.exp (-(396031 / 250000 : ℝ)) ≤ (82051 / 400000 : ℝ) := by
  have hsmall : (5253748319 / 5000000000 : ℝ) ≤ Real.exp (396031 / 8000000 : ℝ) ∧
      Real.exp (396031 / 8000000 : ℝ) ≤ (10507496639 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (396031 / 8000000 : ℝ))
    (a := (5253748319 / 5000000000 : ℝ)) (b := (10507496639 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_138 :
    (7101003 / 2500000 : ℝ) ≤ Real.exp (1069 / 1024 : ℝ) ∧
    Real.exp (1069 / 1024 : ℝ) ≤ (28404013 / 10000000 : ℝ) := by
  have hsmall : (25829031619839 / 25000000000000 : ℝ) ≤ Real.exp (1069 / 32768 : ℝ) ∧
      Real.exp (1069 / 32768 : ℝ) ≤ (103316126479357 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1069 / 32768 : ℝ))
    (a := (25829031619839 / 25000000000000 : ℝ)) (b := (103316126479357 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_139 :
    (3538923 / 5000000 : ℝ) ≤ Real.exp (-(90601 / 262144 : ℝ)) ∧
    Real.exp (-(90601 / 262144 : ℝ)) ≤ (7077847 / 10000000 : ℝ) := by
  have hsmall : (2021718033 / 2000000000 : ℝ) ≤ Real.exp (90601 / 8388608 : ℝ) ∧
      Real.exp (90601 / 8388608 : ℝ) ≤ (5054295083 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (90601 / 8388608 : ℝ))
    (a := (2021718033 / 2000000000 : ℝ)) (b := (5054295083 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_140 :
    (914687 / 1250000 : ℝ) ≤ Real.exp (-(5117 / 16384 : ℝ)) ∧
    Real.exp (-(5117 / 16384 : ℝ)) ≤ (7317497 / 10000000 : ℝ) := by
  have hsmall : (10098076861 / 10000000000 : ℝ) ≤ Real.exp (5117 / 524288 : ℝ) ∧
      Real.exp (5117 / 524288 : ℝ) ≤ (5049038431 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5117 / 524288 : ℝ))
    (a := (10098076861 / 10000000000 : ℝ)) (b := (5049038431 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_141 :
    (78349441 / 10000000 : ℝ) ≤ Real.exp (527 / 256 : ℝ) ∧
    Real.exp (527 / 256 : ℝ) ≤ (39174721 / 5000000 : ℝ) := by
  have hsmall : (416580231279 / 390625000000 : ℝ) ≤ Real.exp (527 / 8192 : ℝ) ∧
      Real.exp (527 / 8192 : ℝ) ≤ (4265781568297 / 4000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (527 / 8192 : ℝ))
    (a := (416580231279 / 390625000000 : ℝ)) (b := (4265781568297 / 4000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_142 :
    (256409 / 1250000 : ℝ) ≤ Real.exp (-(7920623 / 5000000 : ℝ)) ∧
    Real.exp (-(7920623 / 5000000 : ℝ)) ≤ (2051273 / 10000000 : ℝ) := by
  have hsmall : (2101499367 / 2000000000 : ℝ) ≤ Real.exp (7920623 / 160000000 : ℝ) ∧
      Real.exp (7920623 / 160000000 : ℝ) ≤ (2626874209 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7920623 / 160000000 : ℝ))
    (a := (2101499367 / 2000000000 : ℝ)) (b := (2626874209 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_143 :
    (2147271 / 10000000 : ℝ) ≤ Real.exp (-(15383873 / 10000000 : ℝ)) ∧
    Real.exp (-(15383873 / 10000000 : ℝ)) ≤ (268409 / 1250000 : ℝ) := by
  have hsmall : (655780581 / 625000000 : ℝ) ≤ Real.exp (15383873 / 320000000 : ℝ) ∧
      Real.exp (15383873 / 320000000 : ℝ) ≤ (10492489297 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15383873 / 320000000 : ℝ))
    (a := (655780581 / 625000000 : ℝ)) (b := (10492489297 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_144 :
    (2799097 / 1000000 : ℝ) ≤ Real.exp (527 / 512 : ℝ) ∧
    Real.exp (527 / 512 : ℝ) ≤ (27990971 / 10000000 : ℝ) := by
  have hsmall : (20653768586621 / 20000000000000 : ℝ) ≤ Real.exp (527 / 16384 : ℝ) ∧
      Real.exp (527 / 16384 : ℝ) ≤ (51634421466553 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (527 / 16384 : ℝ))
    (a := (20653768586621 / 20000000000000 : ℝ)) (b := (51634421466553 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_145 :
    (7319617 / 10000000 : ℝ) ≤ Real.exp (-(20449 / 65536 : ℝ)) ∧
    Real.exp (-(20449 / 65536 : ℝ)) ≤ (3659809 / 5000000 : ℝ) := by
  have hsmall : (5048992687 / 5000000000 : ℝ) ≤ Real.exp (20449 / 2097152 : ℝ) ∧
      Real.exp (20449 / 2097152 : ℝ) ≤ (80783883 / 80000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (20449 / 2097152 : ℝ))
    (a := (5048992687 / 5000000000 : ℝ)) (b := (80783883 / 80000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_146 :
    (1858069 / 2500000 : ℝ) ≤ Real.exp (-(2431 / 8192 : ℝ)) ∧
    Real.exp (-(2431 / 8192 : ℝ)) ≤ (7432277 / 10000000 : ℝ) := by
  have hsmall : (5046583307 / 5000000000 : ℝ) ≤ Real.exp (2431 / 262144 : ℝ) ∧
      Real.exp (2431 / 262144 : ℝ) ≤ (2018633323 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2431 / 262144 : ℝ))
    (a := (5046583307 / 5000000000 : ℝ)) (b := (2018633323 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_147 :
    (15217469 / 2000000 : ℝ) ≤ Real.exp (1039 / 512 : ℝ) ∧
    Real.exp (1039 / 512 : ℝ) ≤ (38043673 / 5000000 : ℝ) := by
  have hsmall : (26636736974073 / 25000000000000 : ℝ) ≤ Real.exp (1039 / 16384 : ℝ) ∧
      Real.exp (1039 / 16384 : ℝ) ≤ (106546947896293 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1039 / 16384 : ℝ))
    (a := (26636736974073 / 25000000000000 : ℝ)) (b := (106546947896293 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_148 :
    (2147269 / 10000000 : ℝ) ≤ Real.exp (-(15383879 / 10000000 : ℝ)) ∧
    Real.exp (-(15383879 / 10000000 : ℝ)) ≤ (214727 / 1000000 : ℝ) := by
  have hsmall : (10492489493 / 10000000000 : ℝ) ≤ Real.exp (15383879 / 320000000 : ℝ) ∧
      Real.exp (15383879 / 320000000 : ℝ) ≤ (5246244747 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15383879 / 320000000 : ℝ))
    (a := (10492489493 / 10000000000 : ℝ)) (b := (5246244747 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_149 :
    (1122397 / 5000000 : ℝ) ≤ Real.exp (-(233433 / 156250 : ℝ)) ∧
    Real.exp (-(233433 / 156250 : ℝ)) ≤ (448959 / 2000000 : ℝ) := by
  have hsmall : (10477935791 / 10000000000 : ℝ) ≤ Real.exp (233433 / 5000000 : ℝ) ∧
      Real.exp (233433 / 5000000 : ℝ) ≤ (654870987 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (233433 / 5000000 : ℝ))
    (a := (10477935791 / 10000000000 : ℝ)) (b := (654870987 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_150 :
    (13791967 / 5000000 : ℝ) ≤ Real.exp (1039 / 1024 : ℝ) ∧
    Real.exp (1039 / 1024 : ℝ) ≤ (5516787 / 2000000 : ℝ) := by
  have hsmall : (103221581026591 / 100000000000000 : ℝ) ≤ Real.exp (1039 / 32768 : ℝ) ∧
      Real.exp (1039 / 32768 : ℝ) ≤ (3225674407081 / 3125000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1039 / 32768 : ℝ))
    (a := (103221581026591 / 100000000000000 : ℝ)) (b := (3225674407081 / 3125000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_151 :
    (944583 / 1250000 : ℝ) ≤ Real.exp (-(73441 / 262144 : ℝ)) ∧
    Real.exp (-(73441 / 262144 : ℝ)) ≤ (1511333 / 2000000 : ℝ) := by
  have hsmall : (2521983213 / 2500000000 : ℝ) ≤ Real.exp (73441 / 8388608 : ℝ) ∧
      Real.exp (73441 / 8388608 : ℝ) ≤ (10087932853 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (73441 / 8388608 : ℝ))
    (a := (2521983213 / 2500000000 : ℝ)) (b := (10087932853 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_152 :
    (943607 / 1250000 : ℝ) ≤ Real.exp (-(4607 / 16384 : ℝ)) ∧
    Real.exp (-(4607 / 16384 : ℝ)) ≤ (7548857 / 10000000 : ℝ) := by
  have hsmall : (2017651751 / 2000000000 : ℝ) ≤ Real.exp (4607 / 524288 : ℝ) ∧
      Real.exp (4607 / 524288 : ℝ) ≤ (2522064689 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4607 / 524288 : ℝ))
    (a := (2017651751 / 2000000000 : ℝ)) (b := (2522064689 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_153 :
    (115454 / 15625 : ℝ) ≤ Real.exp (2 / 1 : ℝ) ∧
    Real.exp (2 / 1 : ℝ) ≤ (73890561 / 10000000 : ℝ) := by
  have hsmall : (21289889178357 / 20000000000000 : ℝ) ≤ Real.exp (1 / 16 : ℝ) ∧
      Real.exp (1 / 16 : ℝ) ≤ (53224722945893 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 16 : ℝ))
    (a := (21289889178357 / 20000000000000 : ℝ)) (b := (53224722945893 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_154 :
    (280599 / 1250000 : ℝ) ≤ Real.exp (-(7469859 / 5000000 : ℝ)) ∧
    Real.exp (-(7469859 / 5000000 : ℝ)) ≤ (2244793 / 10000000 : ℝ) := by
  have hsmall : (10477935987 / 10000000000 : ℝ) ≤ Real.exp (7469859 / 160000000 : ℝ) ∧
      Real.exp (7469859 / 160000000 : ℝ) ≤ (2619483997 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7469859 / 160000000 : ℝ))
    (a := (10477935987 / 10000000000 : ℝ)) (b := (2619483997 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_155 :
    (2343739 / 10000000 : ℝ) ≤ Real.exp (-(7254187 / 5000000 : ℝ)) ∧
    Real.exp (-(7254187 / 5000000 : ℝ)) ≤ (117187 / 500000 : ℝ) := by
  have hsmall : (1307977721 / 1250000000 : ℝ) ≤ Real.exp (7254187 / 160000000 : ℝ) ∧
      Real.exp (7254187 / 160000000 : ℝ) ≤ (10463821769 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7254187 / 160000000 : ℝ))
    (a := (1307977721 / 1250000000 : ℝ)) (b := (10463821769 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_156 :
    (13591409 / 5000000 : ℝ) ≤ Real.exp (1 / 1 : ℝ) ∧
    Real.exp (1 / 1 : ℝ) ≤ (27182819 / 10000000 : ℝ) := by
  have hsmall : (10317434074991 / 10000000000000 : ℝ) ≤ Real.exp (1 / 32 : ℝ) ∧
      Real.exp (1 / 32 : ℝ) ≤ (103174340749911 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 32 : ℝ))
    (a := (10317434074991 / 10000000000000 : ℝ)) (b := (103174340749911 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_157 :
    (7788007 / 10000000 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) ∧
    Real.exp (-(1 / 4 : ℝ)) ≤ (973501 / 1250000 : ℝ) := by
  have hsmall : (2519607743 / 2500000000 : ℝ) ≤ Real.exp (1 / 128 : ℝ) ∧
      Real.exp (1 / 128 : ℝ) ≤ (10078430973 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 128 : ℝ))
    (a := (2519607743 / 2500000000 : ℝ)) (b := (10078430973 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_158 :
    (1533453 / 2000000 : ℝ) ≤ Real.exp (-(17 / 64 : ℝ)) ∧
    Real.exp (-(17 / 64 : ℝ)) ≤ (3833633 / 5000000 : ℝ) := by
  have hsmall : (5041676641 / 5000000000 : ℝ) ≤ Real.exp (17 / 2048 : ℝ) ∧
      Real.exp (17 / 2048 : ℝ) ≤ (10083353283 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 2048 : ℝ))
    (a := (5041676641 / 5000000000 : ℝ)) (b := (10083353283 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_159 :
    (169169 / 1250000 : ℝ) ≤ Real.exp (-(2 / 1 : ℝ)) ∧
    Real.exp (-(2 / 1 : ℝ)) ≤ (1353353 / 10000000 : ℝ) := by
  have hsmall : (10644944589 / 10000000000 : ℝ) ≤ Real.exp (1 / 16 : ℝ) ∧
      Real.exp (1 / 16 : ℝ) ≤ (1064494459 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 16 : ℝ))
    (a := (10644944589 / 10000000000 : ℝ)) (b := (1064494459 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_160 :
    (174539 / 1250000 : ℝ) ≤ Real.exp (-(63 / 32 : ℝ)) ∧
    Real.exp (-(63 / 32 : ℝ)) ≤ (1396313 / 10000000 : ℝ) := by
  have hsmall : (10634554209 / 10000000000 : ℝ) ≤ Real.exp (63 / 1024 : ℝ) ∧
      Real.exp (63 / 1024 : ℝ) ≤ (1063455421 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (63 / 1024 : ℝ))
    (a := (10634554209 / 10000000000 : ℝ)) (b := (1063455421 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_161 :
    (6448969 / 10000000 : ℝ) ≤ Real.exp (-(548331 / 1250000 : ℝ)) ∧
    Real.exp (-(548331 / 1250000 : ℝ)) ≤ (644897 / 1000000 : ℝ) := by
  have hsmall : (5069013321 / 5000000000 : ℝ) ≤ Real.exp (548331 / 40000000 : ℝ) ∧
      Real.exp (548331 / 40000000 : ℝ) ≤ (10138026643 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (548331 / 40000000 : ℝ))
    (a := (5069013321 / 5000000000 : ℝ)) (b := (10138026643 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_162 :
    (32683 / 50000 : ℝ) ≤ Real.exp (-(4251679 / 10000000 : ℝ)) ∧
    Real.exp (-(4251679 / 10000000 : ℝ)) ≤ (6536601 / 10000000 : ℝ) := by
  have hsmall : (2026750309 / 2000000000 : ℝ) ≤ Real.exp (4251679 / 320000000 : ℝ) ∧
      Real.exp (4251679 / 320000000 : ℝ) ≤ (5066875773 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4251679 / 320000000 : ℝ))
    (a := (2026750309 / 2000000000 : ℝ)) (b := (5066875773 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_163 :
    (4013691 / 5000000 : ℝ) ≤ Real.exp (-(225 / 1024 : ℝ)) ∧
    Real.exp (-(225 / 1024 : ℝ)) ≤ (8027383 / 10000000 : ℝ) := by
  have hsmall : (314653151 / 312500000 : ℝ) ≤ Real.exp (225 / 32768 : ℝ) ∧
      Real.exp (225 / 32768 : ℝ) ≤ (10068900833 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (225 / 32768 : ℝ))
    (a := (314653151 / 312500000 : ℝ)) (b := (10068900833 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_164 :
    (7795617 / 10000000 : ℝ) ≤ Real.exp (-(255 / 1024 : ℝ)) ∧
    Real.exp (-(255 / 1024 : ℝ)) ≤ (3897809 / 5000000 : ℝ) := by
  have hsmall : (10078123407 / 10000000000 : ℝ) ≤ Real.exp (255 / 32768 : ℝ) ∧
      Real.exp (255 / 32768 : ℝ) ≤ (629882713 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (255 / 32768 : ℝ))
    (a := (10078123407 / 10000000000 : ℝ)) (b := (629882713 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_165 :
    (360159 / 2500000 : ℝ) ≤ Real.exp (-(31 / 16 : ℝ)) ∧
    Real.exp (-(31 / 16 : ℝ)) ≤ (1440637 / 10000000 : ℝ) := by
  have hsmall : (2656043493 / 2500000000 : ℝ) ≤ Real.exp (31 / 512 : ℝ) ∧
      Real.exp (31 / 512 : ℝ) ≤ (10624173973 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (31 / 512 : ℝ))
    (a := (2656043493 / 2500000000 : ℝ)) (b := (10624173973 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_166 :
    (635979 / 1000000 : ℝ) ≤ Real.exp (-(565737 / 1250000 : ℝ)) ∧
    Real.exp (-(565737 / 1250000 : ℝ)) ≤ (6359791 / 10000000 : ℝ) := by
  have hsmall : (2535609791 / 2500000000 : ℝ) ≤ Real.exp (565737 / 40000000 : ℝ) ∧
      Real.exp (565737 / 40000000 : ℝ) ≤ (2028487833 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (565737 / 40000000 : ℝ))
    (a := (2535609791 / 2500000000 : ℝ)) (b := (2028487833 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_167 :
    (1612243 / 2500000 : ℝ) ≤ Real.exp (-(2193321 / 5000000 : ℝ)) ∧
    Real.exp (-(2193321 / 5000000 : ℝ)) ≤ (6448973 / 10000000 : ℝ) := by
  have hsmall : (2534506613 / 2500000000 : ℝ) ≤ Real.exp (2193321 / 160000000 : ℝ) ∧
      Real.exp (2193321 / 160000000 : ℝ) ≤ (10138026453 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2193321 / 160000000 : ℝ))
    (a := (2534506613 / 2500000000 : ℝ)) (b := (10138026453 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_168 :
    (825797 / 1000000 : ℝ) ≤ Real.exp (-(49 / 256 : ℝ)) ∧
    Real.exp (-(49 / 256 : ℝ)) ≤ (8257971 / 10000000 : ℝ) := by
  have hsmall : (5029996849 / 5000000000 : ℝ) ≤ Real.exp (49 / 8192 : ℝ) ∧
      Real.exp (49 / 8192 : ℝ) ≤ (10059993699 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 8192 : ℝ))
    (a := (5029996849 / 5000000000 : ℝ)) (b := (10059993699 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_169 :
    (1981529 / 2500000 : ℝ) ≤ Real.exp (-(119 / 512 : ℝ)) ∧
    Real.exp (-(119 / 512 : ℝ)) ≤ (7926117 / 10000000 : ℝ) := by
  have hsmall : (2518224061 / 2500000000 : ℝ) ≤ Real.exp (119 / 16384 : ℝ) ∧
      Real.exp (119 / 16384 : ℝ) ≤ (2014579249 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (119 / 16384 : ℝ))
    (a := (2518224061 / 2500000000 : ℝ)) (b := (2014579249 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_170 :
    (1486367 / 10000000 : ℝ) ≤ Real.exp (-(61 / 32 : ℝ)) ∧
    Real.exp (-(61 / 32 : ℝ)) ≤ (46449 / 312500 : ℝ) := by
  have hsmall : (5306901933 / 5000000000 : ℝ) ≤ Real.exp (61 / 1024 : ℝ) ∧
      Real.exp (61 / 1024 : ℝ) ≤ (10613803867 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (61 / 1024 : ℝ))
    (a := (5306901933 / 5000000000 : ℝ)) (b := (10613803867 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_171 :
    (3134537 / 5000000 : ℝ) ≤ Real.exp (-(1167391 / 2500000 : ℝ)) ∧
    Real.exp (-(1167391 / 2500000 : ℝ)) ≤ (250763 / 400000 : ℝ) := by
  have hsmall : (10146993761 / 10000000000 : ℝ) ≤ Real.exp (1167391 / 80000000 : ℝ) ∧
      Real.exp (1167391 / 80000000 : ℝ) ≤ (5073496881 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1167391 / 80000000 : ℝ))
    (a := (10146993761 / 10000000000 : ℝ)) (b := (5073496881 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_172 :
    (3179897 / 5000000 : ℝ) ≤ Real.exp (-(452589 / 1000000 : ℝ)) ∧
    Real.exp (-(452589 / 1000000 : ℝ)) ≤ (1271959 / 2000000 : ℝ) := by
  have hsmall : (5071219487 / 5000000000 : ℝ) ≤ Real.exp (452589 / 32000000 : ℝ) ∧
      Real.exp (452589 / 32000000 : ℝ) ≤ (405697559 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (452589 / 32000000 : ℝ))
    (a := (5071219487 / 5000000000 : ℝ)) (b := (405697559 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_173 :
    (1695721 / 2000000 : ℝ) ≤ Real.exp (-(169 / 1024 : ℝ)) ∧
    Real.exp (-(169 / 1024 : ℝ)) ≤ (4239303 / 5000000 : ℝ) := by
  have hsmall : (10051707933 / 10000000000 : ℝ) ≤ Real.exp (169 / 32768 : ℝ) ∧
      Real.exp (169 / 32768 : ℝ) ≤ (5025853967 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (169 / 32768 : ℝ))
    (a := (10051707933 / 10000000000 : ℝ)) (b := (5025853967 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_174 :
    (20147 / 25000 : ℝ) ≤ Real.exp (-(221 / 1024 : ℝ)) ∧
    Real.exp (-(221 / 1024 : ℝ)) ≤ (8058801 / 10000000 : ℝ) := by
  have hsmall : (10067671793 / 10000000000 : ℝ) ≤ Real.exp (221 / 32768 : ℝ) ∧
      Real.exp (221 / 32768 : ℝ) ≤ (5033835897 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (221 / 32768 : ℝ))
    (a := (10067671793 / 10000000000 : ℝ)) (b := (5033835897 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_175 :
    (1533549 / 10000000 : ℝ) ≤ Real.exp (-(15 / 8 : ℝ)) ∧
    Real.exp (-(15 / 8 : ℝ)) ≤ (30671 / 200000 : ℝ) := by
  have hsmall : (10603443883 / 10000000000 : ℝ) ≤ Real.exp (15 / 256 : ℝ) ∧
      Real.exp (15 / 256 : ℝ) ≤ (2650860971 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15 / 256 : ℝ))
    (a := (10603443883 / 10000000000 : ℝ)) (b := (2650860971 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_176 :
    (1235367 / 2000000 : ℝ) ≤ Real.exp (-(481779 / 1000000 : ℝ)) ∧
    Real.exp (-(481779 / 1000000 : ℝ)) ≤ (1544209 / 2500000 : ℝ) := by
  have hsmall : (10151695001 / 10000000000 : ℝ) ≤ Real.exp (481779 / 32000000 : ℝ) ∧
      Real.exp (481779 / 32000000 : ℝ) ≤ (5075847501 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (481779 / 32000000 : ℝ))
    (a := (10151695001 / 10000000000 : ℝ)) (b := (5075847501 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_177 :
    (6269077 / 10000000 : ℝ) ≤ Real.exp (-(2334779 / 5000000 : ℝ)) ∧
    Real.exp (-(2334779 / 5000000 : ℝ)) ≤ (3134539 / 5000000 : ℝ) := by
  have hsmall : (10146993571 / 10000000000 : ℝ) ≤ Real.exp (2334779 / 160000000 : ℝ) ∧
      Real.exp (2334779 / 160000000 : ℝ) ≤ (2536748393 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2334779 / 160000000 : ℝ))
    (a := (10146993571 / 10000000000 : ℝ)) (b := (2536748393 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_178 :
    (173763 / 200000 : ℝ) ≤ Real.exp (-(9 / 64 : ℝ)) ∧
    Real.exp (-(9 / 64 : ℝ)) ≤ (8688151 / 10000000 : ℝ) := by
  have hsmall : (10044042013 / 10000000000 : ℝ) ≤ Real.exp (9 / 2048 : ℝ) ∧
      Real.exp (9 / 2048 : ℝ) ≤ (5022021007 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 2048 : ℝ))
    (a := (10044042013 / 10000000000 : ℝ)) (b := (5022021007 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_179 :
    (4096853 / 5000000 : ℝ) ≤ Real.exp (-(51 / 256 : ℝ)) ∧
    Real.exp (-(51 / 256 : ℝ)) ≤ (8193707 / 10000000 : ℝ) := by
  have hsmall : (10062450051 / 10000000000 : ℝ) ≤ Real.exp (51 / 8192 : ℝ) ∧
      Real.exp (51 / 8192 : ℝ) ≤ (2515612513 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51 / 8192 : ℝ))
    (a := (10062450051 / 10000000000 : ℝ)) (b := (2515612513 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_180 :
    (1582229 / 10000000 : ℝ) ≤ Real.exp (-(59 / 32 : ℝ)) ∧
    Real.exp (-(59 / 32 : ℝ)) ≤ (158223 / 1000000 : ℝ) := by
  have hsmall : (2648273503 / 2500000000 : ℝ) ≤ Real.exp (59 / 1024 : ℝ) ∧
      Real.exp (59 / 1024 : ℝ) ≤ (10593094013 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (59 / 1024 : ℝ))
    (a := (2648273503 / 2500000000 : ℝ)) (b := (10593094013 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_181 :
    (608309 / 1000000 : ℝ) ≤ Real.exp (-(4970723 / 10000000 : ℝ)) ∧
    Real.exp (-(4970723 / 10000000 : ℝ)) ≤ (6083091 / 10000000 : ℝ) := by
  have hsmall : (5078273907 / 5000000000 : ℝ) ≤ Real.exp (4970723 / 320000000 : ℝ) ∧
      Real.exp (4970723 / 320000000 : ℝ) ≤ (2031309563 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4970723 / 320000000 : ℝ))
    (a := (5078273907 / 5000000000 : ℝ)) (b := (2031309563 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_182 :
    (3088419 / 5000000 : ℝ) ≤ Real.exp (-(963557 / 2000000 : ℝ)) ∧
    Real.exp (-(963557 / 2000000 : ℝ)) ≤ (6176839 / 10000000 : ℝ) := by
  have hsmall : (5075847421 / 5000000000 : ℝ) ≤ Real.exp (963557 / 64000000 : ℝ) ∧
      Real.exp (963557 / 64000000 : ℝ) ≤ (10151694843 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (963557 / 64000000 : ℝ))
    (a := (5075847421 / 5000000000 : ℝ)) (b := (10151694843 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_183 :
    (4442751 / 5000000 : ℝ) ≤ Real.exp (-(121 / 1024 : ℝ)) ∧
    Real.exp (-(121 / 1024 : ℝ)) ≤ (8885503 / 10000000 : ℝ) := by
  have hsmall : (1003699453 / 1000000000 : ℝ) ≤ Real.exp (121 / 32768 : ℝ) ∧
      Real.exp (121 / 32768 : ℝ) ≤ (10036994531 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (121 / 32768 : ℝ))
    (a := (1003699453 / 1000000000 : ℝ)) (b := (10036994531 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_184 :
    (833087 / 1000000 : ℝ) ≤ Real.exp (-(187 / 1024 : ℝ)) ∧
    Real.exp (-(187 / 1024 : ℝ)) ≤ (8330871 / 10000000 : ℝ) := by
  have hsmall : (5028615509 / 5000000000 : ℝ) ≤ Real.exp (187 / 32768 : ℝ) ∧
      Real.exp (187 / 32768 : ℝ) ≤ (10057231019 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (187 / 32768 : ℝ))
    (a := (5028615509 / 5000000000 : ℝ)) (b := (10057231019 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_185 :
    (326491 / 2000000 : ℝ) ≤ Real.exp (-(29 / 16 : ℝ)) ∧
    Real.exp (-(29 / 16 : ℝ)) ≤ (204057 / 1250000 : ℝ) := by
  have hsmall : (10582754243 / 10000000000 : ℝ) ≤ Real.exp (29 / 512 : ℝ) ∧
      Real.exp (29 / 512 : ℝ) ≤ (2645688561 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29 / 512 : ℝ))
    (a := (10582754243 / 10000000000 : ℝ)) (b := (2645688561 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_186 :
    (2993929 / 5000000 : ℝ) ≤ Real.exp (-(5128513 / 10000000 : ℝ)) ∧
    Real.exp (-(5128513 / 10000000 : ℝ)) ≤ (5987859 / 10000000 : ℝ) := by
  have hsmall : (10161557179 / 10000000000 : ℝ) ≤ Real.exp (5128513 / 320000000 : ℝ) ∧
      Real.exp (5128513 / 320000000 : ℝ) ≤ (508077859 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5128513 / 320000000 : ℝ))
    (a := (10161557179 / 10000000000 : ℝ)) (b := (508077859 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_187 :
    (6083093 / 10000000 : ℝ) ≤ Real.exp (-(4970717 / 10000000 : ℝ)) ∧
    Real.exp (-(4970717 / 10000000 : ℝ)) ≤ (3041547 / 5000000 : ℝ) := by
  have hsmall : (1269568453 / 1250000000 : ℝ) ≤ Real.exp (4970717 / 320000000 : ℝ) ∧
      Real.exp (4970717 / 320000000 : ℝ) ≤ (81252381 / 80000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4970717 / 320000000 : ℝ))
    (a := (1269568453 / 1250000000 : ℝ)) (b := (81252381 / 80000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_188 :
    (4534803 / 5000000 : ℝ) ≤ Real.exp (-(25 / 256 : ℝ)) ∧
    Real.exp (-(25 / 256 : ℝ)) ≤ (9069607 / 10000000 : ℝ) := by
  have hsmall : (10030564191 / 10000000000 : ℝ) ≤ Real.exp (25 / 8192 : ℝ) ∧
      Real.exp (25 / 8192 : ℝ) ≤ (313455131 / 312500000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 8192 : ℝ))
    (a := (10030564191 / 10000000000 : ℝ)) (b := (313455131 / 312500000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_189 :
    (8470329 / 10000000 : ℝ) ≤ Real.exp (-(85 / 512 : ℝ)) ∧
    Real.exp (-(85 / 512 : ℝ)) ≤ (8470331 / 10000000 : ℝ) := by
  have hsmall : (10052014691 / 10000000000 : ℝ) ≤ Real.exp (85 / 16384 : ℝ) ∧
      Real.exp (85 / 16384 : ℝ) ≤ (2513003673 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (85 / 16384 : ℝ))
    (a := (10052014691 / 10000000000 : ℝ)) (b := (2513003673 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_190 :
    (842137 / 5000000 : ℝ) ≤ Real.exp (-(57 / 32 : ℝ)) ∧
    Real.exp (-(57 / 32 : ℝ)) ≤ (67371 / 400000 : ℝ) := by
  have hsmall : (5286212283 / 5000000000 : ℝ) ≤ Real.exp (57 / 1024 : ℝ) ∧
      Real.exp (57 / 1024 : ℝ) ≤ (10572424567 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (57 / 1024 : ℝ))
    (a := (5286212283 / 5000000000 : ℝ)) (b := (10572424567 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_191 :
    (184099 / 312500 : ℝ) ≤ Real.exp (-(5291307 / 10000000 : ℝ)) ∧
    Real.exp (-(5291307 / 10000000 : ℝ)) ≤ (5891169 / 10000000 : ℝ) := by
  have hsmall : (2541681999 / 2500000000 : ℝ) ≤ Real.exp (5291307 / 320000000 : ℝ) ∧
      Real.exp (5291307 / 320000000 : ℝ) ≤ (10166727997 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5291307 / 320000000 : ℝ))
    (a := (2541681999 / 2500000000 : ℝ)) (b := (10166727997 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_192 :
    (5987861 / 10000000 : ℝ) ≤ Real.exp (-(5128507 / 10000000 : ℝ)) ∧
    Real.exp (-(5128507 / 10000000 : ℝ)) ≤ (2993931 / 5000000 : ℝ) := by
  have hsmall : (10161556989 / 10000000000 : ℝ) ≤ Real.exp (5128507 / 320000000 : ℝ) ∧
      Real.exp (5128507 / 320000000 : ℝ) ≤ (1016155699 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5128507 / 320000000 : ℝ))
    (a := (10161556989 / 10000000000 : ℝ)) (b := (1016155699 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_193 :
    (461973 / 500000 : ℝ) ≤ Real.exp (-(81 / 1024 : ℝ)) ∧
    Real.exp (-(81 / 1024 : ℝ)) ≤ (9239461 / 10000000 : ℝ) := by
  have hsmall : (2004949963 / 2000000000 : ℝ) ≤ Real.exp (81 / 32768 : ℝ) ∧
      Real.exp (81 / 32768 : ℝ) ≤ (1253093727 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (81 / 32768 : ℝ))
    (a := (2004949963 / 2000000000 : ℝ)) (b := (1253093727 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_194 :
    (2153031 / 2500000 : ℝ) ≤ Real.exp (-(153 / 1024 : ℝ)) ∧
    Real.exp (-(153 / 1024 : ℝ)) ≤ (68897 / 80000 : ℝ) := by
  have hsmall : (10046801071 / 10000000000 : ℝ) ≤ Real.exp (153 / 32768 : ℝ) ∧
      Real.exp (153 / 32768 : ℝ) ≤ (627925067 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (153 / 32768 : ℝ))
    (a := (10046801071 / 10000000000 : ℝ)) (b := (627925067 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_195 :
    (1737739 / 10000000 : ℝ) ≤ Real.exp (-(7 / 4 : ℝ)) ∧
    Real.exp (-(7 / 4 : ℝ)) ≤ (86887 / 500000 : ℝ) := by
  have hsmall : (10562104973 / 10000000000 : ℝ) ≤ Real.exp (7 / 128 : ℝ) ∧
      Real.exp (7 / 128 : ℝ) ≤ (5281052487 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7 / 128 : ℝ))
    (a := (10562104973 / 10000000000 : ℝ)) (b := (5281052487 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_196 :
    (1448261 / 2500000 : ℝ) ≤ Real.exp (-(682409 / 1250000 : ℝ)) ∧
    Real.exp (-(682409 / 1250000 : ℝ)) ≤ (1158609 / 2000000 : ℝ) := by
  have hsmall : (10172065817 / 10000000000 : ℝ) ≤ Real.exp (682409 / 40000000 : ℝ) ∧
      Real.exp (682409 / 40000000 : ℝ) ≤ (5086032909 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (682409 / 40000000 : ℝ))
    (a := (10172065817 / 10000000000 : ℝ)) (b := (5086032909 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_197 :
    (1472793 / 2500000 : ℝ) ≤ Real.exp (-(5291301 / 10000000 : ℝ)) ∧
    Real.exp (-(5291301 / 10000000 : ℝ)) ≤ (5891173 / 10000000 : ℝ) := by
  have hsmall : (2033345561 / 2000000000 : ℝ) ≤ Real.exp (5291301 / 320000000 : ℝ) ∧
      Real.exp (5291301 / 320000000 : ℝ) ≤ (5083363903 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5291301 / 320000000 : ℝ))
    (a := (2033345561 / 2000000000 : ℝ)) (b := (5083363903 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_198 :
    (939413 / 1000000 : ℝ) ≤ Real.exp (-(1 / 16 : ℝ)) ∧
    Real.exp (-(1 / 16 : ℝ)) ≤ (9394131 / 10000000 : ℝ) := by
  have hsmall : (2003910067 / 2000000000 : ℝ) ≤ Real.exp (1 / 512 : ℝ) ∧
      Real.exp (1 / 512 : ℝ) ≤ (78277737 / 78125000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 512 : ℝ))
    (a := (2003910067 / 2000000000 : ℝ)) (b := (78277737 / 78125000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_199 :
    (2189073 / 2500000 : ℝ) ≤ Real.exp (-(17 / 128 : ℝ)) ∧
    Real.exp (-(17 / 128 : ℝ)) ≤ (8756293 / 10000000 : ℝ) := by
  have hsmall : (5020795077 / 5000000000 : ℝ) ≤ Real.exp (17 / 4096 : ℝ) ∧
      Real.exp (17 / 4096 : ℝ) ≤ (2008318031 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 4096 : ℝ))
    (a := (5020795077 / 5000000000 : ℝ)) (b := (2008318031 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_200 :
    (1792901 / 10000000 : ℝ) ≤ Real.exp (-(55 / 32 : ℝ)) ∧
    Real.exp (-(55 / 32 : ℝ)) ≤ (896451 / 5000000 : ℝ) := by
  have hsmall : (2637948863 / 2500000000 : ℝ) ≤ Real.exp (55 / 1024 : ℝ) ∧
      Real.exp (55 / 1024 : ℝ) ≤ (10551795453 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (55 / 1024 : ℝ))
    (a := (2637948863 / 2500000000 : ℝ)) (b := (10551795453 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_201 :
    (5693517 / 10000000 : ℝ) ≤ Real.exp (-(5632569 / 10000000 : ℝ)) ∧
    Real.exp (-(5632569 / 10000000 : ℝ)) ≤ (2846759 / 5000000 : ℝ) := by
  have hsmall : (10177576023 / 10000000000 : ℝ) ≤ Real.exp (5632569 / 320000000 : ℝ) ∧
      Real.exp (5632569 / 320000000 : ℝ) ≤ (1272197003 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5632569 / 320000000 : ℝ))
    (a := (10177576023 / 10000000000 : ℝ)) (b := (1272197003 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_202 :
    (5793047 / 10000000 : ℝ) ≤ Real.exp (-(2729633 / 5000000 : ℝ)) ∧
    Real.exp (-(2729633 / 5000000 : ℝ)) ≤ (724131 / 1250000 : ℝ) := by
  have hsmall : (5086032813 / 5000000000 : ℝ) ≤ Real.exp (2729633 / 160000000 : ℝ) ∧
      Real.exp (2729633 / 160000000 : ℝ) ≤ (10172065627 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2729633 / 160000000 : ℝ))
    (a := (5086032813 / 5000000000 : ℝ)) (b := (10172065627 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_203 :
    (595797 / 625000 : ℝ) ≤ Real.exp (-(49 / 1024 : ℝ)) ∧
    Real.exp (-(49 / 1024 : ℝ)) ≤ (9532753 / 10000000 : ℝ) := by
  have hsmall : (10014964799 / 10000000000 : ℝ) ≤ Real.exp (49 / 32768 : ℝ) ∧
      Real.exp (49 / 32768 : ℝ) ≤ (6259353 / 6250000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 32768 : ℝ))
    (a := (10014964799 / 10000000000 : ℝ)) (b := (6259353 / 6250000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_204 :
    (4451437 / 5000000 : ℝ) ≤ Real.exp (-(119 / 1024 : ℝ)) ∧
    Real.exp (-(119 / 1024 : ℝ)) ≤ (71223 / 80000 : ℝ) := by
  have hsmall : (501819097 / 500000000 : ℝ) ≤ Real.exp (119 / 32768 : ℝ) ∧
      Real.exp (119 / 32768 : ℝ) ≤ (10036381941 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (119 / 32768 : ℝ))
    (a := (501819097 / 500000000 : ℝ)) (b := (10036381941 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_205 :
    (1849813 / 10000000 : ℝ) ≤ Real.exp (-(27 / 16 : ℝ)) ∧
    Real.exp (-(27 / 16 : ℝ)) ≤ (369963 / 2000000 : ℝ) := by
  have hsmall : (5270747997 / 5000000000 : ℝ) ≤ Real.exp (27 / 512 : ℝ) ∧
      Real.exp (27 / 512 : ℝ) ≤ (2108299199 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (27 / 512 : ℝ))
    (a := (5270747997 / 5000000000 : ℝ)) (b := (2108299199 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_206 :
    (5592623 / 10000000 : ℝ) ≤ Real.exp (-(2905683 / 5000000 : ℝ)) ∧
    Real.exp (-(2905683 / 5000000 : ℝ)) ≤ (349539 / 625000 : ℝ) := by
  have hsmall : (10183264237 / 10000000000 : ℝ) ≤ Real.exp (2905683 / 160000000 : ℝ) ∧
      Real.exp (2905683 / 160000000 : ℝ) ≤ (5091632119 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2905683 / 160000000 : ℝ))
    (a := (10183264237 / 10000000000 : ℝ)) (b := (5091632119 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_207 :
    (71169 / 125000 : ℝ) ≤ Real.exp (-(5632563 / 10000000 : ℝ)) ∧
    Real.exp (-(5632563 / 10000000 : ℝ)) ≤ (5693521 / 10000000 : ℝ) := by
  have hsmall : (1272196979 / 1250000000 : ℝ) ≤ Real.exp (5632563 / 320000000 : ℝ) ∧
      Real.exp (5632563 / 320000000 : ℝ) ≤ (10177575833 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5632563 / 320000000 : ℝ))
    (a := (1272196979 / 1250000000 : ℝ)) (b := (10177575833 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_208 :
    (1930909 / 2000000 : ℝ) ≤ Real.exp (-(9 / 256 : ℝ)) ∧
    Real.exp (-(9 / 256 : ℝ)) ≤ (4827273 / 5000000 : ℝ) := by
  have hsmall : (2002198473 / 2000000000 : ℝ) ≤ Real.exp (9 / 8192 : ℝ) ∧
      Real.exp (9 / 8192 : ℝ) ≤ (5005496183 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 8192 : ℝ))
    (a := (2002198473 / 2000000000 : ℝ)) (b := (5005496183 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_209 :
    (9051909 / 10000000 : ℝ) ≤ Real.exp (-(51 / 512 : ℝ)) ∧
    Real.exp (-(51 / 512 : ℝ)) ≤ (905191 / 1000000 : ℝ) := by
  have hsmall : (10031176427 / 10000000000 : ℝ) ≤ Real.exp (51 / 16384 : ℝ) ∧
      Real.exp (51 / 16384 : ℝ) ≤ (2507794107 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51 / 16384 : ℝ))
    (a := (10031176427 / 10000000000 : ℝ)) (b := (2507794107 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_210 :
    (1908533 / 10000000 : ℝ) ≤ Real.exp (-(53 / 32 : ℝ)) ∧
    Real.exp (-(53 / 32 : ℝ)) ≤ (954267 / 5000000 : ℝ) := by
  have hsmall : (10531206589 / 10000000000 : ℝ) ≤ Real.exp (53 / 1024 : ℝ) ∧
      Real.exp (53 / 1024 : ℝ) ≤ (1053120659 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (53 / 1024 : ℝ))
    (a := (10531206589 / 10000000000 : ℝ)) (b := (1053120659 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_211 :
    (6863 / 12500 : ℝ) ≤ Real.exp (-(2997919 / 5000000 : ℝ)) ∧
    Real.exp (-(2997919 / 5000000 : ℝ)) ≤ (5490401 / 10000000 : ℝ) := by
  have hsmall : (10189136327 / 10000000000 : ℝ) ≤ Real.exp (2997919 / 160000000 : ℝ) ∧
      Real.exp (2997919 / 160000000 : ℝ) ≤ (1273642041 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2997919 / 160000000 : ℝ))
    (a := (10189136327 / 10000000000 : ℝ)) (b := (1273642041 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_212 :
    (1398157 / 2500000 : ℝ) ≤ Real.exp (-(5811357 / 10000000 : ℝ)) ∧
    Real.exp (-(5811357 / 10000000 : ℝ)) ≤ (5592629 / 10000000 : ℝ) := by
  have hsmall : (10183263951 / 10000000000 : ℝ) ≤ Real.exp (5811357 / 320000000 : ℝ) ∧
      Real.exp (5811357 / 320000000 : ℝ) ≤ (636453997 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5811357 / 320000000 : ℝ))
    (a := (10183263951 / 10000000000 : ℝ)) (b := (636453997 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_213 :
    (1951763 / 2000000 : ℝ) ≤ Real.exp (-(25 / 1024 : ℝ)) ∧
    Real.exp (-(25 / 1024 : ℝ)) ≤ (304963 / 312500 : ℝ) := by
  have hsmall : (2001526461 / 2000000000 : ℝ) ≤ Real.exp (25 / 32768 : ℝ) ∧
      Real.exp (25 / 32768 : ℝ) ≤ (5003816153 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 32768 : ℝ))
    (a := (2001526461 / 2000000000 : ℝ)) (b := (5003816153 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_214 :
    (9203439 / 10000000 : ℝ) ≤ Real.exp (-(85 / 1024 : ℝ)) ∧
    Real.exp (-(85 / 1024 : ℝ)) ≤ (115043 / 125000 : ℝ) := by
  have hsmall : (5012986807 / 5000000000 : ℝ) ≤ Real.exp (85 / 32768 : ℝ) ∧
      Real.exp (85 / 32768 : ℝ) ≤ (2005194723 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (85 / 32768 : ℝ))
    (a := (5012986807 / 5000000000 : ℝ)) (b := (2005194723 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_215 :
    (492279 / 2500000 : ℝ) ≤ Real.exp (-(13 / 8 : ℝ)) ∧
    Real.exp (-(13 / 8 : ℝ)) ≤ (1969117 / 10000000 : ℝ) := by
  have hsmall : (2630231807 / 2500000000 : ℝ) ≤ Real.exp (13 / 256 : ℝ) ∧
      Real.exp (13 / 256 : ℝ) ≤ (10520927229 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13 / 256 : ℝ))
    (a := (2630231807 / 2500000000 : ℝ)) (b := (10520927229 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_216 :
    (5386891 / 10000000 : ℝ) ≤ Real.exp (-(1237233 / 2000000 : ℝ)) ∧
    Real.exp (-(1237233 / 2000000 : ℝ)) ≤ (1346723 / 2500000 : ℝ) := by
  have hsmall : (10195198341 / 10000000000 : ℝ) ≤ Real.exp (1237233 / 64000000 : ℝ) ∧
      Real.exp (1237233 / 64000000 : ℝ) ≤ (5097599171 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1237233 / 64000000 : ℝ))
    (a := (10195198341 / 10000000000 : ℝ)) (b := (5097599171 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_217 :
    (1372601 / 2500000 : ℝ) ≤ Real.exp (-(749479 / 1250000 : ℝ)) ∧
    Real.exp (-(749479 / 1250000 : ℝ)) ≤ (1098081 / 2000000 : ℝ) := by
  have hsmall : (1273642017 / 1250000000 : ℝ) ≤ Real.exp (749479 / 40000000 : ℝ) ∧
      Real.exp (749479 / 40000000 : ℝ) ≤ (10189136137 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (749479 / 40000000 : ℝ))
    (a := (1273642017 / 1250000000 : ℝ)) (b := (10189136137 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_218 :
    (2461241 / 2500000 : ℝ) ≤ Real.exp (-(1 / 64 : ℝ)) ∧
    Real.exp (-(1 / 64 : ℝ)) ≤ (1968993 / 2000000 : ℝ) := by
  have hsmall : (2501221001 / 2500000000 : ℝ) ≤ Real.exp (1 / 2048 : ℝ) ∧
      Real.exp (1 / 2048 : ℝ) ≤ (2000976801 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 2048 : ℝ))
    (a := (2501221001 / 2500000000 : ℝ)) (b := (2000976801 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_219 :
    (4678753 / 5000000 : ℝ) ≤ Real.exp (-(17 / 256 : ℝ)) ∧
    Real.exp (-(17 / 256 : ℝ)) ≤ (9357507 / 10000000 : ℝ) := by
  have hsmall : (20041547 / 20000000 : ℝ) ≤ Real.exp (17 / 8192 : ℝ) ∧
      Real.exp (17 / 8192 : ℝ) ≤ (10020773501 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 8192 : ℝ))
    (a := (20041547 / 20000000 : ℝ)) (b := (10020773501 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_220 :
    (2031623 / 10000000 : ℝ) ≤ Real.exp (-(51 / 32 : ℝ)) ∧
    Real.exp (-(51 / 32 : ℝ)) ≤ (253953 / 1250000 : ℝ) := by
  have hsmall : (105106579 / 100000000 : ℝ) ≤ Real.exp (51 / 1024 : ℝ) ∧
      Real.exp (51 / 1024 : ℝ) ≤ (10510657901 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51 / 1024 : ℝ))
    (a := (105106579 / 100000000 : ℝ)) (b := (10510657901 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_221 :
    (264107 / 500000 : ℝ) ≤ Real.exp (-(797817 / 1250000 : ℝ)) ∧
    Real.exp (-(797817 / 1250000 : ℝ)) ≤ (5282141 / 10000000 : ℝ) := by
  have hsmall : (1992472 / 1953125 : ℝ) ≤ Real.exp (797817 / 40000000 : ℝ) ∧
      Real.exp (797817 / 40000000 : ℝ) ≤ (10201456641 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (797817 / 40000000 : ℝ))
    (a := (1992472 / 1953125 : ℝ)) (b := (10201456641 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_222 :
    (1077379 / 2000000 : ℝ) ≤ Real.exp (-(6186159 / 10000000 : ℝ)) ∧
    Real.exp (-(6186159 / 10000000 : ℝ)) ≤ (336681 / 625000 : ℝ) := by
  have hsmall : (203903963 / 200000000 : ℝ) ≤ Real.exp (6186159 / 320000000 : ℝ) ∧
      Real.exp (6186159 / 320000000 : ℝ) ≤ (10195198151 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6186159 / 320000000 : ℝ))
    (a := (203903963 / 200000000 : ℝ)) (b := (10195198151 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_223 :
    (4956247 / 5000000 : ℝ) ≤ Real.exp (-(9 / 1024 : ℝ)) ∧
    Real.exp (-(9 / 1024 : ℝ)) ≤ (1982499 / 2000000 : ℝ) := by
  have hsmall : (10002746959 / 10000000000 : ℝ) ≤ Real.exp (9 / 32768 : ℝ) ∧
      Real.exp (9 / 32768 : ℝ) ≤ (125034337 / 125000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 32768 : ℝ))
    (a := (10002746959 / 10000000000 : ℝ)) (b := (125034337 / 125000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_224 :
    (1189269 / 1250000 : ℝ) ≤ Real.exp (-(51 / 1024 : ℝ)) ∧
    Real.exp (-(51 / 1024 : ℝ)) ≤ (9514153 / 10000000 : ℝ) := by
  have hsmall : (5007788041 / 5000000000 : ℝ) ≤ Real.exp (51 / 32768 : ℝ) ∧
      Real.exp (51 / 32768 : ℝ) ≤ (10015576083 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51 / 32768 : ℝ))
    (a := (5007788041 / 5000000000 : ℝ)) (b := (10015576083 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_225 :
    (2096113 / 10000000 : ℝ) ≤ Real.exp (-(25 / 16 : ℝ)) ∧
    Real.exp (-(25 / 16 : ℝ)) ≤ (1048057 / 5000000 : ℝ) := by
  have hsmall : (2625099649 / 2500000000 : ℝ) ≤ Real.exp (25 / 512 : ℝ) ∧
      Real.exp (25 / 512 : ℝ) ≤ (10500398597 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 512 : ℝ))
    (a := (2625099649 / 2500000000 : ℝ)) (b := (10500398597 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_226 :
    (25881 / 50000 : ℝ) ≤ Real.exp (-(3292569 / 5000000 : ℝ)) ∧
    Real.exp (-(3292569 / 5000000 : ℝ)) ≤ (5176201 / 10000000 : ℝ) := by
  have hsmall : (5103958773 / 5000000000 : ℝ) ≤ Real.exp (3292569 / 160000000 : ℝ) ∧
      Real.exp (3292569 / 160000000 : ℝ) ≤ (10207917547 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3292569 / 160000000 : ℝ))
    (a := (5103958773 / 5000000000 : ℝ)) (b := (10207917547 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_227 :
    (165067 / 312500 : ℝ) ≤ Real.exp (-(638253 / 1000000 : ℝ)) ∧
    Real.exp (-(638253 / 1000000 : ℝ)) ≤ (1056429 / 2000000 : ℝ) := by
  have hsmall : (10201456449 / 10000000000 : ℝ) ≤ Real.exp (638253 / 32000000 : ℝ) ∧
      Real.exp (638253 / 32000000 : ℝ) ≤ (204029129 / 200000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (638253 / 32000000 : ℝ))
    (a := (10201456449 / 10000000000 : ℝ)) (b := (204029129 / 200000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_228 :
    (9961013 / 10000000 : ℝ) ≤ Real.exp (-(1 / 256 : ℝ)) ∧
    Real.exp (-(1 / 256 : ℝ)) ≤ (4980507 / 5000000 : ℝ) := by
  have hsmall : (10001220777 / 10000000000 : ℝ) ≤ Real.exp (1 / 8192 : ℝ) ∧
      Real.exp (1 / 8192 : ℝ) ≤ (5000610389 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 8192 : ℝ))
    (a := (10001220777 / 10000000000 : ℝ)) (b := (5000610389 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_229 :
    (483671 / 500000 : ℝ) ≤ Real.exp (-(17 / 512 : ℝ)) ∧
    Real.exp (-(17 / 512 : ℝ)) ≤ (9673421 / 10000000 : ℝ) := by
  have hsmall : (10010381361 / 10000000000 : ℝ) ≤ Real.exp (17 / 16384 : ℝ) ∧
      Real.exp (17 / 16384 : ℝ) ≤ (5005190681 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 16384 : ℝ))
    (a := (10010381361 / 10000000000 : ℝ)) (b := (5005190681 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_230 :
    (2162651 / 10000000 : ℝ) ≤ Real.exp (-(49 / 32 : ℝ)) ∧
    Real.exp (-(49 / 32 : ℝ)) ≤ (540663 / 2500000 : ℝ) := by
  have hsmall : (5245074653 / 5000000000 : ℝ) ≤ Real.exp (49 / 1024 : ℝ) ∧
      Real.exp (49 / 1024 : ℝ) ≤ (10490149307 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 1024 : ℝ))
    (a := (5245074653 / 5000000000 : ℝ)) (b := (10490149307 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_231 :
    (2534561 / 5000000 : ℝ) ≤ Real.exp (-(6794173 / 10000000 : ℝ)) ∧
    Real.exp (-(6794173 / 10000000 : ℝ)) ≤ (5069123 / 10000000 : ℝ) := by
  have hsmall : (10214587887 / 10000000000 : ℝ) ≤ Real.exp (6794173 / 320000000 : ℝ) ∧
      Real.exp (6794173 / 320000000 : ℝ) ≤ (638411743 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6794173 / 320000000 : ℝ))
    (a := (10214587887 / 10000000000 : ℝ)) (b := (638411743 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_232 :
    (1294051 / 2500000 : ℝ) ≤ Real.exp (-(6585131 / 10000000 : ℝ)) ∧
    Real.exp (-(6585131 / 10000000 : ℝ)) ≤ (1035241 / 2000000 : ℝ) := by
  have hsmall : (10207917323 / 10000000000 : ℝ) ≤ Real.exp (6585131 / 320000000 : ℝ) ∧
      Real.exp (6585131 / 320000000 : ℝ) ≤ (2551979331 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6585131 / 320000000 : ℝ))
    (a := (10207917323 / 10000000000 : ℝ)) (b := (2551979331 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_233 :
    (9990239 / 10000000 : ℝ) ≤ Real.exp (-(1 / 1024 : ℝ)) ∧
    Real.exp (-(1 / 1024 : ℝ)) ≤ (62439 / 62500 : ℝ) := by
  have hsmall : (500015259 / 500000000 : ℝ) ≤ Real.exp (1 / 32768 : ℝ) ∧
      Real.exp (1 / 32768 : ℝ) ≤ (10000305181 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 32768 : ℝ))
    (a := (500015259 / 500000000 : ℝ)) (b := (10000305181 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_234 :
    (4917677 / 5000000 : ℝ) ≤ Real.exp (-(17 / 1024 : ℝ)) ∧
    Real.exp (-(17 / 1024 : ℝ)) ≤ (1967071 / 2000000 : ℝ) := by
  have hsmall : (5002594667 / 5000000000 : ℝ) ≤ Real.exp (17 / 32768 : ℝ) ∧
      Real.exp (17 / 32768 : ℝ) ≤ (2001037867 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 32768 : ℝ))
    (a := (5002594667 / 5000000000 : ℝ)) (b := (2001037867 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_235 :
    (2231301 / 10000000 : ℝ) ≤ Real.exp (-(3 / 2 : ℝ)) ∧
    Real.exp (-(3 / 2 : ℝ)) ≤ (1115651 / 5000000 : ℝ) := by
  have hsmall : (523995501 / 500000000 : ℝ) ≤ Real.exp (3 / 64 : ℝ) ∧
      Real.exp (3 / 64 : ℝ) ≤ (10479910021 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3 / 64 : ℝ))
    (a := (523995501 / 500000000 : ℝ)) (b := (10479910021 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_236 :
    (4960967 / 10000000 : ℝ) ≤ Real.exp (-(7009843 / 10000000 : ℝ)) ∧
    Real.exp (-(7009843 / 10000000 : ℝ)) ≤ (620121 / 1250000 : ℝ) := by
  have hsmall : (10221474521 / 10000000000 : ℝ) ≤ Real.exp (7009843 / 320000000 : ℝ) ∧
      Real.exp (7009843 / 320000000 : ℝ) ≤ (5110737261 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7009843 / 320000000 : ℝ))
    (a := (10221474521 / 10000000000 : ℝ)) (b := (5110737261 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_237 :
    (40553 / 80000 : ℝ) ≤ Real.exp (-(6794167 / 10000000 : ℝ)) ∧
    Real.exp (-(6794167 / 10000000 : ℝ)) ≤ (2534563 / 5000000 : ℝ) := by
  have hsmall : (638411731 / 625000000 : ℝ) ≤ Real.exp (6794167 / 320000000 : ℝ) ∧
      Real.exp (6794167 / 320000000 : ℝ) ≤ (10214587697 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6794167 / 320000000 : ℝ))
    (a := (638411731 / 625000000 : ℝ)) (b := (10214587697 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_238 :
    (1 / 1 : ℝ) ≤ Real.exp (0 / 1 : ℝ) ∧
    Real.exp (0 / 1 : ℝ) ≤ (1 / 1 : ℝ) := by
  have hsmall : (1 / 1 : ℝ) ≤ Real.exp (0 / 1 : ℝ) ∧
      Real.exp (0 / 1 : ℝ) ≤ (1 / 1 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (0 / 1 : ℝ))
    (a := (1 / 1 : ℝ)) (b := (1 / 1 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_239 :
    (230213 / 1000000 : ℝ) ≤ Real.exp (-(47 / 32 : ℝ)) ∧
    Real.exp (-(47 / 32 : ℝ)) ≤ (2302131 / 10000000 : ℝ) := by
  have hsmall : (1308710091 / 1250000000 : ℝ) ≤ Real.exp (47 / 1024 : ℝ) ∧
      Real.exp (47 / 1024 : ℝ) ≤ (10469680729 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (47 / 1024 : ℝ))
    (a := (1308710091 / 1250000000 : ℝ)) (b := (10469680729 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_240 :
    (4851797 / 10000000 : ℝ) ≤ Real.exp (-(7232359 / 10000000 : ℝ)) ∧
    Real.exp (-(7232359 / 10000000 : ℝ)) ≤ (2425899 / 5000000 : ℝ) := by
  have hsmall : (10228584623 / 10000000000 : ℝ) ≤ Real.exp (7232359 / 320000000 : ℝ) ∧
      Real.exp (7232359 / 320000000 : ℝ) ≤ (639286539 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7232359 / 320000000 : ℝ))
    (a := (10228584623 / 10000000000 : ℝ)) (b := (639286539 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_241 :
    (496097 / 1000000 : ℝ) ≤ Real.exp (-(7009837 / 10000000 : ℝ)) ∧
    Real.exp (-(7009837 / 10000000 : ℝ)) ≤ (4960971 / 10000000 : ℝ) := by
  have hsmall : (10221474329 / 10000000000 : ℝ) ≤ Real.exp (7009837 / 320000000 : ℝ) ∧
      Real.exp (7009837 / 320000000 : ℝ) ≤ (1022147433 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7009837 / 320000000 : ℝ))
    (a := (10221474329 / 10000000000 : ℝ)) (b := (1022147433 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_242 :
    (10307363 / 10000000 : ℝ) ≤ Real.exp (31 / 1024 : ℝ) ∧
    Real.exp (31 / 1024 : ℝ) ≤ (2576841 / 2500000 : ℝ) := by
  have hsmall : (3127957789261 / 3125000000000 : ℝ) ≤ Real.exp (31 / 32768 : ℝ) ∧
      Real.exp (31 / 32768 : ℝ) ≤ (100094649256353 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 32768 : ℝ))
    (a := (3127957789261 / 3125000000000 : ℝ)) (b := (100094649256353 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_243 :
    (296901 / 1250000 : ℝ) ≤ Real.exp (-(23 / 16 : ℝ)) ∧
    Real.exp (-(23 / 16 : ℝ)) ≤ (2375209 / 10000000 : ℝ) := by
  have hsmall : (10459461421 / 10000000000 : ℝ) ≤ Real.exp (23 / 512 : ℝ) ∧
      Real.exp (23 / 512 : ℝ) ≤ (5229730711 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (23 / 512 : ℝ))
    (a := (10459461421 / 10000000000 : ℝ)) (b := (5229730711 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_244 :
    (2370839 / 5000000 : ℝ) ≤ Real.exp (-(373097 / 500000 : ℝ)) ∧
    Real.exp (-(373097 / 500000 : ℝ)) ≤ (4741679 / 10000000 : ℝ) := by
  have hsmall : (5117962829 / 5000000000 : ℝ) ≤ Real.exp (373097 / 16000000 : ℝ) ∧
      Real.exp (373097 / 16000000 : ℝ) ≤ (10235925659 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (373097 / 16000000 : ℝ))
    (a := (5117962829 / 5000000000 : ℝ)) (b := (10235925659 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_245 :
    (24259 / 50000 : ℝ) ≤ Real.exp (-(7232353 / 10000000 : ℝ)) ∧
    Real.exp (-(7232353 / 10000000 : ℝ)) ≤ (4851801 / 10000000 : ℝ) := by
  have hsmall : (10228584431 / 10000000000 : ℝ) ≤ Real.exp (7232353 / 320000000 : ℝ) ∧
      Real.exp (7232353 / 320000000 : ℝ) ≤ (639286527 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7232353 / 320000000 : ℝ))
    (a := (10228584431 / 10000000000 : ℝ)) (b := (639286527 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_246 :
    (10624173 / 10000000 : ℝ) ≤ Real.exp (31 / 512 : ℝ) ∧
    Real.exp (31 / 512 : ℝ) ≤ (5312087 / 5000000 : ℝ) := by
  have hsmall : (50094694048761 / 50000000000000 : ℝ) ≤ Real.exp (31 / 16384 : ℝ) ∧
      Real.exp (31 / 16384 : ℝ) ≤ (100189388097523 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 16384 : ℝ))
    (a := (50094694048761 / 50000000000000 : ℝ)) (b := (100189388097523 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_247 :
    (490121 / 2000000 : ℝ) ≤ Real.exp (-(45 / 32 : ℝ)) ∧
    Real.exp (-(45 / 32 : ℝ)) ≤ (1225303 / 5000000 : ℝ) := by
  have hsmall : (10449252089 / 10000000000 : ℝ) ≤ Real.exp (45 / 1024 : ℝ) ∧
      Real.exp (45 / 1024 : ℝ) ≤ (1044925209 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (45 / 1024 : ℝ))
    (a := (10449252089 / 10000000000 : ℝ)) (b := (1044925209 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_248 :
    (4630683 / 10000000 : ℝ) ≤ Real.exp (-(7698807 / 10000000 : ℝ)) ∧
    Real.exp (-(7698807 / 10000000 : ℝ)) ≤ (1157671 / 2500000 : ℝ) := by
  have hsmall : (10243505191 / 10000000000 : ℝ) ≤ Real.exp (7698807 / 320000000 : ℝ) ∧
      Real.exp (7698807 / 320000000 : ℝ) ≤ (1280438149 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7698807 / 320000000 : ℝ))
    (a := (10243505191 / 10000000000 : ℝ)) (b := (1280438149 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_249 :
    (59271 / 125000 : ℝ) ≤ Real.exp (-(3730967 / 5000000 : ℝ)) ∧
    Real.exp (-(3730967 / 5000000 : ℝ)) ≤ (4741681 / 10000000 : ℝ) := by
  have hsmall : (5117962733 / 5000000000 : ℝ) ≤ Real.exp (3730967 / 160000000 : ℝ) ∧
      Real.exp (3730967 / 160000000 : ℝ) ≤ (10235925467 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3730967 / 160000000 : ℝ))
    (a := (5117962733 / 5000000000 : ℝ)) (b := (10235925467 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_250 :
    (5475361 / 5000000 : ℝ) ≤ Real.exp (93 / 1024 : ℝ) ∧
    Real.exp (93 / 1024 : ℝ) ≤ (10950723 / 10000000 : ℝ) := by
  have hsmall : (1002842166083 / 1000000000000 : ℝ) ≤ Real.exp (93 / 32768 : ℝ) ∧
      Real.exp (93 / 32768 : ℝ) ≤ (100284216608301 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 32768 : ℝ))
    (a := (1002842166083 / 1000000000000 : ℝ)) (b := (100284216608301 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_251 :
    (505679 / 2000000 : ℝ) ≤ Real.exp (-(11 / 8 : ℝ)) ∧
    Real.exp (-(11 / 8 : ℝ)) ≤ (632099 / 2500000 : ℝ) := by
  have hsmall : (10439052723 / 10000000000 : ℝ) ≤ Real.exp (11 / 256 : ℝ) ∧
      Real.exp (11 / 256 : ℝ) ≤ (2609763181 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11 / 256 : ℝ))
    (a := (10439052723 / 10000000000 : ℝ)) (b := (2609763181 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_252 :
    (4518887 / 10000000 : ℝ) ≤ Real.exp (-(992899 / 1250000 : ℝ)) ∧
    Real.exp (-(992899 / 1250000 : ℝ)) ≤ (564861 / 1250000 : ℝ) := by
  have hsmall : (1281416397 / 1250000000 : ℝ) ≤ Real.exp (992899 / 40000000 : ℝ) ∧
      Real.exp (992899 / 40000000 : ℝ) ≤ (10251331177 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (992899 / 40000000 : ℝ))
    (a := (1281416397 / 1250000000 : ℝ)) (b := (10251331177 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_253 :
    (926137 / 2000000 : ℝ) ≤ Real.exp (-(7698801 / 10000000 : ℝ)) ∧
    Real.exp (-(7698801 / 10000000 : ℝ)) ≤ (2315343 / 5000000 : ℝ) := by
  have hsmall : (10243504999 / 10000000000 : ℝ) ≤ Real.exp (7698801 / 320000000 : ℝ) ∧
      Real.exp (7698801 / 320000000 : ℝ) ≤ (2048701 / 2000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7698801 / 320000000 : ℝ))
    (a := (10243504999 / 10000000000 : ℝ)) (b := (2048701 / 2000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_254 :
    (11287307 / 10000000 : ℝ) ≤ Real.exp (31 / 256 : ℝ) ∧
    Real.exp (31 / 256 : ℝ) ≤ (2821827 / 2500000 : ℝ) := by
  have hsmall : (50189567436779 / 50000000000000 : ℝ) ≤ Real.exp (31 / 8192 : ℝ) ∧
      Real.exp (31 / 8192 : ℝ) ≤ (100379134873559 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 8192 : ℝ))
    (a := (50189567436779 / 50000000000000 : ℝ)) (b := (100379134873559 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_255 :
    (521731 / 2000000 : ℝ) ≤ Real.exp (-(43 / 32 : ℝ)) ∧
    Real.exp (-(43 / 32 : ℝ)) ≤ (163041 / 625000 : ℝ) := by
  have hsmall : (10428863311 / 10000000000 : ℝ) ≤ Real.exp (43 / 1024 : ℝ) ∧
      Real.exp (43 / 1024 : ℝ) ≤ (651803957 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (43 / 1024 : ℝ))
    (a := (10428863311 / 10000000000 : ℝ)) (b := (651803957 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_256 :
    (4406371 / 10000000 : ℝ) ≤ Real.exp (-(1024417 / 1250000 : ℝ)) ∧
    Real.exp (-(1024417 / 1250000 : ℝ)) ≤ (1101593 / 2500000 : ℝ) := by
  have hsmall : (2051882379 / 2000000000 : ℝ) ≤ Real.exp (1024417 / 40000000 : ℝ) ∧
      Real.exp (1024417 / 40000000 : ℝ) ≤ (1282426487 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1024417 / 40000000 : ℝ))
    (a := (2051882379 / 2000000000 : ℝ)) (b := (1282426487 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_257 :
    (451889 / 1000000 : ℝ) ≤ Real.exp (-(1588637 / 2000000 : ℝ)) ∧
    Real.exp (-(1588637 / 2000000 : ℝ)) ≤ (4518891 / 10000000 : ℝ) := by
  have hsmall : (10251330951 / 10000000000 : ℝ) ≤ Real.exp (1588637 / 64000000 : ℝ) ∧
      Real.exp (1588637 / 64000000 : ℝ) ≤ (1281416369 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1588637 / 64000000 : ℝ))
    (a := (10251330951 / 10000000000 : ℝ)) (b := (1281416369 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_258 :
    (11634237 / 10000000 : ℝ) ≤ Real.exp (155 / 1024 : ℝ) ∧
    Real.exp (155 / 1024 : ℝ) ≤ (5817119 / 5000000 : ℝ) := by
  have hsmall : (100474142978249 / 100000000000000 : ℝ) ≤ Real.exp (155 / 32768 : ℝ) ∧
      Real.exp (155 / 32768 : ℝ) ≤ (401896571913 / 400000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (155 / 32768 : ℝ))
    (a := (100474142978249 / 100000000000000 : ℝ)) (b := (401896571913 / 400000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_259 :
    (2691463 / 10000000 : ℝ) ≤ Real.exp (-(21 / 16 : ℝ)) ∧
    Real.exp (-(21 / 16 : ℝ)) ≤ (336433 / 1250000 : ℝ) := by
  have hsmall : (5209341923 / 5000000000 : ℝ) ≤ Real.exp (21 / 512 : ℝ) ∧
      Real.exp (21 / 512 : ℝ) ≤ (10418683847 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (21 / 512 : ℝ))
    (a := (5209341923 / 5000000000 : ℝ)) (b := (10418683847 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_260 :
    (2146609 / 5000000 : ℝ) ≤ Real.exp (-(1691097 / 2000000 : ℝ)) ∧
    Real.exp (-(1691097 / 2000000 : ℝ)) ≤ (4293219 / 10000000 : ℝ) := by
  have hsmall : (2566938959 / 2500000000 : ℝ) ≤ Real.exp (1691097 / 64000000 : ℝ) ∧
      Real.exp (1691097 / 64000000 : ℝ) ≤ (10267755837 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1691097 / 64000000 : ℝ))
    (a := (2566938959 / 2500000000 : ℝ)) (b := (10267755837 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_261 :
    (2203187 / 5000000 : ℝ) ≤ Real.exp (-(8195329 / 10000000 : ℝ)) ∧
    Real.exp (-(8195329 / 10000000 : ℝ)) ≤ (35251 / 80000 : ℝ) := by
  have hsmall : (10259411671 / 10000000000 : ℝ) ≤ Real.exp (8195329 / 320000000 : ℝ) ∧
      Real.exp (8195329 / 320000000 : ℝ) ≤ (1282426459 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8195329 / 320000000 : ℝ))
    (a := (10259411671 / 10000000000 : ℝ)) (b := (1282426459 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_262 :
    (11991831 / 10000000 : ℝ) ≤ Real.exp (93 / 512 : ℝ) ∧
    Real.exp (93 / 512 : ℝ) ≤ (1498979 / 1250000 : ℝ) := by
  have hsmall : (20113848201481 / 20000000000000 : ℝ) ≤ Real.exp (93 / 16384 : ℝ) ∧
      Real.exp (93 / 16384 : ℝ) ≤ (50284620503703 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 16384 : ℝ))
    (a := (20113848201481 / 20000000000000 : ℝ)) (b := (50284620503703 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_263 :
    (2776899 / 10000000 : ℝ) ≤ Real.exp (-(41 / 32 : ℝ)) ∧
    Real.exp (-(41 / 32 : ℝ)) ≤ (27769 / 100000 : ℝ) := by
  have hsmall : (2602128579 / 2500000000 : ℝ) ≤ Real.exp (41 / 1024 : ℝ) ∧
      Real.exp (41 / 1024 : ℝ) ≤ (10408514317 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (41 / 1024 : ℝ))
    (a := (2602128579 / 2500000000 : ℝ)) (b := (10408514317 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_264 :
    (2089759 / 5000000 : ℝ) ≤ Real.exp (-(872389 / 1000000 : ℝ)) ∧
    Real.exp (-(872389 / 1000000 : ℝ)) ≤ (4179519 / 10000000 : ℝ) := by
  have hsmall : (10276371689 / 10000000000 : ℝ) ≤ Real.exp (872389 / 32000000 : ℝ) ∧
      Real.exp (872389 / 32000000 : ℝ) ≤ (1027637169 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (872389 / 32000000 : ℝ))
    (a := (10276371689 / 10000000000 : ℝ)) (b := (1027637169 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_265 :
    (4293221 / 10000000 : ℝ) ≤ Real.exp (-(4227739 / 5000000 : ℝ)) ∧
    Real.exp (-(4227739 / 5000000 : ℝ)) ≤ (2146611 / 5000000 : ℝ) := by
  have hsmall : (10267755611 / 10000000000 : ℝ) ≤ Real.exp (4227739 / 160000000 : ℝ) ∧
      Real.exp (4227739 / 160000000 : ℝ) ≤ (2566938903 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4227739 / 160000000 : ℝ))
    (a := (10267755611 / 10000000000 : ℝ)) (b := (2566938903 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_266 :
    (386263 / 312500 : ℝ) ≤ Real.exp (217 / 1024 : ℝ) ∧
    Real.exp (217 / 1024 : ℝ) ≤ (12360417 / 10000000 : ℝ) := by
  have hsmall : (100664429046137 / 100000000000000 : ℝ) ≤ Real.exp (217 / 32768 : ℝ) ∧
      Real.exp (217 / 32768 : ℝ) ≤ (50332214523069 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (217 / 32768 : ℝ))
    (a := (100664429046137 / 100000000000000 : ℝ)) (b := (50332214523069 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_267 :
    (2865047 / 10000000 : ℝ) ≤ Real.exp (-(5 / 4 : ℝ)) ∧
    Real.exp (-(5 / 4 : ℝ)) ≤ (358131 / 1250000 : ℝ) := by
  have hsmall : (10398354713 / 10000000000 : ℝ) ≤ Real.exp (5 / 128 : ℝ) ∧
      Real.exp (5 / 128 : ℝ) ≤ (5199177357 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5 / 128 : ℝ))
    (a := (10398354713 / 10000000000 : ℝ)) (b := (5199177357 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_268 :
    (813073 / 2000000 : ℝ) ≤ Real.exp (-(1800163 / 2000000 : ℝ)) ∧
    Real.exp (-(1800163 / 2000000 : ℝ)) ≤ (2032683 / 5000000 : ℝ) := by
  have hsmall : (5142634307 / 5000000000 : ℝ) ≤ Real.exp (1800163 / 64000000 : ℝ) ∧
      Real.exp (1800163 / 64000000 : ℝ) ≤ (2057053723 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1800163 / 64000000 : ℝ))
    (a := (5142634307 / 5000000000 : ℝ)) (b := (2057053723 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_269 :
    (4179521 / 10000000 : ℝ) ≤ Real.exp (-(8723883 / 10000000 : ℝ)) ∧
    Real.exp (-(8723883 / 10000000 : ℝ)) ≤ (2089761 / 5000000 : ℝ) := by
  have hsmall : (1284546433 / 1250000000 : ℝ) ≤ Real.exp (8723883 / 320000000 : ℝ) ∧
      Real.exp (8723883 / 320000000 : ℝ) ≤ (2055274293 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8723883 / 320000000 : ℝ))
    (a := (1284546433 / 1250000000 : ℝ)) (b := (2055274293 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_270 :
    (1274033 / 1000000 : ℝ) ≤ Real.exp (31 / 128 : ℝ) ∧
    Real.exp (31 / 128 : ℝ) ≤ (12740331 / 10000000 : ℝ) := by
  have hsmall : (100759707179641 / 100000000000000 : ℝ) ≤ Real.exp (31 / 4096 : ℝ) ∧
      Real.exp (31 / 4096 : ℝ) ≤ (50379853589821 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 4096 : ℝ))
    (a := (100759707179641 / 100000000000000 : ℝ)) (b := (50379853589821 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_271 :
    (1477997 / 5000000 : ℝ) ≤ Real.exp (-(39 / 32 : ℝ)) ∧
    Real.exp (-(39 / 32 : ℝ)) ≤ (591199 / 2000000 : ℝ) := by
  have hsmall : (5194102513 / 5000000000 : ℝ) ≤ Real.exp (39 / 1024 : ℝ) ∧
      Real.exp (39 / 1024 : ℝ) ≤ (10388205027 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (39 / 1024 : ℝ))
    (a := (5194102513 / 5000000000 : ℝ)) (b := (10388205027 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_272 :
    (3950853 / 10000000 : ℝ) ≤ Real.exp (-(4643267 / 5000000 : ℝ)) ∧
    Real.exp (-(4643267 / 5000000 : ℝ)) ≤ (1975427 / 5000000 : ℝ) := by
  have hsmall : (5147228071 / 5000000000 : ℝ) ≤ Real.exp (4643267 / 160000000 : ℝ) ∧
      Real.exp (4643267 / 160000000 : ℝ) ≤ (10294456143 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4643267 / 160000000 : ℝ))
    (a := (5147228071 / 5000000000 : ℝ)) (b := (10294456143 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_273 :
    (508171 / 1250000 : ℝ) ≤ Real.exp (-(1125101 / 1250000 : ℝ)) ∧
    Real.exp (-(1125101 / 1250000 : ℝ)) ≤ (4065369 / 10000000 : ℝ) := by
  have hsmall : (10285268389 / 10000000000 : ℝ) ≤ Real.exp (1125101 / 40000000 : ℝ) ∧
      Real.exp (1125101 / 40000000 : ℝ) ≤ (1028526839 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1125101 / 40000000 : ℝ))
    (a := (10285268389 / 10000000000 : ℝ)) (b := (1028526839 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_274 :
    (13131921 / 10000000 : ℝ) ≤ Real.exp (279 / 1024 : ℝ) ∧
    Real.exp (279 / 1024 : ℝ) ≤ (6565961 / 5000000 : ℝ) := by
  have hsmall : (100855075493189 / 100000000000000 : ℝ) ≤ Real.exp (279 / 32768 : ℝ) ∧
      Real.exp (279 / 32768 : ℝ) ≤ (10085507549319 / 10000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (279 / 32768 : ℝ))
    (a := (100855075493189 / 100000000000000 : ℝ)) (b := (10085507549319 / 10000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_275 :
    (3049827 / 10000000 : ℝ) ≤ Real.exp (-(19 / 16 : ℝ)) ∧
    Real.exp (-(19 / 16 : ℝ)) ≤ (762457 / 2500000 : ℝ) := by
  have hsmall : (10378065247 / 10000000000 : ℝ) ≤ Real.exp (19 / 512 : ℝ) ∧
      Real.exp (19 / 512 : ℝ) ≤ (324314539 / 312500000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (19 / 512 : ℝ))
    (a := (10378065247 / 10000000000 : ℝ)) (b := (324314539 / 312500000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_276 :
    (479511 / 1250000 : ℝ) ≤ Real.exp (-(9581319 / 10000000 : ℝ)) ∧
    Real.exp (-(9581319 / 10000000 : ℝ)) ≤ (3836089 / 10000000 : ℝ) := by
  have hsmall : (10303943797 / 10000000000 : ℝ) ≤ Real.exp (9581319 / 320000000 : ℝ) ∧
      Real.exp (9581319 / 320000000 : ℝ) ≤ (5151971899 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9581319 / 320000000 : ℝ))
    (a := (10303943797 / 10000000000 : ℝ)) (b := (5151971899 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_277 :
    (493857 / 1250000 : ℝ) ≤ Real.exp (-(9286527 / 10000000 : ℝ)) ∧
    Real.exp (-(9286527 / 10000000 : ℝ)) ≤ (3950857 / 10000000 : ℝ) := by
  have hsmall : (10294455917 / 10000000000 : ℝ) ≤ Real.exp (9286527 / 320000000 : ℝ) ∧
      Real.exp (9286527 / 320000000 : ℝ) ≤ (5147227959 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9286527 / 320000000 : ℝ))
    (a := (10294455917 / 10000000000 : ℝ)) (b := (5147227959 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_278 :
    (3383887 / 2500000 : ℝ) ≤ Real.exp (155 / 512 : ℝ) ∧
    Real.exp (155 / 512 : ℝ) ≤ (13535549 / 10000000 : ℝ) := by
  have hsmall : (100950534072137 / 100000000000000 : ℝ) ≤ Real.exp (155 / 16384 : ℝ) ∧
      Real.exp (155 / 16384 : ℝ) ≤ (50475267036069 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (155 / 16384 : ℝ))
    (a := (100950534072137 / 100000000000000 : ℝ)) (b := (50475267036069 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_279 :
    (3146639 / 10000000 : ℝ) ≤ Real.exp (-(37 / 32 : ℝ)) ∧
    Real.exp (-(37 / 32 : ℝ)) ≤ (39333 / 125000 : ℝ) := by
  have hsmall : (2591983841 / 2500000000 : ℝ) ≤ Real.exp (37 / 1024 : ℝ) ∧
      Real.exp (37 / 1024 : ℝ) ≤ (2073587073 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (37 / 1024 : ℝ))
    (a := (2591983841 / 2500000000 : ℝ)) (b := (2073587073 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_280 :
    (930293 / 2500000 : ℝ) ≤ Real.exp (-(9885463 / 10000000 : ℝ)) ∧
    Real.exp (-(9885463 / 10000000 : ℝ)) ≤ (3721173 / 10000000 : ℝ) := by
  have hsmall : (2062748367 / 2000000000 : ℝ) ≤ Real.exp (9885463 / 320000000 : ℝ) ∧
      Real.exp (9885463 / 320000000 : ℝ) ≤ (2578435459 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9885463 / 320000000 : ℝ))
    (a := (2062748367 / 2000000000 : ℝ)) (b := (2578435459 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_281 :
    (3836091 / 10000000 : ℝ) ≤ Real.exp (-(74854 / 78125 : ℝ)) ∧
    Real.exp (-(74854 / 78125 : ℝ)) ≤ (959023 / 2500000 : ℝ) := by
  have hsmall : (10303943571 / 10000000000 : ℝ) ≤ Real.exp (37427 / 1250000 : ℝ) ∧
      Real.exp (37427 / 1250000 : ℝ) ≤ (2575985893 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (37427 / 1250000 : ℝ))
    (a := (10303943571 / 10000000000 : ℝ)) (b := (2575985893 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_282 :
    (13951581 / 10000000 : ℝ) ≤ Real.exp (341 / 1024 : ℝ) ∧
    Real.exp (341 / 1024 : ℝ) ≤ (6975791 / 5000000 : ℝ) := by
  have hsmall : (315769009381 / 312500000000 : ℝ) ≤ Real.exp (341 / 32768 : ℝ) ∧
      Real.exp (341 / 32768 : ℝ) ≤ (101046083001921 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (341 / 32768 : ℝ))
    (a := (315769009381 / 312500000000 : ℝ)) (b := (101046083001921 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_283 :
    (811631 / 2500000 : ℝ) ≤ Real.exp (-(9 / 8 : ℝ)) ∧
    Real.exp (-(9 / 8 : ℝ)) ≤ (129861 / 400000 : ℝ) := by
  have hsmall : (1035781537 / 1000000000 : ℝ) ≤ Real.exp (9 / 256 : ℝ) ∧
      Real.exp (9 / 256 : ℝ) ≤ (10357815371 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 256 : ℝ))
    (a := (1035781537 / 1000000000 : ℝ)) (b := (10357815371 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_284 :
    (721243 / 2000000 : ℝ) ≤ Real.exp (-(10199261 / 10000000 : ℝ)) ∧
    Real.exp (-(10199261 / 10000000 : ℝ)) ≤ (450777 / 1250000 : ℝ) := by
  have hsmall : (2064772129 / 2000000000 : ℝ) ≤ Real.exp (10199261 / 320000000 : ℝ) ∧
      Real.exp (10199261 / 320000000 : ℝ) ≤ (5161930323 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10199261 / 320000000 : ℝ))
    (a := (2064772129 / 2000000000 : ℝ)) (b := (5161930323 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_285 :
    (148847 / 400000 : ℝ) ≤ Real.exp (-(1977091 / 2000000 : ℝ)) ∧
    Real.exp (-(1977091 / 2000000 : ℝ)) ≤ (465147 / 1250000 : ℝ) := by
  have hsmall : (5156870789 / 5000000000 : ℝ) ≤ Real.exp (1977091 / 64000000 : ℝ) ∧
      Real.exp (1977091 / 64000000 : ℝ) ≤ (10313741579 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1977091 / 64000000 : ℝ))
    (a := (5156870789 / 5000000000 : ℝ)) (b := (10313741579 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_286 :
    (7190201 / 5000000 : ℝ) ≤ Real.exp (93 / 256 : ℝ) ∧
    Real.exp (93 / 256 : ℝ) ≤ (14380403 / 10000000 : ℝ) := by
  have hsmall : (20228344473611 / 20000000000000 : ℝ) ≤ Real.exp (93 / 8192 : ℝ) ∧
      Real.exp (93 / 8192 : ℝ) ≤ (12642715296007 / 12500000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 8192 : ℝ))
    (a := (20228344473611 / 20000000000000 : ℝ)) (b := (12642715296007 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_287 :
    (167479 / 500000 : ℝ) ≤ Real.exp (-(35 / 32 : ℝ)) ∧
    Real.exp (-(35 / 32 : ℝ)) ≤ (3349581 / 10000000 : ℝ) := by
  have hsmall : (10347705253 / 10000000000 : ℝ) ≤ Real.exp (35 / 1024 : ℝ) ∧
      Real.exp (35 / 1024 : ℝ) ≤ (5173852627 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (35 / 1024 : ℝ))
    (a := (10347705253 / 10000000000 : ℝ)) (b := (5173852627 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_288 :
    (349133 / 1000000 : ℝ) ≤ Real.exp (-(10523021 / 10000000 : ℝ)) ∧
    Real.exp (-(10523021 / 10000000 : ℝ)) ≤ (3491331 / 10000000 : ℝ) := by
  have hsmall : (1291788887 / 1250000000 : ℝ) ≤ Real.exp (10523021 / 320000000 : ℝ) ∧
      Real.exp (10523021 / 320000000 : ℝ) ≤ (10334311097 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10523021 / 320000000 : ℝ))
    (a := (1291788887 / 1250000000 : ℝ)) (b := (10334311097 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_289 :
    (1803109 / 5000000 : ℝ) ≤ Real.exp (-(10199253 / 10000000 : ℝ)) ∧
    Real.exp (-(10199253 / 10000000 : ℝ)) ≤ (3606219 / 10000000 : ℝ) := by
  have hsmall : (10323860387 / 10000000000 : ℝ) ≤ Real.exp (10199253 / 320000000 : ℝ) ∧
      Real.exp (10199253 / 320000000 : ℝ) ≤ (2580965097 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10199253 / 320000000 : ℝ))
    (a := (10323860387 / 10000000000 : ℝ)) (b := (2580965097 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_290 :
    (14822403 / 10000000 : ℝ) ≤ Real.exp (403 / 1024 : ℝ) ∧
    Real.exp (403 / 1024 : ℝ) ≤ (3705601 / 2500000 : ℝ) := by
  have hsmall : (50618726128069 / 50000000000000 : ℝ) ≤ Real.exp (403 / 32768 : ℝ) ∧
      Real.exp (403 / 32768 : ℝ) ≤ (101237452256139 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (403 / 32768 : ℝ))
    (a := (50618726128069 / 50000000000000 : ℝ)) (b := (101237452256139 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_291 :
    (3455907 / 10000000 : ℝ) ≤ Real.exp (-(17 / 16 : ℝ)) ∧
    Real.exp (-(17 / 16 : ℝ)) ≤ (863977 / 2500000 : ℝ) := by
  have hsmall : (2067521001 / 2000000000 : ℝ) ≤ Real.exp (17 / 512 : ℝ) ∧
      Real.exp (17 / 512 : ℝ) ≤ (5168802503 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 512 : ℝ))
    (a := (2067521001 / 2000000000 : ℝ)) (b := (5168802503 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_292 :
    (1688317 / 5000000 : ℝ) ≤ Real.exp (-(10857057 / 10000000 : ℝ)) ∧
    Real.exp (-(10857057 / 10000000 : ℝ)) ≤ (675327 / 2000000 : ℝ) := by
  have hsmall : (10345104329 / 10000000000 : ℝ) ≤ Real.exp (10857057 / 320000000 : ℝ) ∧
      Real.exp (10857057 / 320000000 : ℝ) ≤ (1034510433 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10857057 / 320000000 : ℝ))
    (a := (10345104329 / 10000000000 : ℝ)) (b := (1034510433 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_293 :
    (3491333 / 10000000 : ℝ) ≤ Real.exp (-(10523013 / 10000000 : ℝ)) ∧
    Real.exp (-(10523013 / 10000000 : ℝ)) ≤ (1745667 / 5000000 : ℝ) := by
  have hsmall : (5167155419 / 5000000000 : ℝ) ≤ Real.exp (10523013 / 320000000 : ℝ) ∧
      Real.exp (10523013 / 320000000 : ℝ) ≤ (10334310839 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10523013 / 320000000 : ℝ))
    (a := (5167155419 / 5000000000 : ℝ)) (b := (10334310839 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_294 :
    (15277989 / 10000000 : ℝ) ≤ Real.exp (217 / 512 : ℝ) ∧
    Real.exp (217 / 512 : ℝ) ≤ (1527799 / 1000000 : ℝ) := by
  have hsmall : (101333272751849 / 100000000000000 : ℝ) ≤ Real.exp (217 / 16384 : ℝ) ∧
      Real.exp (217 / 16384 : ℝ) ≤ (2026665455037 / 2000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (217 / 16384 : ℝ))
    (a := (101333272751849 / 100000000000000 : ℝ)) (b := (2026665455037 / 2000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_295 :
    (3565609 / 10000000 : ℝ) ≤ Real.exp (-(33 / 32 : ℝ)) ∧
    Real.exp (-(33 / 32 : ℝ)) ≤ (356561 / 1000000 : ℝ) := by
  have hsmall : (2065502923 / 2000000000 : ℝ) ≤ Real.exp (33 / 1024 : ℝ) ∧
      Real.exp (33 / 1024 : ℝ) ≤ (1290939327 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (33 / 1024 : ℝ))
    (a := (2065502923 / 2000000000 : ℝ)) (b := (1290939327 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_296 :
    (815561 / 2500000 : ℝ) ≤ Real.exp (-(350053 / 312500 : ℝ)) ∧
    Real.exp (-(350053 / 312500 : ℝ)) ≤ (652449 / 2000000 : ℝ) := by
  have hsmall : (414250079 / 400000000 : ℝ) ≤ Real.exp (350053 / 10000000 : ℝ) ∧
      Real.exp (350053 / 10000000 : ℝ) ≤ (1294531497 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (350053 / 10000000 : ℝ))
    (a := (414250079 / 400000000 : ℝ)) (b := (1294531497 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_297 :
    (844159 / 2500000 : ℝ) ≤ Real.exp (-(10857049 / 10000000 : ℝ)) ∧
    Real.exp (-(10857049 / 10000000 : ℝ)) ≤ (3376637 / 10000000 : ℝ) := by
  have hsmall : (1034510407 / 1000000000 : ℝ) ≤ Real.exp (10857049 / 320000000 : ℝ) ∧
      Real.exp (10857049 / 320000000 : ℝ) ≤ (10345104071 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10857049 / 320000000 : ℝ))
    (a := (1034510407 / 1000000000 : ℝ)) (b := (10345104071 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_298 :
    (15747579 / 10000000 : ℝ) ≤ Real.exp (465 / 1024 : ℝ) ∧
    Real.exp (465 / 1024 : ℝ) ≤ (787379 / 500000 : ℝ) := by
  have hsmall : (50714591970473 / 50000000000000 : ℝ) ≤ Real.exp (465 / 32768 : ℝ) ∧
      Real.exp (465 / 32768 : ℝ) ≤ (101429183940947 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (465 / 32768 : ℝ))
    (a := (50714591970473 / 50000000000000 : ℝ)) (b := (101429183940947 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_299 :
    (1839397 / 5000000 : ℝ) ≤ Real.exp (-(1 / 1 : ℝ)) ∧
    Real.exp (-(1 / 1 : ℝ)) ≤ (735759 / 2000000 : ℝ) := by
  have hsmall : (5158717037 / 5000000000 : ℝ) ≤ Real.exp (1 / 32 : ℝ) ∧
      Real.exp (1 / 32 : ℝ) ≤ (412697363 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 32 : ℝ))
    (a := (5158717037 / 5000000000 : ℝ)) (b := (412697363 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_300 :
    (3148283 / 10000000 : ℝ) ≤ Real.exp (-(11557277 / 10000000 : ℝ)) ∧
    Real.exp (-(11557277 / 10000000 : ℝ)) ≤ (787071 / 2500000 : ℝ) := by
  have hsmall : (5183883071 / 5000000000 : ℝ) ≤ Real.exp (11557277 / 320000000 : ℝ) ∧
      Real.exp (11557277 / 320000000 : ℝ) ≤ (10367766143 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11557277 / 320000000 : ℝ))
    (a := (5183883071 / 5000000000 : ℝ)) (b := (10367766143 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_301 :
    (3262247 / 10000000 : ℝ) ≤ Real.exp (-(1400211 / 1250000 : ℝ)) ∧
    Real.exp (-(1400211 / 1250000 : ℝ)) ≤ (407781 / 1250000 : ℝ) := by
  have hsmall : (10356251717 / 10000000000 : ℝ) ≤ Real.exp (1400211 / 40000000 : ℝ) ∧
      Real.exp (1400211 / 40000000 : ℝ) ≤ (5178125859 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1400211 / 40000000 : ℝ))
    (a := (10356251717 / 10000000000 : ℝ)) (b := (5178125859 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_302 :
    (8115801 / 5000000 : ℝ) ≤ Real.exp (31 / 64 : ℝ) ∧
    Real.exp (31 / 64 : ℝ) ≤ (16231603 / 10000000 : ℝ) := by
  have hsmall : (10152518590927 / 10000000000000 : ℝ) ≤ Real.exp (31 / 2048 : ℝ) ∧
      Real.exp (31 / 2048 : ℝ) ≤ (101525185909271 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 2048 : ℝ))
    (a := (10152518590927 / 10000000000000 : ℝ)) (b := (101525185909271 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_303 :
    (3795571 / 10000000 : ℝ) ≤ Real.exp (-(31 / 32 : ℝ)) ∧
    Real.exp (-(31 / 32 : ℝ)) ≤ (948893 / 2500000 : ℝ) := by
  have hsmall : (10307363373 / 10000000000 : ℝ) ≤ Real.exp (31 / 1024 : ℝ) ∧
      Real.exp (31 / 1024 : ℝ) ≤ (5153681687 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (31 / 1024 : ℝ))
    (a := (10307363373 / 10000000000 : ℝ)) (b := (5153681687 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_304 :
    (758719 / 2500000 : ℝ) ≤ Real.exp (-(11924143 / 10000000 : ℝ)) ∧
    Real.exp (-(11924143 / 10000000 : ℝ)) ≤ (3034877 / 10000000 : ℝ) := by
  have hsmall : (2594914787 / 2500000000 : ℝ) ≤ Real.exp (11924143 / 320000000 : ℝ) ∧
      Real.exp (11924143 / 320000000 : ℝ) ≤ (10379659149 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11924143 / 320000000 : ℝ))
    (a := (2594914787 / 2500000000 : ℝ)) (b := (10379659149 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_305 :
    (1574143 / 5000000 : ℝ) ≤ Real.exp (-(11557269 / 10000000 : ℝ)) ∧
    Real.exp (-(11557269 / 10000000 : ℝ)) ≤ (3148287 / 10000000 : ℝ) := by
  have hsmall : (5183882941 / 5000000000 : ℝ) ≤ Real.exp (11557269 / 320000000 : ℝ) ∧
      Real.exp (11557269 / 320000000 : ℝ) ≤ (10367765883 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11557269 / 320000000 : ℝ))
    (a := (5183882941 / 5000000000 : ℝ)) (b := (10367765883 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_306 :
    (1885257 / 2500000 : ℝ) ≤ Real.exp (-(289 / 1024 : ℝ)) ∧
    Real.exp (-(289 / 1024 : ℝ)) ≤ (7541029 / 10000000 : ℝ) := by
  have hsmall : (10088585871 / 10000000000 : ℝ) ≤ Real.exp (289 / 32768 : ℝ) ∧
      Real.exp (289 / 32768 : ℝ) ≤ (630536617 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (289 / 32768 : ℝ))
    (a := (10088585871 / 10000000000 : ℝ)) (b := (630536617 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_307 :
    (8365251 / 5000000 : ℝ) ≤ Real.exp (527 / 1024 : ℝ) ∧
    Real.exp (527 / 1024 : ℝ) ≤ (16730503 / 10000000 : ℝ) := by
  have hsmall : (12702659842843 / 12500000000000 : ℝ) ≤ Real.exp (527 / 32768 : ℝ) ∧
      Real.exp (527 / 32768 : ℝ) ≤ (20324255748549 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (527 / 32768 : ℝ))
    (a := (12702659842843 / 12500000000000 : ℝ)) (b := (20324255748549 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_308 :
    (489507 / 1250000 : ℝ) ≤ Real.exp (-(15 / 16 : ℝ)) ∧
    Real.exp (-(15 / 16 : ℝ)) ≤ (3916057 / 10000000 : ℝ) := by
  have hsmall : (5148651251 / 5000000000 : ℝ) ≤ Real.exp (15 / 512 : ℝ) ∧
      Real.exp (15 / 512 : ℝ) ≤ (10297302503 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15 / 512 : ℝ))
    (a := (5148651251 / 5000000000 : ℝ)) (b := (10297302503 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_309 :
    (730537 / 2500000 : ℝ) ≤ Real.exp (-(6151329 / 5000000 : ℝ)) ∧
    Real.exp (-(6151329 / 5000000 : ℝ)) ≤ (2922149 / 10000000 : ℝ) := by
  have hsmall : (10391944089 / 10000000000 : ℝ) ≤ Real.exp (6151329 / 160000000 : ℝ) ∧
      Real.exp (6151329 / 160000000 : ℝ) ≤ (1039194409 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6151329 / 160000000 : ℝ))
    (a := (10391944089 / 10000000000 : ℝ)) (b := (1039194409 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_310 :
    (3034879 / 10000000 : ℝ) ≤ Real.exp (-(2384827 / 2000000 : ℝ)) ∧
    Real.exp (-(2384827 / 2000000 : ℝ)) ≤ (4742 / 15625 : ℝ) := by
  have hsmall : (10379658889 / 10000000000 : ℝ) ≤ Real.exp (2384827 / 64000000 : ℝ) ∧
      Real.exp (2384827 / 64000000 : ℝ) ≤ (1037965889 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2384827 / 64000000 : ℝ))
    (a := (10379658889 / 10000000000 : ℝ)) (b := (1037965889 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_311 :
    (7287633 / 10000000 : ℝ) ≤ Real.exp (-(81 / 256 : ℝ)) ∧
    Real.exp (-(81 / 256 : ℝ)) ≤ (3643817 / 5000000 : ℝ) := by
  have hsmall : (50496837 / 50000000 : ℝ) ≤ Real.exp (81 / 8192 : ℝ) ∧
      Real.exp (81 / 8192 : ℝ) ≤ (10099367401 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (81 / 8192 : ℝ))
    (a := (50496837 / 50000000 : ℝ)) (b := (10099367401 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_312 :
    (269449 / 156250 : ℝ) ≤ Real.exp (279 / 512 : ℝ) ∧
    Real.exp (279 / 512 : ℝ) ≤ (17244737 / 10000000 : ℝ) := by
  have hsmall : (10171746252737 / 10000000000000 : ℝ) ≤ Real.exp (279 / 16384 : ℝ) ∧
      Real.exp (279 / 16384 : ℝ) ≤ (101717462527371 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (279 / 16384 : ℝ))
    (a := (10171746252737 / 10000000000000 : ℝ)) (b := (101717462527371 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_313 :
    (808073 / 2000000 : ℝ) ≤ Real.exp (-(29 / 32 : ℝ)) ∧
    Real.exp (-(29 / 32 : ℝ)) ≤ (2020183 / 5000000 : ℝ) := by
  have hsmall : (10287251451 / 10000000000 : ℝ) ≤ Real.exp (29 / 1024 : ℝ) ∧
      Real.exp (29 / 1024 : ℝ) ≤ (2571812863 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29 / 1024 : ℝ))
    (a := (10287251451 / 10000000000 : ℝ)) (b := (2571812863 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_314 :
    (281023 / 1000000 : ℝ) ≤ Real.exp (-(6346593 / 5000000 : ℝ)) ∧
    Real.exp (-(6346593 / 5000000 : ℝ)) ≤ (2810231 / 10000000 : ℝ) := by
  have hsmall : (130057927 / 125000000 : ℝ) ≤ Real.exp (6346593 / 160000000 : ℝ) ∧
      Real.exp (6346593 / 160000000 : ℝ) ≤ (10404634161 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6346593 / 160000000 : ℝ))
    (a := (130057927 / 125000000 : ℝ)) (b := (10404634161 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_315 :
    (2922151 / 10000000 : ℝ) ≤ Real.exp (-(246053 / 200000 : ℝ)) ∧
    Real.exp (-(246053 / 200000 : ℝ)) ≤ (365269 / 1250000 : ℝ) := by
  have hsmall : (1039194383 / 1000000000 : ℝ) ≤ Real.exp (246053 / 6400000 : ℝ) ∧
      Real.exp (246053 / 6400000 : ℝ) ≤ (10391943831 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (246053 / 6400000 : ℝ))
    (a := (1039194383 / 1000000000 : ℝ)) (b := (10391943831 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_316 :
    (7029011 / 10000000 : ℝ) ≤ Real.exp (-(361 / 1024 : ℝ)) ∧
    Real.exp (-(361 / 1024 : ℝ)) ≤ (1757253 / 2500000 : ℝ) := by
  have hsmall : (5055388773 / 5000000000 : ℝ) ≤ Real.exp (361 / 32768 : ℝ) ∧
      Real.exp (361 / 32768 : ℝ) ≤ (10110777547 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (361 / 32768 : ℝ))
    (a := (5055388773 / 5000000000 : ℝ)) (b := (10110777547 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_317 :
    (2221847 / 1250000 : ℝ) ≤ Real.exp (589 / 1024 : ℝ) ∧
    Real.exp (589 / 1024 : ℝ) ≤ (17774777 / 10000000 : ℝ) := by
  have hsmall : (6363358584327 / 6250000000000 : ℝ) ≤ Real.exp (589 / 32768 : ℝ) ∧
      Real.exp (589 / 32768 : ℝ) ≤ (101813737349233 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (589 / 32768 : ℝ))
    (a := (6363358584327 / 6250000000000 : ℝ)) (b := (101813737349233 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_318 :
    (208431 / 500000 : ℝ) ≤ Real.exp (-(7 / 8 : ℝ)) ∧
    Real.exp (-(7 / 8 : ℝ)) ≤ (4168621 / 10000000 : ℝ) := by
  have hsmall : (10277210211 / 10000000000 : ℝ) ≤ Real.exp (7 / 256 : ℝ) ∧
      Real.exp (7 / 256 : ℝ) ≤ (2569302553 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7 / 256 : ℝ))
    (a := (10277210211 / 10000000000 : ℝ)) (b := (2569302553 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_319 :
    (10797 / 40000 : ℝ) ≤ Real.exp (-(13096111 / 10000000 : ℝ)) ∧
    Real.exp (-(13096111 / 10000000 : ℝ)) ≤ (2699251 / 10000000 : ℝ) := by
  have hsmall : (10417743309 / 10000000000 : ℝ) ≤ Real.exp (13096111 / 320000000 : ℝ) ∧
      Real.exp (13096111 / 320000000 : ℝ) ≤ (1041774331 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13096111 / 320000000 : ℝ))
    (a := (10417743309 / 10000000000 : ℝ)) (b := (1041774331 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_320 :
    (351279 / 1250000 : ℝ) ≤ Real.exp (-(6346589 / 5000000 : ℝ)) ∧
    Real.exp (-(6346589 / 5000000 : ℝ)) ≤ (2810233 / 10000000 : ℝ) := by
  have hsmall : (104046339 / 100000000 : ℝ) ≤ Real.exp (6346589 / 160000000 : ℝ) ∧
      Real.exp (6346589 / 160000000 : ℝ) ≤ (10404633901 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6346589 / 160000000 : ℝ))
    (a := (104046339 / 100000000 : ℝ)) (b := (10404633901 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_321 :
    (3383169 / 5000000 : ℝ) ≤ Real.exp (-(25 / 64 : ℝ)) ∧
    Real.exp (-(25 / 64 : ℝ)) ≤ (6766339 / 10000000 : ℝ) := by
  have hsmall : (10122818411 / 10000000000 : ℝ) ≤ Real.exp (25 / 2048 : ℝ) ∧
      Real.exp (25 / 2048 : ℝ) ≤ (2530704603 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 2048 : ℝ))
    (a := (10122818411 / 10000000000 : ℝ)) (b := (2530704603 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_322 :
    (4580277 / 2500000 : ℝ) ≤ Real.exp (155 / 256 : ℝ) ∧
    Real.exp (155 / 256 : ℝ) ≤ (18321109 / 10000000 : ℝ) := by
  have hsmall : (50955051647249 / 50000000000000 : ℝ) ≤ Real.exp (155 / 8192 : ℝ) ∧
      Real.exp (155 / 8192 : ℝ) ≤ (101910103294499 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (155 / 8192 : ℝ))
    (a := (50955051647249 / 50000000000000 : ℝ)) (b := (101910103294499 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_323 :
    (2150473 / 5000000 : ℝ) ≤ Real.exp (-(27 / 32 : ℝ)) ∧
    Real.exp (-(27 / 32 : ℝ)) ≤ (4300947 / 10000000 : ℝ) := by
  have hsmall : (2566794693 / 2500000000 : ℝ) ≤ Real.exp (27 / 1024 : ℝ) ∧
      Real.exp (27 / 1024 : ℝ) ≤ (10267178773 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (27 / 1024 : ℝ))
    (a := (2566794693 / 2500000000 : ℝ)) (b := (10267178773 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_324 :
    (1294669 / 5000000 : ℝ) ≤ Real.exp (-(540473 / 400000 : ℝ)) ∧
    Real.exp (-(540473 / 400000 : ℝ)) ≤ (2589339 / 10000000 : ℝ) := by
  have hsmall : (10431285859 / 10000000000 : ℝ) ≤ Real.exp (540473 / 12800000 : ℝ) ∧
      Real.exp (540473 / 12800000 : ℝ) ≤ (521564293 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (540473 / 12800000 : ℝ))
    (a := (10431285859 / 10000000000 : ℝ)) (b := (521564293 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_325 :
    (674813 / 2500000 : ℝ) ≤ Real.exp (-(13096103 / 10000000 : ℝ)) ∧
    Real.exp (-(13096103 / 10000000 : ℝ)) ≤ (2699253 / 10000000 : ℝ) := by
  have hsmall : (1302217881 / 1250000000 : ℝ) ≤ Real.exp (13096103 / 320000000 : ℝ) ∧
      Real.exp (13096103 / 320000000 : ℝ) ≤ (10417743049 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13096103 / 320000000 : ℝ))
    (a := (1302217881 / 1250000000 : ℝ)) (b := (10417743049 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_326 :
    (1625193 / 2500000 : ℝ) ≤ Real.exp (-(441 / 1024 : ℝ)) ∧
    Real.exp (-(441 / 1024 : ℝ)) ≤ (6500773 / 10000000 : ℝ) := by
  have hsmall : (5067746109 / 5000000000 : ℝ) ≤ Real.exp (441 / 32768 : ℝ) ∧
      Real.exp (441 / 32768 : ℝ) ≤ (10135492219 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (441 / 32768 : ℝ))
    (a := (5067746109 / 5000000000 : ℝ)) (b := (10135492219 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_327 :
    (18884231 / 10000000 : ℝ) ≤ Real.exp (651 / 1024 : ℝ) ∧
    Real.exp (651 / 1024 : ℝ) ≤ (2360529 / 1250000 : ℝ) := by
  have hsmall : (51003280224707 / 50000000000000 : ℝ) ≤ Real.exp (651 / 32768 : ℝ) ∧
      Real.exp (651 / 32768 : ℝ) ≤ (20401312089883 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (651 / 32768 : ℝ))
    (a := (51003280224707 / 50000000000000 : ℝ)) (b := (20401312089883 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_328 :
    (4437473 / 10000000 : ℝ) ≤ Real.exp (-(13 / 16 : ℝ)) ∧
    Real.exp (-(13 / 16 : ℝ)) ≤ (2218737 / 5000000 : ℝ) := by
  have hsmall : (2564289281 / 2500000000 : ℝ) ≤ Real.exp (13 / 512 : ℝ) ∧
      Real.exp (13 / 512 : ℝ) ≤ (82057257 / 80000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13 / 512 : ℝ))
    (a := (2564289281 / 2500000000 : ℝ)) (b := (82057257 / 80000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_329 :
    (1240313 / 5000000 : ℝ) ≤ Real.exp (-(6970369 / 5000000 : ℝ)) ∧
    Real.exp (-(6970369 / 5000000 : ℝ)) ≤ (2480627 / 10000000 : ℝ) := by
  have hsmall : (261131921 / 250000000 : ℝ) ≤ Real.exp (6970369 / 160000000 : ℝ) ∧
      Real.exp (6970369 / 160000000 : ℝ) ≤ (10445276841 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6970369 / 160000000 : ℝ))
    (a := (261131921 / 250000000 : ℝ)) (b := (10445276841 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_330 :
    (129467 / 500000 : ℝ) ≤ Real.exp (-(13511817 / 10000000 : ℝ)) ∧
    Real.exp (-(13511817 / 10000000 : ℝ)) ≤ (2589341 / 10000000 : ℝ) := by
  have hsmall : (5215642799 / 5000000000 : ℝ) ≤ Real.exp (13511817 / 320000000 : ℝ) ∧
      Real.exp (13511817 / 320000000 : ℝ) ≤ (10431285599 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13511817 / 320000000 : ℝ))
    (a := (5215642799 / 5000000000 : ℝ)) (b := (10431285599 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_331 :
    (6233443 / 10000000 : ℝ) ≤ Real.exp (-(121 / 256 : ℝ)) ∧
    Real.exp (-(121 / 256 : ℝ)) ≤ (1558361 / 2500000 : ℝ) := by
  have hsmall : (2537200327 / 2500000000 : ℝ) ≤ Real.exp (121 / 8192 : ℝ) ∧
      Real.exp (121 / 8192 : ℝ) ≤ (10148801309 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (121 / 8192 : ℝ))
    (a := (2537200327 / 2500000000 : ℝ)) (b := (10148801309 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_332 :
    (19464663 / 10000000 : ℝ) ≤ Real.exp (341 / 512 : ℝ) ∧
    Real.exp (341 / 512 : ℝ) ≤ (2433083 / 1250000 : ℝ) := by
  have hsmall : (10210310890031 / 10000000000000 : ℝ) ≤ Real.exp (341 / 16384 : ℝ) ∧
      Real.exp (341 / 16384 : ℝ) ≤ (102103108900311 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (341 / 16384 : ℝ))
    (a := (10210310890031 / 10000000000000 : ℝ)) (b := (102103108900311 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_333 :
    (4578333 / 10000000 : ℝ) ≤ Real.exp (-(25 / 32 : ℝ)) ∧
    Real.exp (-(25 / 32 : ℝ)) ≤ (2289167 / 5000000 : ℝ) := by
  have hsmall : (10247145259 / 10000000000 : ℝ) ≤ Real.exp (25 / 1024 : ℝ) ∧
      Real.exp (25 / 1024 : ℝ) ≤ (512357263 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 1024 : ℝ))
    (a := (10247145259 / 10000000000 : ℝ)) (b := (512357263 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_334 :
    (1186623 / 5000000 : ℝ) ≤ Real.exp (-(14383263 / 10000000 : ℝ)) ∧
    Real.exp (-(14383263 / 10000000 : ℝ)) ≤ (2373247 / 10000000 : ℝ) := by
  have hsmall : (2614932877 / 2500000000 : ℝ) ≤ Real.exp (14383263 / 320000000 : ℝ) ∧
      Real.exp (14383263 / 320000000 : ℝ) ≤ (10459731509 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (14383263 / 320000000 : ℝ))
    (a := (2614932877 / 2500000000 : ℝ)) (b := (10459731509 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_335 :
    (2480629 / 10000000 : ℝ) ≤ Real.exp (-(13940729 / 10000000 : ℝ)) ∧
    Real.exp (-(13940729 / 10000000 : ℝ)) ≤ (248063 / 1000000 : ℝ) := by
  have hsmall : (5222638273 / 5000000000 : ℝ) ≤ Real.exp (13940729 / 320000000 : ℝ) ∧
      Real.exp (13940729 / 320000000 : ℝ) ≤ (10445276547 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13940729 / 320000000 : ℝ))
    (a := (5222638273 / 5000000000 : ℝ)) (b := (10445276547 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_336 :
    (1491361 / 2500000 : ℝ) ≤ Real.exp (-(529 / 1024 : ℝ)) ∧
    Real.exp (-(529 / 1024 : ℝ)) ≤ (1193089 / 2000000 : ℝ) := by
  have hsmall : (508137407 / 500000000 : ℝ) ≤ Real.exp (529 / 32768 : ℝ) ∧
      Real.exp (529 / 32768 : ℝ) ≤ (10162748141 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (529 / 32768 : ℝ))
    (a := (508137407 / 500000000 : ℝ)) (b := (10162748141 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_337 :
    (2507867 / 1250000 : ℝ) ≤ Real.exp (713 / 1024 : ℝ) ∧
    Real.exp (713 / 1024 : ℝ) ≤ (20062937 / 10000000 : ℝ) := by
  have hsmall : (102199748733597 / 100000000000000 : ℝ) ≤ Real.exp (713 / 32768 : ℝ) ∧
      Real.exp (713 / 32768 : ℝ) ≤ (51099874366799 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (713 / 32768 : ℝ))
    (a := (102199748733597 / 100000000000000 : ℝ)) (b := (51099874366799 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_338 :
    (944733 / 2000000 : ℝ) ≤ Real.exp (-(3 / 4 : ℝ)) ∧
    Real.exp (-(3 / 4 : ℝ)) ≤ (2361833 / 5000000 : ℝ) := by
  have hsmall : (5118571583 / 5000000000 : ℝ) ≤ Real.exp (3 / 128 : ℝ) ∧
      Real.exp (3 / 128 : ℝ) ≤ (10237143167 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3 / 128 : ℝ))
    (a := (5118571583 / 5000000000 : ℝ)) (b := (10237143167 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_339 :
    (1133663 / 5000000 : ℝ) ≤ Real.exp (-(14839837 / 10000000 : ℝ)) ∧
    Real.exp (-(14839837 / 10000000 : ℝ)) ≤ (2267327 / 10000000 : ℝ) := by
  have hsmall : (10474666039 / 10000000000 : ℝ) ≤ Real.exp (14839837 / 320000000 : ℝ) ∧
      Real.exp (14839837 / 320000000 : ℝ) ≤ (261866651 / 250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (14839837 / 320000000 : ℝ))
    (a := (10474666039 / 10000000000 : ℝ)) (b := (261866651 / 250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_340 :
    (18541 / 78125 : ℝ) ≤ Real.exp (-(7191627 / 5000000 : ℝ)) ∧
    Real.exp (-(7191627 / 5000000 : ℝ)) ≤ (2373249 / 10000000 : ℝ) := by
  have hsmall : (10459731213 / 10000000000 : ℝ) ≤ Real.exp (7191627 / 160000000 : ℝ) ∧
      Real.exp (7191627 / 160000000 : ℝ) ≤ (5229865607 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7191627 / 160000000 : ℝ))
    (a := (10459731213 / 10000000000 : ℝ)) (b := (5229865607 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_341 :
    (1424457 / 2500000 : ℝ) ≤ Real.exp (-(9 / 16 : ℝ)) ∧
    Real.exp (-(9 / 16 : ℝ)) ≤ (5697829 / 10000000 : ℝ) := by
  have hsmall : (5088667647 / 5000000000 : ℝ) ≤ Real.exp (9 / 512 : ℝ) ∧
      Real.exp (9 / 512 : ℝ) ≤ (2035467059 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 512 : ℝ))
    (a := (5088667647 / 5000000000 : ℝ)) (b := (2035467059 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_342 :
    (20679597 / 10000000 : ℝ) ≤ Real.exp (93 / 128 : ℝ) ∧
    Real.exp (93 / 128 : ℝ) ≤ (10339799 / 5000000 : ℝ) := by
  have hsmall : (12787060004471 / 12500000000000 : ℝ) ≤ Real.exp (93 / 4096 : ℝ) ∧
      Real.exp (93 / 4096 : ℝ) ≤ (102296480035769 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 4096 : ℝ))
    (a := (12787060004471 / 12500000000000 : ℝ)) (b := (102296480035769 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_343 :
    (487361 / 1000000 : ℝ) ≤ Real.exp (-(23 / 32 : ℝ)) ∧
    Real.exp (-(23 / 32 : ℝ)) ≤ (4873611 / 10000000 : ℝ) := by
  have hsmall : (2045430167 / 2000000000 : ℝ) ≤ Real.exp (23 / 1024 : ℝ) ∧
      Real.exp (23 / 1024 : ℝ) ≤ (2556787709 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (23 / 1024 : ℝ))
    (a := (2045430167 / 2000000000 : ℝ)) (b := (2556787709 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_344 :
    (2162997 / 10000000 : ℝ) ≤ Real.exp (-(15310903 / 10000000 : ℝ)) ∧
    Real.exp (-(15310903 / 10000000 : ℝ)) ≤ (1081499 / 5000000 : ℝ) := by
  have hsmall : (10490096953 / 10000000000 : ℝ) ≤ Real.exp (15310903 / 320000000 : ℝ) ∧
      Real.exp (15310903 / 320000000 : ℝ) ≤ (5245048477 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15310903 / 320000000 : ℝ))
    (a := (10490096953 / 10000000000 : ℝ)) (b := (5245048477 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_345 :
    (35427 / 156250 : ℝ) ≤ Real.exp (-(3709957 / 2500000 : ℝ)) ∧
    Real.exp (-(3709957 / 2500000 : ℝ)) ≤ (2267329 / 10000000 : ℝ) := by
  have hsmall : (654666609 / 625000000 : ℝ) ≤ Real.exp (3709957 / 80000000 : ℝ) ∧
      Real.exp (3709957 / 80000000 : ℝ) ≤ (2094933149 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3709957 / 80000000 : ℝ))
    (a := (654666609 / 625000000 : ℝ)) (b := (2094933149 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_346 :
    (2715799 / 5000000 : ℝ) ≤ Real.exp (-(625 / 1024 : ℝ)) ∧
    Real.exp (-(625 / 1024 : ℝ)) ≤ (5431599 / 10000000 : ℝ) := by
  have hsmall : (318517671 / 312500000 : ℝ) ≤ Real.exp (625 / 32768 : ℝ) ∧
      Real.exp (625 / 32768 : ℝ) ≤ (10192565473 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (625 / 32768 : ℝ))
    (a := (318517671 / 312500000 : ℝ)) (b := (10192565473 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_347 :
    (5328803 / 2500000 : ℝ) ≤ Real.exp (775 / 1024 : ℝ) ∧
    Real.exp (775 / 1024 : ℝ) ≤ (21315213 / 10000000 : ℝ) := by
  have hsmall : (25598325723349 / 25000000000000 : ℝ) ≤ Real.exp (775 / 32768 : ℝ) ∧
      Real.exp (775 / 32768 : ℝ) ≤ (102393302893397 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (775 / 32768 : ℝ))
    (a := (25598325723349 / 25000000000000 : ℝ)) (b := (102393302893397 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_348 :
    (1005663 / 2000000 : ℝ) ≤ Real.exp (-(11 / 16 : ℝ)) ∧
    Real.exp (-(11 / 16 : ℝ)) ≤ (1257079 / 2500000 : ℝ) := by
  have hsmall : (5108584129 / 5000000000 : ℝ) ≤ Real.exp (11 / 512 : ℝ) ∧
      Real.exp (11 / 512 : ℝ) ≤ (10217168259 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11 / 512 : ℝ))
    (a := (5108584129 / 5000000000 : ℝ)) (b := (10217168259 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_349 :
    (64387 / 312500 : ℝ) ≤ Real.exp (-(15796923 / 10000000 : ℝ)) ∧
    Real.exp (-(15796923 / 10000000 : ℝ)) ≤ (412077 / 2000000 : ℝ) := by
  have hsmall : (10506041549 / 10000000000 : ℝ) ≤ Real.exp (15796923 / 320000000 : ℝ) ∧
      Real.exp (15796923 / 320000000 : ℝ) ≤ (210120831 / 200000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15796923 / 320000000 : ℝ))
    (a := (10506041549 / 10000000000 : ℝ)) (b := (210120831 / 200000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_350 :
    (2162999 / 10000000 : ℝ) ≤ Real.exp (-(7655447 / 5000000 : ℝ)) ∧
    Real.exp (-(7655447 / 5000000 : ℝ)) ≤ (2163 / 10000 : ℝ) := by
  have hsmall : (5245048329 / 5000000000 : ℝ) ≤ Real.exp (7655447 / 160000000 : ℝ) ∧
      Real.exp (7655447 / 160000000 : ℝ) ≤ (10490096659 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7655447 / 160000000 : ℝ))
    (a := (5245048329 / 5000000000 : ℝ)) (b := (10490096659 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_351 :
    (1033541 / 2000000 : ℝ) ≤ Real.exp (-(169 / 256 : ℝ)) ∧
    Real.exp (-(169 / 256 : ℝ)) ≤ (2583853 / 5000000 : ℝ) := by
  have hsmall : (10208441497 / 10000000000 : ℝ) ≤ Real.exp (169 / 8192 : ℝ) ∧
      Real.exp (169 / 8192 : ℝ) ≤ (5104220749 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (169 / 8192 : ℝ))
    (a := (10208441497 / 10000000000 : ℝ)) (b := (5104220749 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_352 :
    (5492591 / 2500000 : ℝ) ≤ Real.exp (403 / 512 : ℝ) ∧
    Real.exp (403 / 512 : ℝ) ≤ (4394073 / 2000000 : ℝ) := by
  have hsmall : (102490217393139 / 100000000000000 : ℝ) ≤ Real.exp (403 / 16384 : ℝ) ∧
      Real.exp (403 / 16384 : ℝ) ≤ (5124510869657 / 5000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (403 / 16384 : ℝ))
    (a := (102490217393139 / 100000000000000 : ℝ)) (b := (5124510869657 / 5000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_353 :
    (5187931 / 10000000 : ℝ) ≤ Real.exp (-(21 / 32 : ℝ)) ∧
    Real.exp (-(21 / 32 : ℝ)) ≤ (1296983 / 2500000 : ℝ) := by
  have hsmall : (408287817 / 400000000 : ℝ) ≤ Real.exp (21 / 1024 : ℝ) ∧
      Real.exp (21 / 1024 : ℝ) ≤ (5103597713 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (21 / 1024 : ℝ))
    (a := (408287817 / 400000000 : ℝ)) (b := (5103597713 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_354 :
    (979807 / 5000000 : ℝ) ≤ Real.exp (-(16298371 / 10000000 : ℝ)) ∧
    Real.exp (-(16298371 / 10000000 : ℝ)) ≤ (391923 / 2000000 : ℝ) := by
  have hsmall : (2104503537 / 2000000000 : ℝ) ≤ Real.exp (16298371 / 320000000 : ℝ) ∧
      Real.exp (16298371 / 320000000 : ℝ) ≤ (5261258843 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (16298371 / 320000000 : ℝ))
    (a := (2104503537 / 2000000000 : ℝ)) (b := (5261258843 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_355 :
    (1030193 / 5000000 : ℝ) ≤ Real.exp (-(7898457 / 5000000 : ℝ)) ∧
    Real.exp (-(7898457 / 5000000 : ℝ)) ≤ (2060387 / 10000000 : ℝ) := by
  have hsmall : (5253020627 / 5000000000 : ℝ) ≤ Real.exp (7898457 / 160000000 : ℝ) ∧
      Real.exp (7898457 / 160000000 : ℝ) ≤ (2101208251 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7898457 / 160000000 : ℝ))
    (a := (5253020627 / 5000000000 : ℝ)) (b := (2101208251 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_356 :
    (30669 / 62500 : ℝ) ≤ Real.exp (-(729 / 1024 : ℝ)) ∧
    Real.exp (-(729 / 1024 : ℝ)) ≤ (4907041 / 10000000 : ℝ) := by
  have hsmall : (10224966313 / 10000000000 : ℝ) ≤ Real.exp (729 / 32768 : ℝ) ∧
      Real.exp (729 / 32768 : ℝ) ≤ (5112483157 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (729 / 32768 : ℝ))
    (a := (10224966313 / 10000000000 : ℝ)) (b := (5112483157 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_357 :
    (5661413 / 2500000 : ℝ) ≤ Real.exp (837 / 1024 : ℝ) ∧
    Real.exp (837 / 1024 : ℝ) ≤ (22645653 / 10000000 : ℝ) := by
  have hsmall : (12823402952717 / 12500000000000 : ℝ) ≤ Real.exp (837 / 32768 : ℝ) ∧
      Real.exp (837 / 32768 : ℝ) ≤ (102587223621737 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (837 / 32768 : ℝ))
    (a := (12823402952717 / 12500000000000 : ℝ)) (b := (102587223621737 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_358 :
    (2676307 / 5000000 : ℝ) ≤ Real.exp (-(5 / 8 : ℝ)) ∧
    Real.exp (-(5 / 8 : ℝ)) ≤ (1070523 / 2000000 : ℝ) := by
  have hsmall : (10197232327 / 10000000000 : ℝ) ≤ Real.exp (5 / 256 : ℝ) ∧
      Real.exp (5 / 256 : ℝ) ≤ (1274654041 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5 / 256 : ℝ))
    (a := (10197232327 / 10000000000 : ℝ)) (b := (1274654041 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_359 :
    (232601 / 1250000 : ℝ) ≤ Real.exp (-(8407869 / 5000000 : ℝ)) ∧
    Real.exp (-(8407869 / 5000000 : ℝ)) ≤ (1860809 / 10000000 : ℝ) := by
  have hsmall : (2107908791 / 2000000000 : ℝ) ≤ Real.exp (8407869 / 160000000 : ℝ) ∧
      Real.exp (8407869 / 160000000 : ℝ) ≤ (2634885989 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8407869 / 160000000 : ℝ))
    (a := (2107908791 / 2000000000 : ℝ)) (b := (2634885989 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_360 :
    (30619 / 156250 : ℝ) ≤ Real.exp (-(8149181 / 5000000 : ℝ)) ∧
    Real.exp (-(8149181 / 5000000 : ℝ)) ≤ (1959617 / 10000000 : ℝ) := by
  have hsmall : (10522517389 / 10000000000 : ℝ) ≤ Real.exp (8149181 / 160000000 : ℝ) ∧
      Real.exp (8149181 / 160000000 : ℝ) ≤ (1052251739 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8149181 / 160000000 : ℝ))
    (a := (10522517389 / 10000000000 : ℝ)) (b := (1052251739 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_361 :
    (4650431 / 10000000 : ℝ) ≤ Real.exp (-(49 / 64 : ℝ)) ∧
    Real.exp (-(49 / 64 : ℝ)) ≤ (72663 / 156250 : ℝ) := by
  have hsmall : (10242142991 / 10000000000 : ℝ) ≤ Real.exp (49 / 2048 : ℝ) ∧
      Real.exp (49 / 2048 : ℝ) ≤ (640133937 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 2048 : ℝ))
    (a := (10242142991 / 10000000000 : ℝ)) (b := (640133937 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_362 :
    (23341697 / 10000000 : ℝ) ≤ Real.exp (217 / 256 : ℝ) ∧
    Real.exp (217 / 256 : ℝ) ≤ (11670849 / 5000000 : ℝ) := by
  have hsmall : (51342160833003 / 50000000000000 : ℝ) ≤ Real.exp (217 / 8192 : ℝ) ∧
      Real.exp (217 / 8192 : ℝ) ≤ (102684321666007 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (217 / 8192 : ℝ))
    (a := (51342160833003 / 50000000000000 : ℝ)) (b := (102684321666007 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_363 :
    (1380631 / 2500000 : ℝ) ≤ Real.exp (-(19 / 32 : ℝ)) ∧
    Real.exp (-(19 / 32 : ℝ)) ≤ (220901 / 400000 : ℝ) := by
  have hsmall : (10187278953 / 10000000000 : ℝ) ≤ Real.exp (19 / 1024 : ℝ) ∧
      Real.exp (19 / 1024 : ℝ) ≤ (5093639477 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (19 / 1024 : ℝ))
    (a := (10187278953 / 10000000000 : ℝ)) (b := (5093639477 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_364 :
    (352817 / 2000000 : ℝ) ≤ Real.exp (-(8674763 / 5000000 : ℝ)) ∧
    Real.exp (-(8674763 / 5000000 : ℝ)) ≤ (882043 / 5000000 : ℝ) := by
  have hsmall : (2639284877 / 2500000000 : ℝ) ≤ Real.exp (8674763 / 160000000 : ℝ) ∧
      Real.exp (8674763 / 160000000 : ℝ) ≤ (10557139509 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8674763 / 160000000 : ℝ))
    (a := (2639284877 / 2500000000 : ℝ)) (b := (10557139509 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_365 :
    (186081 / 1000000 : ℝ) ≤ Real.exp (-(16815729 / 10000000 : ℝ)) ∧
    Real.exp (-(16815729 / 10000000 : ℝ)) ≤ (1860811 / 10000000 : ℝ) := by
  have hsmall : (10539543659 / 10000000000 : ℝ) ≤ Real.exp (16815729 / 320000000 : ℝ) ∧
      Real.exp (16815729 / 320000000 : ℝ) ≤ (526977183 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (16815729 / 320000000 : ℝ))
    (a := (10539543659 / 10000000000 : ℝ)) (b := (526977183 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_366 :
    (2199321 / 5000000 : ℝ) ≤ Real.exp (-(841 / 1024 : ℝ)) ∧
    Real.exp (-(841 / 1024 : ℝ)) ≤ (4398643 / 10000000 : ℝ) := by
  have hsmall : (2564993681 / 2500000000 : ℝ) ≤ Real.exp (841 / 32768 : ℝ) ∧
      Real.exp (841 / 32768 : ℝ) ≤ (410398989 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (841 / 32768 : ℝ))
    (a := (2564993681 / 2500000000 : ℝ)) (b := (410398989 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_367 :
    (4811827 / 2000000 : ℝ) ≤ Real.exp (899 / 1024 : ℝ) ∧
    Real.exp (899 / 1024 : ℝ) ≤ (187962 / 78125 : ℝ) := by
  have hsmall : (51390755806427 / 50000000000000 : ℝ) ≤ Real.exp (899 / 32768 : ℝ) ∧
      Real.exp (899 / 32768 : ℝ) ≤ (20556302322571 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (899 / 32768 : ℝ))
    (a := (51390755806427 / 50000000000000 : ℝ)) (b := (20556302322571 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_368 :
    (834779 / 5000000 : ℝ) ≤ Real.exp (-(895013 / 500000 : ℝ)) ∧
    Real.exp (-(895013 / 500000 : ℝ)) ≤ (1669559 / 10000000 : ℝ) := by
  have hsmall : (10575324451 / 10000000000 : ℝ) ≤ Real.exp (895013 / 16000000 : ℝ) ∧
      Real.exp (895013 / 16000000 : ℝ) ≤ (2643831113 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (895013 / 16000000 : ℝ))
    (a := (10575324451 / 10000000000 : ℝ)) (b := (2643831113 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_369 :
    (1764087 / 10000000 : ℝ) ≤ Real.exp (-(17349517 / 10000000 : ℝ)) ∧
    Real.exp (-(17349517 / 10000000 : ℝ)) ≤ (220511 / 1250000 : ℝ) := by
  have hsmall : (10557139211 / 10000000000 : ℝ) ≤ Real.exp (17349517 / 320000000 : ℝ) ∧
      Real.exp (17349517 / 320000000 : ℝ) ≤ (2639284803 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17349517 / 320000000 : ℝ))
    (a := (10557139211 / 10000000000 : ℝ)) (b := (2639284803 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_370 :
    (259523 / 625000 : ℝ) ≤ Real.exp (-(225 / 256 : ℝ)) ∧
    Real.exp (-(225 / 256 : ℝ)) ≤ (4152369 / 10000000 : ℝ) := by
  have hsmall : (1027846483 / 1000000000 : ℝ) ≤ Real.exp (225 / 8192 : ℝ) ∧
      Real.exp (225 / 8192 : ℝ) ≤ (10278464831 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (225 / 8192 : ℝ))
    (a := (1027846483 / 1000000000 : ℝ)) (b := (10278464831 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_371 :
    (198389 / 80000 : ℝ) ≤ Real.exp (465 / 512 : ℝ) ∧
    Real.exp (465 / 512 : ℝ) ≤ (12399313 / 5000000 : ℝ) := by
  have hsmall : (102878793549263 / 100000000000000 : ℝ) ≤ Real.exp (465 / 16384 : ℝ) ∧
      Real.exp (465 / 16384 : ℝ) ≤ (6429924596829 / 6250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (465 / 16384 : ℝ))
    (a := (102878793549263 / 100000000000000 : ℝ)) (b := (6429924596829 / 6250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_372 :
    (734837 / 1250000 : ℝ) ≤ Real.exp (-(17 / 32 : ℝ)) ∧
    Real.exp (-(17 / 32 : ℝ)) ≤ (5878697 / 10000000 : ℝ) := by
  have hsmall : (5083700671 / 5000000000 : ℝ) ≤ Real.exp (17 / 1024 : ℝ) ∧
      Real.exp (17 / 1024 : ℝ) ≤ (10167401343 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 1024 : ℝ))
    (a := (5083700671 / 5000000000 : ℝ)) (b := (10167401343 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_373 :
    (197167 / 1250000 : ℝ) ≤ Real.exp (-(9234237 / 5000000 : ℝ)) ∧
    Real.exp (-(9234237 / 5000000 : ℝ)) ≤ (1577337 / 10000000 : ℝ) := by
  have hsmall : (5297059703 / 5000000000 : ℝ) ≤ Real.exp (9234237 / 160000000 : ℝ) ∧
      Real.exp (9234237 / 160000000 : ℝ) ≤ (10594119407 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9234237 / 160000000 : ℝ))
    (a := (5297059703 / 5000000000 : ℝ)) (b := (10594119407 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_374 :
    (1669559 / 10000000 : ℝ) ≤ Real.exp (-(71601 / 40000 : ℝ)) ∧
    Real.exp (-(71601 / 40000 : ℝ)) ≤ (41739 / 250000 : ℝ) := by
  have hsmall : (10575324121 / 10000000000 : ℝ) ≤ Real.exp (71601 / 1280000 : ℝ) ∧
      Real.exp (71601 / 1280000 : ℝ) ≤ (5287662061 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (71601 / 1280000 : ℝ))
    (a := (10575324121 / 10000000000 : ℝ)) (b := (5287662061 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_375 :
    (6390211 / 2500000 : ℝ) ≤ Real.exp (961 / 1024 : ℝ) ∧
    Real.exp (961 / 1024 : ℝ) ≤ (5112169 / 2000000 : ℝ) := by
  have hsmall : (51488083781151 / 50000000000000 : ℝ) ≤ Real.exp (961 / 32768 : ℝ) ∧
      Real.exp (961 / 32768 : ℝ) ≤ (102976167562303 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (961 / 32768 : ℝ))
    (a := (51488083781151 / 50000000000000 : ℝ)) (b := (102976167562303 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_376 :
    (3032653 / 5000000 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) ∧
    Real.exp (-(1 / 2 : ℝ)) ≤ (6065307 / 10000000 : ℝ) := by
  have hsmall : (2031495417 / 2000000000 : ℝ) ≤ Real.exp (1 / 64 : ℝ) ∧
      Real.exp (1 / 64 : ℝ) ≤ (5078738543 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 64 : ℝ))
    (a := (2031495417 / 2000000000 : ℝ)) (b := (5078738543 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_377 :
    (1487523 / 10000000 : ℝ) ≤ Real.exp (-(19054727 / 10000000 : ℝ)) ∧
    Real.exp (-(19054727 / 10000000 : ℝ)) ≤ (371881 / 2500000 : ℝ) := by
  have hsmall : (10613546053 / 10000000000 : ℝ) ≤ Real.exp (19054727 / 320000000 : ℝ) ∧
      Real.exp (19054727 / 320000000 : ℝ) ≤ (5306773027 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (19054727 / 320000000 : ℝ))
    (a := (10613546053 / 10000000000 : ℝ)) (b := (5306773027 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_378 :
    (788669 / 5000000 : ℝ) ≤ Real.exp (-(1154279 / 625000 : ℝ)) ∧
    Real.exp (-(1154279 / 625000 : ℝ)) ≤ (1577339 / 10000000 : ℝ) := by
  have hsmall : (423764763 / 400000000 : ℝ) ≤ Real.exp (1154279 / 20000000 : ℝ) ∧
      Real.exp (1154279 / 20000000 : ℝ) ≤ (2648529769 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1154279 / 20000000 : ℝ))
    (a := (423764763 / 400000000 : ℝ)) (b := (2648529769 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_379 :
    (2634649 / 1000000 : ℝ) ≤ Real.exp (31 / 32 : ℝ) ∧
    Real.exp (31 / 32 : ℝ) ≤ (26346491 / 10000000 : ℝ) := by
  have hsmall : (1288420421739 / 1250000000000 : ℝ) ≤ Real.exp (31 / 1024 : ℝ) ∧
      Real.exp (31 / 1024 : ℝ) ≤ (103073633739121 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 1024 : ℝ))
    (a := (1288420421739 / 1250000000000 : ℝ)) (b := (103073633739121 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_380 :
    (78223 / 125000 : ℝ) ≤ Real.exp (-(15 / 32 : ℝ)) ∧
    Real.exp (-(15 / 32 : ℝ)) ≤ (6257841 / 10000000 : ℝ) := by
  have hsmall : (2536890629 / 2500000000 : ℝ) ≤ Real.exp (15 / 1024 : ℝ) ∧
      Real.exp (15 / 1024 : ℝ) ≤ (10147562517 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15 / 1024 : ℝ))
    (a := (2536890629 / 2500000000 : ℝ)) (b := (10147562517 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_381 :
    (280043 / 2000000 : ℝ) ≤ Real.exp (-(1965959 / 1000000 : ℝ)) ∧
    Real.exp (-(1965959 / 1000000 : ℝ)) ≤ (175027 / 1250000 : ℝ) := by
  have hsmall : (10633626717 / 10000000000 : ℝ) ≤ Real.exp (1965959 / 32000000 : ℝ) ∧
      Real.exp (1965959 / 32000000 : ℝ) ≤ (5316813359 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1965959 / 32000000 : ℝ))
    (a := (10633626717 / 10000000000 : ℝ)) (b := (5316813359 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_382 :
    (371881 / 2500000 : ℝ) ≤ Real.exp (-(4763679 / 2500000 : ℝ)) ∧
    Real.exp (-(4763679 / 2500000 : ℝ)) ≤ (59501 / 400000 : ℝ) := by
  have hsmall : (10613545689 / 10000000000 : ℝ) ≤ Real.exp (4763679 / 80000000 : ℝ) ∧
      Real.exp (4763679 / 80000000 : ℝ) ≤ (1061354569 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4763679 / 80000000 : ℝ))
    (a := (10613545689 / 10000000000 : ℝ)) (b := (1061354569 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_383 :
    (1726267 / 5000000 : ℝ) ≤ Real.exp (-(1089 / 1024 : ℝ)) ∧
    Real.exp (-(1089 / 1024 : ℝ)) ≤ (690507 / 2000000 : ℝ) := by
  have hsmall : (1292240061 / 1250000000 : ℝ) ≤ Real.exp (1089 / 32768 : ℝ) ∧
      Real.exp (1089 / 32768 : ℝ) ≤ (10337920489 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1089 / 32768 : ℝ))
    (a := (1292240061 / 1250000000 : ℝ)) (b := (10337920489 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_384 :
    (5431257 / 2000000 : ℝ) ≤ Real.exp (1023 / 1024 : ℝ) ∧
    Real.exp (1023 / 1024 : ℝ) ≤ (13578143 / 5000000 : ℝ) := by
  have hsmall : (103171192166949 / 100000000000000 : ℝ) ≤ Real.exp (1023 / 32768 : ℝ) ∧
      Real.exp (1023 / 32768 : ℝ) ≤ (2063423843339 / 2000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1023 / 32768 : ℝ))
    (a := (103171192166949 / 100000000000000 : ℝ)) (b := (2063423843339 / 2000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_385 :
    (1291297 / 2000000 : ℝ) ≤ Real.exp (-(7 / 16 : ℝ)) ∧
    Real.exp (-(7 / 16 : ℝ)) ≤ (3228243 / 5000000 : ℝ) := by
  have hsmall : (1267207203 / 1250000000 : ℝ) ≤ Real.exp (7 / 512 : ℝ) ∧
      Real.exp (7 / 512 : ℝ) ≤ (81101261 / 80000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7 / 512 : ℝ))
    (a := (1267207203 / 1250000000 : ℝ)) (b := (81101261 / 80000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_386 :
    (82219 / 625000 : ℝ) ≤ Real.exp (-(5070913 / 2500000 : ℝ)) ∧
    Real.exp (-(5070913 / 2500000 : ℝ)) ≤ (263101 / 2000000 : ℝ) := by
  have hsmall : (1331798073 / 1250000000 : ℝ) ≤ Real.exp (5070913 / 80000000 : ℝ) ∧
      Real.exp (5070913 / 80000000 : ℝ) ≤ (2130876917 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5070913 / 80000000 : ℝ))
    (a := (1331798073 / 1250000000 : ℝ)) (b := (2130876917 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_387 :
    (175027 / 1250000 : ℝ) ≤ Real.exp (-(982979 / 500000 : ℝ)) ∧
    Real.exp (-(982979 / 500000 : ℝ)) ≤ (1400217 / 10000000 : ℝ) := by
  have hsmall : (2126725277 / 2000000000 : ℝ) ≤ Real.exp (982979 / 16000000 : ℝ) ∧
      Real.exp (982979 / 16000000 : ℝ) ≤ (5316813193 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (982979 / 16000000 : ℝ))
    (a := (2126725277 / 2000000000 : ℝ)) (b := (5316813193 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_388 :
    (3233867 / 10000000 : ℝ) ≤ Real.exp (-(289 / 256 : ℝ)) ∧
    Real.exp (-(289 / 256 : ℝ)) ≤ (808467 / 2500000 : ℝ) := by
  have hsmall : (10359079829 / 10000000000 : ℝ) ≤ Real.exp (289 / 8192 : ℝ) ∧
      Real.exp (289 / 8192 : ℝ) ≤ (1035907983 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (289 / 8192 : ℝ))
    (a := (10359079829 / 10000000000 : ℝ)) (b := (1035907983 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_389 :
    (1665359 / 2500000 : ℝ) ≤ Real.exp (-(13 / 32 : ℝ)) ∧
    Real.exp (-(13 / 32 : ℝ)) ≤ (6661437 / 10000000 : ℝ) := by
  have hsmall : (12659703 / 12500000 : ℝ) ≤ Real.exp (13 / 1024 : ℝ) ∧
      Real.exp (13 / 1024 : ℝ) ≤ (10127762401 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13 / 1024 : ℝ))
    (a := (12659703 / 12500000 : ℝ)) (b := (10127762401 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_390 :
    (1233471 / 10000000 : ℝ) ≤ Real.exp (-(5231881 / 2500000 : ℝ)) ∧
    Real.exp (-(5231881 / 2500000 : ℝ)) ≤ (19273 / 156250 : ℝ) := by
  have hsmall : (10675843853 / 10000000000 : ℝ) ≤ Real.exp (5231881 / 80000000 : ℝ) ∧
      Real.exp (5231881 / 80000000 : ℝ) ≤ (5337921927 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5231881 / 80000000 : ℝ))
    (a := (10675843853 / 10000000000 : ℝ)) (b := (5337921927 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_391 :
    (263101 / 2000000 : ℝ) ≤ Real.exp (-(20283641 / 10000000 : ℝ)) ∧
    Real.exp (-(20283641 / 10000000 : ℝ)) ≤ (657753 / 5000000 : ℝ) := by
  have hsmall : (5327192109 / 5000000000 : ℝ) ≤ Real.exp (20283641 / 320000000 : ℝ) ∧
      Real.exp (20283641 / 320000000 : ℝ) ≤ (10654384219 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (20283641 / 320000000 : ℝ))
    (a := (5327192109 / 5000000000 : ℝ)) (b := (10654384219 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_392 :
    (151157 / 500000 : ℝ) ≤ Real.exp (-(1225 / 1024 : ℝ)) ∧
    Real.exp (-(1225 / 1024 : ℝ)) ≤ (3023141 / 10000000 : ℝ) := by
  have hsmall : (10380916059 / 10000000000 : ℝ) ≤ Real.exp (1225 / 32768 : ℝ) ∧
      Real.exp (1225 / 32768 : ℝ) ≤ (519045803 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1225 / 32768 : ℝ))
    (a := (10380916059 / 10000000000 : ℝ)) (b := (519045803 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_393 :
    (2885131 / 1000000 : ℝ) ≤ Real.exp (1085 / 1024 : ℝ) ∧
    Real.exp (1085 / 1024 : ℝ) ≤ (28851311 / 10000000 : ℝ) := by
  have hsmall : (20673317224997 / 20000000000000 : ℝ) ≤ Real.exp (1085 / 32768 : ℝ) ∧
      Real.exp (1085 / 32768 : ℝ) ≤ (51683293062493 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1085 / 32768 : ℝ))
    (a := (20673317224997 / 20000000000000 : ℝ)) (b := (51683293062493 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_394 :
    (1718223 / 2500000 : ℝ) ≤ Real.exp (-(3 / 8 : ℝ)) ∧
    Real.exp (-(3 / 8 : ℝ)) ≤ (6872893 / 10000000 : ℝ) := by
  have hsmall : (2023575367 / 2000000000 : ℝ) ≤ Real.exp (3 / 256 : ℝ) ∧
      Real.exp (3 / 256 : ℝ) ≤ (2529469209 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3 / 256 : ℝ))
    (a := (2023575367 / 2000000000 : ℝ)) (b := (2529469209 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_395 :
    (1154193 / 10000000 : ℝ) ≤ Real.exp (-(21591833 / 10000000 : ℝ)) ∧
    Real.exp (-(21591833 / 10000000 : ℝ)) ≤ (577097 / 5000000 : ℝ) := by
  have hsmall : (5349014779 / 5000000000 : ℝ) ≤ Real.exp (21591833 / 320000000 : ℝ) ∧
      Real.exp (21591833 / 320000000 : ℝ) ≤ (10698029559 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (21591833 / 320000000 : ℝ))
    (a := (5349014779 / 5000000000 : ℝ)) (b := (10698029559 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_396 :
    (19273 / 156250 : ℝ) ≤ Real.exp (-(10463757 / 5000000 : ℝ)) ∧
    Real.exp (-(10463757 / 5000000 : ℝ)) ≤ (1233473 / 10000000 : ℝ) := by
  have hsmall : (10675843519 / 10000000000 : ℝ) ≤ Real.exp (10463757 / 160000000 : ℝ) ∧
      Real.exp (10463757 / 160000000 : ℝ) ≤ (33362011 / 31250000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10463757 / 160000000 : ℝ))
    (a := (10675843519 / 10000000000 : ℝ)) (b := (33362011 / 31250000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_397 :
    (2820629 / 10000000 : ℝ) ≤ Real.exp (-(81 / 64 : ℝ)) ∧
    Real.exp (-(81 / 64 : ℝ)) ≤ (282063 / 1000000 : ℝ) := by
  have hsmall : (5201716637 / 5000000000 : ℝ) ≤ Real.exp (81 / 2048 : ℝ) ∧
      Real.exp (81 / 2048 : ℝ) ≤ (416137331 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (81 / 2048 : ℝ))
    (a := (5201716637 / 5000000000 : ℝ)) (b := (416137331 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_398 :
    (29738093 / 10000000 : ℝ) ≤ Real.exp (279 / 256 : ℝ) ∧
    Real.exp (279 / 256 : ℝ) ≤ (14869047 / 5000000 : ℝ) := by
  have hsmall : (103464421830069 / 100000000000000 : ℝ) ≤ Real.exp (279 / 8192 : ℝ) ∧
      Real.exp (279 / 8192 : ℝ) ≤ (10346442183007 / 10000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (279 / 8192 : ℝ))
    (a := (103464421830069 / 100000000000000 : ℝ)) (b := (10346442183007 / 10000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_399 :
    (7091061 / 10000000 : ℝ) ≤ Real.exp (-(11 / 32 : ℝ)) ∧
    Real.exp (-(11 / 32 : ℝ)) ≤ (3545531 / 5000000 : ℝ) := by
  have hsmall : (10108000919 / 10000000000 : ℝ) ≤ Real.exp (11 / 1024 : ℝ) ∧
      Real.exp (11 / 1024 : ℝ) ≤ (252700023 / 250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11 / 1024 : ℝ))
    (a := (10108000919 / 10000000000 : ℝ)) (b := (252700023 / 250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_400 :
    (215547 / 2000000 : ℝ) ≤ Real.exp (-(22277231 / 10000000 : ℝ)) ∧
    Real.exp (-(22277231 / 10000000 : ℝ)) ≤ (134717 / 1250000 : ℝ) := by
  have hsmall : (1072096789 / 1000000000 : ℝ) ≤ Real.exp (22277231 / 320000000 : ℝ) ∧
      Real.exp (22277231 / 320000000 : ℝ) ≤ (10720967891 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (22277231 / 320000000 : ℝ))
    (a := (1072096789 / 1000000000 : ℝ)) (b := (10720967891 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_401 :
    (577097 / 5000000 : ℝ) ≤ Real.exp (-(10795911 / 5000000 : ℝ)) ∧
    Real.exp (-(10795911 / 5000000 : ℝ)) ≤ (230839 / 2000000 : ℝ) := by
  have hsmall : (1069802919 / 1000000000 : ℝ) ≤ Real.exp (10795911 / 160000000 : ℝ) ∧
      Real.exp (10795911 / 160000000 : ℝ) ≤ (10698029191 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10795911 / 160000000 : ℝ))
    (a := (1069802919 / 1000000000 : ℝ)) (b := (10698029191 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_402 :
    (2626549 / 10000000 : ℝ) ≤ Real.exp (-(1369 / 1024 : ℝ)) ∧
    Real.exp (-(1369 / 1024 : ℝ)) ≤ (52531 / 200000 : ℝ) := by
  have hsmall : (1303329463 / 1250000000 : ℝ) ≤ Real.exp (1369 / 32768 : ℝ) ∧
      Real.exp (1369 / 32768 : ℝ) ≤ (2085327141 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1369 / 32768 : ℝ))
    (a := (1303329463 / 1250000000 : ℝ)) (b := (2085327141 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_403 :
    (30652133 / 10000000 : ℝ) ≤ Real.exp (1147 / 1024 : ℝ) ∧
    Real.exp (1147 / 1024 : ℝ) ≤ (15326067 / 5000000 : ℝ) := by
  have hsmall : (103562350135921 / 100000000000000 : ℝ) ≤ Real.exp (1147 / 32768 : ℝ) ∧
      Real.exp (1147 / 32768 : ℝ) ≤ (51781175067961 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1147 / 32768 : ℝ))
    (a := (103562350135921 / 100000000000000 : ℝ)) (b := (51781175067961 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_404 :
    (1829039 / 2500000 : ℝ) ≤ Real.exp (-(5 / 16 : ℝ)) ∧
    Real.exp (-(5 / 16 : ℝ)) ≤ (7316157 / 10000000 : ℝ) := by
  have hsmall : (10098134643 / 10000000000 : ℝ) ≤ Real.exp (5 / 512 : ℝ) ∧
      Real.exp (5 / 512 : ℝ) ≤ (2524533661 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5 / 512 : ℝ))
    (a := (10098134643 / 10000000000 : ℝ)) (b := (2524533661 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_405 :
    (502077 / 5000000 : ℝ) ≤ Real.exp (-(5746097 / 2500000 : ℝ)) ∧
    Real.exp (-(5746097 / 2500000 : ℝ)) ≤ (200831 / 2000000 : ℝ) := by
  have hsmall : (5372342993 / 5000000000 : ℝ) ≤ Real.exp (5746097 / 80000000 : ℝ) ∧
      Real.exp (5746097 / 80000000 : ℝ) ≤ (10744685987 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5746097 / 80000000 : ℝ))
    (a := (5372342993 / 5000000000 : ℝ)) (b := (10744685987 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_406 :
    (134717 / 1250000 : ℝ) ≤ Real.exp (-(1113861 / 500000 : ℝ)) ∧
    Real.exp (-(1113861 / 500000 : ℝ)) ≤ (1077737 / 10000000 : ℝ) := by
  have hsmall : (5360483761 / 5000000000 : ℝ) ≤ Real.exp (1113861 / 16000000 : ℝ) ∧
      Real.exp (1113861 / 16000000 : ℝ) ≤ (10720967523 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1113861 / 16000000 : ℝ))
    (a := (5360483761 / 5000000000 : ℝ)) (b := (10720967523 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_407 :
    (2441051 / 10000000 : ℝ) ≤ Real.exp (-(361 / 256 : ℝ)) ∧
    Real.exp (-(361 / 256 : ℝ)) ≤ (610263 / 2500000 : ℝ) := by
  have hsmall : (10450527711 / 10000000000 : ℝ) ≤ Real.exp (361 / 8192 : ℝ) ∧
      Real.exp (361 / 8192 : ℝ) ≤ (326578991 / 312500000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (361 / 8192 : ℝ))
    (a := (10450527711 / 10000000000 : ℝ)) (b := (326578991 / 312500000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_408 :
    (7898567 / 2500000 : ℝ) ≤ Real.exp (589 / 512 : ℝ) ∧
    Real.exp (589 / 512 : ℝ) ≤ (31594269 / 10000000 : ℝ) := by
  have hsmall : (20732074226037 / 20000000000000 : ℝ) ≤ Real.exp (589 / 16384 : ℝ) ∧
      Real.exp (589 / 16384 : ℝ) ≤ (51830185565093 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (589 / 16384 : ℝ))
    (a := (20732074226037 / 20000000000000 : ℝ)) (b := (51830185565093 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_409 :
    (1509679 / 2000000 : ℝ) ≤ Real.exp (-(9 / 32 : ℝ)) ∧
    Real.exp (-(9 / 32 : ℝ)) ≤ (7548397 / 10000000 : ℝ) := by
  have hsmall : (10088277997 / 10000000000 : ℝ) ≤ Real.exp (9 / 1024 : ℝ) ∧
      Real.exp (9 / 1024 : ℝ) ≤ (5044138999 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 1024 : ℝ))
    (a := (10088277997 / 10000000000 : ℝ)) (b := (5044138999 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_410 :
    (1867 / 20000 : ℝ) ≤ Real.exp (-(2964249 / 1250000 : ℝ)) ∧
    Real.exp (-(2964249 / 1250000 : ℝ)) ≤ (933501 / 10000000 : ℝ) := by
  have hsmall : (10769211953 / 10000000000 : ℝ) ≤ Real.exp (2964249 / 40000000 : ℝ) ∧
      Real.exp (2964249 / 40000000 : ℝ) ≤ (5384605977 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2964249 / 40000000 : ℝ))
    (a := (10769211953 / 10000000000 : ℝ)) (b := (5384605977 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_411 :
    (251039 / 2500000 : ℝ) ≤ Real.exp (-(22984377 / 10000000 : ℝ)) ∧
    Real.exp (-(22984377 / 10000000 : ℝ)) ≤ (1004157 / 10000000 : ℝ) := by
  have hsmall : (671542851 / 625000000 : ℝ) ≤ Real.exp (22984377 / 320000000 : ℝ) ∧
      Real.exp (22984377 / 320000000 : ℝ) ≤ (10744685617 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (22984377 / 320000000 : ℝ))
    (a := (671542851 / 625000000 : ℝ)) (b := (10744685617 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_412 :
    (2264227 / 10000000 : ℝ) ≤ Real.exp (-(1521 / 1024 : ℝ)) ∧
    Real.exp (-(1521 / 1024 : ℝ)) ≤ (566057 / 2500000 : ℝ) := by
  have hsmall : (2095022759 / 2000000000 : ℝ) ≤ Real.exp (1521 / 32768 : ℝ) ∧
      Real.exp (1521 / 32768 : ℝ) ≤ (2618778449 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1521 / 32768 : ℝ))
    (a := (2095022759 / 2000000000 : ℝ)) (b := (2618778449 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_413 :
    (407067 / 125000 : ℝ) ≤ Real.exp (1209 / 1024 : ℝ) ∧
    Real.exp (1209 / 1024 : ℝ) ≤ (32565361 / 10000000 : ℝ) := by
  have hsmall : (6484905306287 / 6250000000000 : ℝ) ≤ Real.exp (1209 / 32768 : ℝ) ∧
      Real.exp (1209 / 32768 : ℝ) ≤ (103758484900593 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1209 / 32768 : ℝ))
    (a := (6484905306287 / 6250000000000 : ℝ)) (b := (103758484900593 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_414 :
    (865809 / 10000000 : ℝ) ≤ Real.exp (-(382293 / 156250 : ℝ)) ∧
    Real.exp (-(382293 / 156250 : ℝ)) ≤ (86581 / 1000000 : ℝ) := by
  have hsmall : (5397287499 / 5000000000 : ℝ) ≤ Real.exp (382293 / 5000000 : ℝ) ∧
      Real.exp (382293 / 5000000 : ℝ) ≤ (10794574999 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (382293 / 5000000 : ℝ))
    (a := (5397287499 / 5000000000 : ℝ)) (b := (10794574999 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_415 :
    (933501 / 10000000 : ℝ) ≤ Real.exp (-(23713977 / 10000000 : ℝ)) ∧
    Real.exp (-(23713977 / 10000000 : ℝ)) ≤ (466751 / 5000000 : ℝ) := by
  have hsmall : (1346151431 / 1250000000 : ℝ) ≤ Real.exp (23713977 / 320000000 : ℝ) ∧
      Real.exp (23713977 / 320000000 : ℝ) ≤ (10769211449 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (23713977 / 320000000 : ℝ))
    (a := (1346151431 / 1250000000 : ℝ)) (b := (10769211449 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_416 :
    (335663 / 100000 : ℝ) ≤ Real.exp (155 / 128 : ℝ) ∧
    Real.exp (155 / 128 : ℝ) ≤ (33566301 / 10000000 : ℝ) := by
  have hsmall : (103856691534953 / 100000000000000 : ℝ) ≤ Real.exp (155 / 4096 : ℝ) ∧
      Real.exp (155 / 4096 : ℝ) ≤ (51928345767477 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (155 / 4096 : ℝ))
    (a := (103856691534953 / 100000000000000 : ℝ)) (b := (51928345767477 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_417 :
    (8290291 / 10000000 : ℝ) ≤ Real.exp (-(3 / 16 : ℝ)) ∧
    Real.exp (-(3 / 16 : ℝ)) ≤ (2072573 / 2500000 : ℝ) := by
  have hsmall : (10058765747 / 10000000000 : ℝ) ≤ Real.exp (3 / 512 : ℝ) ∧
      Real.exp (3 / 512 : ℝ) ≤ (2514691437 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3 / 512 : ℝ))
    (a := (10058765747 / 10000000000 : ℝ)) (b := (2514691437 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_418 :
    (739421 / 10000000 : ℝ) ≤ Real.exp (-(6511181 / 2500000 : ℝ)) ∧
    Real.exp (-(6511181 / 2500000 : ℝ)) ≤ (369711 / 5000000 : ℝ) := by
  have hsmall : (542396813 / 500000000 : ℝ) ≤ Real.exp (6511181 / 80000000 : ℝ) ∧
      Real.exp (6511181 / 80000000 : ℝ) ≤ (10847936261 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6511181 / 80000000 : ℝ))
    (a := (542396813 / 500000000 : ℝ)) (b := (10847936261 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_419 :
    (86581 / 1000000 : ℝ) ≤ Real.exp (-(1223337 / 500000 : ℝ)) ∧
    Real.exp (-(1223337 / 500000 : ℝ)) ≤ (865811 / 10000000 : ℝ) := by
  have hsmall : (10794574593 / 10000000000 : ℝ) ≤ Real.exp (1223337 / 16000000 : ℝ) ∧
      Real.exp (1223337 / 16000000 : ℝ) ≤ (5397287297 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1223337 / 16000000 : ℝ))
    (a := (10794574593 / 10000000000 : ℝ)) (b := (5397287297 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_420 :
    (1785911 / 10000000 : ℝ) ≤ Real.exp (-(441 / 256 : ℝ)) ∧
    Real.exp (-(441 / 256 : ℝ)) ≤ (223239 / 1250000 : ℝ) := by
  have hsmall : (10553083591 / 10000000000 : ℝ) ≤ Real.exp (441 / 8192 : ℝ) ∧
      Real.exp (441 / 8192 : ℝ) ≤ (1319135449 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (441 / 8192 : ℝ))
    (a := (10553083591 / 10000000000 : ℝ)) (b := (1319135449 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_421 :
    (35661421 / 10000000 : ℝ) ≤ Real.exp (651 / 512 : ℝ) ∧
    Real.exp (651 / 512 : ℝ) ≤ (17830711 / 5000000 : ℝ) := by
  have hsmall : (104053383747201 / 100000000000000 : ℝ) ≤ Real.exp (651 / 16384 : ℝ) ∧
      Real.exp (651 / 16384 : ℝ) ≤ (52026691873601 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (651 / 16384 : ℝ))
    (a := (104053383747201 / 100000000000000 : ℝ)) (b := (52026691873601 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_422 :
    (8824969 / 10000000 : ℝ) ≤ Real.exp (-(1 / 8 : ℝ)) ∧
    Real.exp (-(1 / 8 : ℝ)) ≤ (882497 / 1000000 : ℝ) := by
  have hsmall : (10039138893 / 10000000000 : ℝ) ≤ Real.exp (1 / 256 : ℝ) ∧
      Real.exp (1 / 256 : ℝ) ≤ (5019569447 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 256 : ℝ))
    (a := (10039138893 / 10000000000 : ℝ)) (b := (5019569447 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_423 :
    (9767 / 156250 : ℝ) ≤ Real.exp (-(1732779 / 625000 : ℝ)) ∧
    Real.exp (-(1732779 / 625000 : ℝ)) ≤ (625089 / 10000000 : ℝ) := by
  have hsmall : (436201153 / 400000000 : ℝ) ≤ Real.exp (1732779 / 20000000 : ℝ) ∧
      Real.exp (1732779 / 20000000 : ℝ) ≤ (5452514413 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1732779 / 20000000 : ℝ))
    (a := (436201153 / 400000000 : ℝ)) (b := (5452514413 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_424 :
    (369711 / 5000000 : ℝ) ≤ Real.exp (-(26044711 / 10000000 : ℝ)) ∧
    Real.exp (-(26044711 / 10000000 : ℝ)) ≤ (739423 / 10000000 : ℝ) := by
  have hsmall : (10847935819 / 10000000000 : ℝ) ≤ Real.exp (26044711 / 320000000 : ℝ) ∧
      Real.exp (26044711 / 320000000 : ℝ) ≤ (542396791 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (26044711 / 320000000 : ℝ))
    (a := (10847935819 / 10000000000 : ℝ)) (b := (542396791 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_425 :
    (754887 / 5000000 : ℝ) ≤ Real.exp (-(121 / 64 : ℝ)) ∧
    Real.exp (-(121 / 64 : ℝ)) ≤ (60391 / 400000 : ℝ) := by
  have hsmall : (1060862261 / 1000000000 : ℝ) ≤ Real.exp (121 / 2048 : ℝ) ∧
      Real.exp (121 / 2048 : ℝ) ≤ (10608622611 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (121 / 2048 : ℝ))
    (a := (1060862261 / 1000000000 : ℝ)) (b := (10608622611 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_426 :
    (18943657 / 5000000 : ℝ) ≤ Real.exp (341 / 256 : ℝ) ∧
    Real.exp (341 / 256 : ℝ) ≤ (7577463 / 2000000 : ℝ) := by
  have hsmall : (104250448471087 / 100000000000000 : ℝ) ≤ Real.exp (341 / 8192 : ℝ) ∧
      Real.exp (341 / 8192 : ℝ) ≤ (6515653029443 / 6250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (341 / 8192 : ℝ))
    (a := (104250448471087 / 100000000000000 : ℝ)) (b := (6515653029443 / 6250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_427 :
    (522741 / 10000000 : ℝ) ≤ Real.exp (-(29512537 / 10000000 : ℝ)) ∧
    Real.exp (-(29512537 / 10000000 : ℝ)) ≤ (261371 / 5000000 : ℝ) := by
  have hsmall : (10966133721 / 10000000000 : ℝ) ≤ Real.exp (29512537 / 320000000 : ℝ) ∧
      Real.exp (29512537 / 320000000 : ℝ) ≤ (5483066861 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29512537 / 320000000 : ℝ))
    (a := (10966133721 / 10000000000 : ℝ)) (b := (5483066861 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_428 :
    (625089 / 10000000 : ℝ) ≤ Real.exp (-(6931113 / 2500000 : ℝ)) ∧
    Real.exp (-(6931113 / 2500000 : ℝ)) ≤ (62509 / 1000000 : ℝ) := by
  have hsmall : (170391069 / 156250000 : ℝ) ≤ Real.exp (6931113 / 80000000 : ℝ) ∧
      Real.exp (6931113 / 80000000 : ℝ) ≤ (10905028417 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6931113 / 80000000 : ℝ))
    (a := (170391069 / 156250000 : ℝ)) (b := (10905028417 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_429 :
    (40252141 / 10000000 : ℝ) ≤ Real.exp (713 / 512 : ℝ) ∧
    Real.exp (713 / 512 : ℝ) ≤ (20126071 / 5000000 : ℝ) := by
  have hsmall : (13055985801513 / 12500000000000 : ℝ) ≤ Real.exp (713 / 16384 : ℝ) ∧
      Real.exp (713 / 16384 : ℝ) ≤ (20889577282421 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (713 / 16384 : ℝ))
    (a := (13055985801513 / 12500000000000 : ℝ)) (b := (20889577282421 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_430 :
    (432139 / 10000000 : ℝ) ≤ Real.exp (-(3141593 / 1000000 : ℝ)) ∧
    Real.exp (-(3141593 / 1000000 : ℝ)) ≤ (21607 / 500000 : ℝ) := by
  have hsmall : (11031555791 / 10000000000 : ℝ) ≤ Real.exp (3141593 / 32000000 : ℝ) ∧
      Real.exp (3141593 / 32000000 : ℝ) ≤ (689472237 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3141593 / 32000000 : ℝ))
    (a := (11031555791 / 10000000000 : ℝ)) (b := (689472237 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_431 :
    (261371 / 5000000 : ℝ) ≤ Real.exp (-(29512523 / 10000000 : ℝ)) ∧
    Real.exp (-(29512523 / 10000000 : ℝ)) ≤ (522743 / 10000000 : ℝ) := by
  have hsmall : (10966133241 / 10000000000 : ℝ) ≤ Real.exp (29512523 / 320000000 : ℝ) ∧
      Real.exp (29512523 / 320000000 : ℝ) ≤ (5483066621 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29512523 / 320000000 : ℝ))
    (a := (10966133241 / 10000000000 : ℝ)) (b := (5483066621 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_432 :
    (131749 / 1250000 : ℝ) ≤ Real.exp (-(9 / 4 : ℝ)) ∧
    Real.exp (-(9 / 4 : ℝ)) ≤ (1053993 / 10000000 : ℝ) := by
  have hsmall : (2682108481 / 2500000000 : ℝ) ≤ Real.exp (9 / 128 : ℝ) ∧
      Real.exp (9 / 128 : ℝ) ≤ (429137357 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 128 : ℝ))
    (a := (2682108481 / 2500000000 : ℝ)) (b := (429137357 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_433 :
    (1710583 / 400000 : ℝ) ≤ Real.exp (93 / 64 : ℝ) ∧
    Real.exp (93 / 64 : ℝ) ≤ (1336393 / 312500 : ℝ) := by
  have hsmall : (52322849138541 / 50000000000000 : ℝ) ≤ Real.exp (93 / 2048 : ℝ) ∧
      Real.exp (93 / 2048 : ℝ) ≤ (104645698277083 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 2048 : ℝ))
    (a := (52322849138541 / 50000000000000 : ℝ)) (b := (104645698277083 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_434 :
    (665309 / 625000 : ℝ) ≤ Real.exp (1 / 16 : ℝ) ∧
    Real.exp (1 / 16 : ℝ) ≤ (2128989 / 2000000 : ℝ) := by
  have hsmall : (1001955033591 / 1000000000000 : ℝ) ≤ Real.exp (1 / 512 : ℝ) ∧
      Real.exp (1 / 512 : ℝ) ≤ (100195503359101 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 512 : ℝ))
    (a := (1001955033591 / 1000000000000 : ℝ)) (b := (100195503359101 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_435 :
    (352881 / 10000000 : ℝ) ≤ Real.exp (-(6688417 / 2000000 : ℝ)) ∧
    Real.exp (-(6688417 / 2000000 : ℝ)) ≤ (176441 / 5000000 : ℝ) := by
  have hsmall : (346925821 / 312500000 : ℝ) ≤ Real.exp (6688417 / 64000000 : ℝ) ∧
      Real.exp (6688417 / 64000000 : ℝ) ≤ (11101626273 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6688417 / 64000000 : ℝ))
    (a := (346925821 / 312500000 : ℝ)) (b := (11101626273 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_436 :
    (432139 / 10000000 : ℝ) ≤ Real.exp (-(392699 / 125000 : ℝ)) ∧
    Real.exp (-(392699 / 125000 : ℝ)) ≤ (21607 / 500000 : ℝ) := by
  have hsmall : (5515777723 / 5000000000 : ℝ) ≤ Real.exp (392699 / 4000000 : ℝ) ∧
      Real.exp (392699 / 4000000 : ℝ) ≤ (11031555447 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (392699 / 4000000 : ℝ))
    (a := (5515777723 / 5000000000 : ℝ)) (b := (11031555447 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_437 :
    (870383 / 10000000 : ℝ) ≤ Real.exp (-(625 / 256 : ℝ)) ∧
    Real.exp (-(625 / 256 : ℝ)) ≤ (54399 / 625000 : ℝ) := by
  have hsmall : (10792797767 / 10000000000 : ℝ) ≤ Real.exp (625 / 8192 : ℝ) ∧
      Real.exp (625 / 8192 : ℝ) ≤ (1349099721 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (625 / 8192 : ℝ))
    (a := (10792797767 / 10000000000 : ℝ)) (b := (1349099721 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_438 :
    (45433829 / 10000000 : ℝ) ≤ Real.exp (775 / 512 : ℝ) ∧
    Real.exp (775 / 512 : ℝ) ≤ (4543383 / 1000000 : ℝ) := by
  have hsmall : (26210971193547 / 25000000000000 : ℝ) ≤ Real.exp (775 / 16384 : ℝ) ∧
      Real.exp (775 / 16384 : ℝ) ≤ (104843884774189 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (775 / 16384 : ℝ))
    (a := (26210971193547 / 25000000000000 : ℝ)) (b := (104843884774189 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_439 :
    (2832871 / 2500000 : ℝ) ≤ Real.exp (1 / 8 : ℝ) ∧
    Real.exp (1 / 8 : ℝ) ≤ (2266297 / 2000000 : ℝ) := by
  have hsmall : (50195694466917 / 50000000000000 : ℝ) ≤ Real.exp (1 / 256 : ℝ) ∧
      Real.exp (1 / 256 : ℝ) ≤ (20078277786767 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 256 : ℝ))
    (a := (50195694466917 / 50000000000000 : ℝ)) (b := (20078277786767 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_440 :
    (284419 / 10000000 : ℝ) ≤ Real.exp (-(17799457 / 5000000 : ℝ)) ∧
    Real.exp (-(17799457 / 5000000 : ℝ)) ≤ (14221 / 500000 : ℝ) := by
  have hsmall : (5588352487 / 5000000000 : ℝ) ≤ Real.exp (17799457 / 160000000 : ℝ) ∧
      Real.exp (17799457 / 160000000 : ℝ) ≤ (447068199 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17799457 / 160000000 : ℝ))
    (a := (5588352487 / 5000000000 : ℝ)) (b := (447068199 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_441 :
    (352881 / 10000000 : ℝ) ≤ Real.exp (-(3344207 / 1000000 : ℝ)) ∧
    Real.exp (-(3344207 / 1000000 : ℝ)) ≤ (176441 / 5000000 : ℝ) := by
  have hsmall : (1387703219 / 1250000000 : ℝ) ≤ Real.exp (3344207 / 32000000 : ℝ) ∧
      Real.exp (3344207 / 32000000 : ℝ) ≤ (11101625753 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3344207 / 32000000 : ℝ))
    (a := (1387703219 / 1250000000 : ℝ)) (b := (11101625753 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_442 :
    (356583 / 5000000 : ℝ) ≤ Real.exp (-(169 / 64 : ℝ)) ∧
    Real.exp (-(169 / 64 : ℝ)) ≤ (713167 / 10000000 : ℝ) := by
  have hsmall : (2172039769 / 2000000000 : ℝ) ≤ Real.exp (169 / 2048 : ℝ) ∧
      Real.exp (169 / 2048 : ℝ) ≤ (5430099423 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (169 / 2048 : ℝ))
    (a := (2172039769 / 2000000000 : ℝ)) (b := (5430099423 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_443 :
    (4826969 / 1000000 : ℝ) ≤ Real.exp (403 / 256 : ℝ) ∧
    Real.exp (403 / 256 : ℝ) ≤ (48269691 / 10000000 : ℝ) := by
  have hsmall : (10504244661293 / 10000000000000 : ℝ) ≤ Real.exp (403 / 8192 : ℝ) ∧
      Real.exp (403 / 8192 : ℝ) ≤ (105042446612931 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (403 / 8192 : ℝ))
    (a := (10504244661293 / 10000000000000 : ℝ)) (b := (105042446612931 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_444 :
    (6031151 / 5000000 : ℝ) ≤ Real.exp (3 / 16 : ℝ) ∧
    Real.exp (3 / 16 : ℝ) ≤ (12062303 / 10000000 : ℝ) := by
  have hsmall : (100587657471447 / 100000000000000 : ℝ) ≤ Real.exp (3 / 512 : ℝ) ∧
      Real.exp (3 / 512 : ℝ) ≤ (12573457183931 / 12500000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (3 / 512 : ℝ))
    (a := (100587657471447 / 100000000000000 : ℝ)) (b := (12573457183931 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_445 :
    (28259 / 1250000 : ℝ) ≤ Real.exp (-(37894847 / 10000000 : ℝ)) ∧
    Real.exp (-(37894847 / 10000000 : ℝ)) ≤ (226073 / 10000000 : ℝ) := by
  have hsmall : (703573991 / 625000000 : ℝ) ≤ Real.exp (37894847 / 320000000 : ℝ) ∧
      Real.exp (37894847 / 320000000 : ℝ) ≤ (11257183857 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (37894847 / 320000000 : ℝ))
    (a := (703573991 / 625000000 : ℝ)) (b := (11257183857 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_446 :
    (284419 / 10000000 : ℝ) ≤ Real.exp (-(35598899 / 10000000 : ℝ)) ∧
    Real.exp (-(35598899 / 10000000 : ℝ)) ≤ (14221 / 500000 : ℝ) := by
  have hsmall : (223534089 / 200000000 : ℝ) ≤ Real.exp (35598899 / 320000000 : ℝ) ∧
      Real.exp (35598899 / 320000000 : ℝ) ≤ (11176704451 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (35598899 / 320000000 : ℝ))
    (a := (223534089 / 200000000 : ℝ)) (b := (11176704451 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_447 :
    (2899 / 50000 : ℝ) ≤ Real.exp (-(729 / 256 : ℝ)) ∧
    Real.exp (-(729 / 256 : ℝ)) ≤ (579801 / 10000000 : ℝ) := by
  have hsmall : (10930689143 / 10000000000 : ℝ) ≤ Real.exp (729 / 8192 : ℝ) ∧
      Real.exp (729 / 8192 : ℝ) ≤ (1366336143 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (729 / 8192 : ℝ))
    (a := (10930689143 / 10000000000 : ℝ)) (b := (1366336143 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_448 :
    (51282559 / 10000000 : ℝ) ≤ Real.exp (837 / 512 : ℝ) ∧
    Real.exp (837 / 512 : ℝ) ≤ (80129 / 15625 : ℝ) := by
  have hsmall : (105241384504161 / 100000000000000 : ℝ) ≤ Real.exp (837 / 16384 : ℝ) ∧
      Real.exp (837 / 16384 : ℝ) ≤ (52620692252081 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (837 / 16384 : ℝ))
    (a := (105241384504161 / 100000000000000 : ℝ)) (b := (52620692252081 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_449 :
    (6420127 / 5000000 : ℝ) ≤ Real.exp (1 / 4 : ℝ) ∧
    Real.exp (1 / 4 : ℝ) ≤ (2568051 / 2000000 : ℝ) := by
  have hsmall : (25196077430161 / 25000000000000 : ℝ) ≤ Real.exp (1 / 128 : ℝ) ∧
      Real.exp (1 / 128 : ℝ) ≤ (20156861944129 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 128 : ℝ))
    (a := (25196077430161 / 25000000000000 : ℝ)) (b := (20156861944129 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_450 :
    (177053 / 10000000 : ℝ) ≤ Real.exp (-(5042357 / 1250000 : ℝ)) ∧
    Real.exp (-(5042357 / 1250000 : ℝ)) ≤ (35411 / 2000000 : ℝ) := by
  have hsmall : (5671745039 / 5000000000 : ℝ) ≤ Real.exp (5042357 / 40000000 : ℝ) ∧
      Real.exp (5042357 / 40000000 : ℝ) ≤ (11343490079 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5042357 / 40000000 : ℝ))
    (a := (5671745039 / 5000000000 : ℝ)) (b := (11343490079 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_451 :
    (28259 / 1250000 : ℝ) ≤ Real.exp (-(37894831 / 10000000 : ℝ)) ∧
    Real.exp (-(37894831 / 10000000 : ℝ)) ≤ (226073 / 10000000 : ℝ) := by
  have hsmall : (11257183293 / 10000000000 : ℝ) ≤ Real.exp (37894831 / 320000000 : ℝ) ∧
      Real.exp (37894831 / 320000000 : ℝ) ≤ (5628591647 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (37894831 / 320000000 : ℝ))
    (a := (11257183293 / 10000000000 : ℝ)) (b := (5628591647 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_452 :
    (233853 / 5000000 : ℝ) ≤ Real.exp (-(49 / 16 : ℝ)) ∧
    Real.exp (-(49 / 16 : ℝ)) ≤ (467707 / 10000000 : ℝ) := by
  have hsmall : (5502161623 / 5000000000 : ℝ) ≤ Real.exp (49 / 512 : ℝ) ∧
      Real.exp (49 / 512 : ℝ) ≤ (11004323247 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 512 : ℝ))
    (a := (5502161623 / 5000000000 : ℝ)) (b := (11004323247 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_453 :
    (54483483 / 10000000 : ℝ) ≤ Real.exp (217 / 128 : ℝ) ∧
    Real.exp (217 / 128 : ℝ) ≤ (13620871 / 2500000 : ℝ) := by
  have hsmall : (105440699160079 / 100000000000000 : ℝ) ≤ Real.exp (217 / 4096 : ℝ) ∧
      Real.exp (217 / 4096 : ℝ) ≤ (1318008739501 / 1250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (217 / 4096 : ℝ))
    (a := (105440699160079 / 100000000000000 : ℝ)) (b := (1318008739501 / 1250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_454 :
    (7274957 / 5000000 : ℝ) ≤ Real.exp (3 / 8 : ℝ) ∧
    Real.exp (3 / 8 : ℝ) ≤ (2909983 / 2000000 : ℝ) := by
  have hsmall : (101178768355933 / 100000000000000 : ℝ) ≤ Real.exp (3 / 256 : ℝ) ∧
      Real.exp (3 / 256 : ℝ) ≤ (50589384177967 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (3 / 256 : ℝ))
    (a := (101178768355933 / 100000000000000 : ℝ)) (b := (50589384177967 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_455 :
    (25869 / 2500000 : ℝ) ≤ Real.exp (-(5713739 / 1250000 : ℝ)) ∧
    Real.exp (-(5713739 / 1250000 : ℝ)) ≤ (103477 / 10000000 : ℝ) := by
  have hsmall : (5767746141 / 5000000000 : ℝ) ≤ Real.exp (5713739 / 40000000 : ℝ) ∧
      Real.exp (5713739 / 40000000 : ℝ) ≤ (11535492283 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5713739 / 40000000 : ℝ))
    (a := (5767746141 / 5000000000 : ℝ)) (b := (11535492283 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_456 :
    (88527 / 5000000 : ℝ) ≤ Real.exp (-(40338839 / 10000000 : ℝ)) ∧
    Real.exp (-(40338839 / 10000000 : ℝ)) ≤ (35411 / 2000000 : ℝ) := by
  have hsmall : (453739579 / 400000000 : ℝ) ≤ Real.exp (40338839 / 320000000 : ℝ) ∧
      Real.exp (40338839 / 320000000 : ℝ) ≤ (2835872369 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (40338839 / 320000000 : ℝ))
    (a := (453739579 / 400000000 : ℝ)) (b := (2835872369 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_457 :
    (74323 / 2500000 : ℝ) ≤ Real.exp (-(225 / 64 : ℝ)) ∧
    Real.exp (-(225 / 64 : ℝ)) ≤ (297293 / 10000000 : ℝ) := by
  have hsmall : (11161254647 / 10000000000 : ℝ) ≤ Real.exp (225 / 2048 : ℝ) ∧
      Real.exp (225 / 2048 : ℝ) ≤ (1395156831 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (225 / 2048 : ℝ))
    (a := (11161254647 / 10000000000 : ℝ)) (b := (1395156831 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_458 :
    (61497181 / 10000000 : ℝ) ≤ Real.exp (465 / 256 : ℝ) ∧
    Real.exp (465 / 256 : ℝ) ≤ (30748591 / 5000000 : ℝ) := by
  have hsmall : (1323005770269 / 1250000000000 : ℝ) ≤ Real.exp (465 / 8192 : ℝ) ∧
      Real.exp (465 / 8192 : ℝ) ≤ (105840461621521 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (465 / 8192 : ℝ))
    (a := (1323005770269 / 1250000000000 : ℝ)) (b := (105840461621521 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_459 :
    (4121803 / 2500000 : ℝ) ≤ Real.exp (1 / 2 : ℝ) ∧
    Real.exp (1 / 2 : ℝ) ≤ (16487213 / 10000000 : ℝ) := by
  have hsmall : (25393692714667 / 25000000000000 : ℝ) ≤ Real.exp (1 / 64 : ℝ) ∧
      Real.exp (1 / 64 : ℝ) ≤ (101574770858669 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 64 : ℝ))
    (a := (25393692714667 / 25000000000000 : ℝ)) (b := (101574770858669 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_460 :
    (56301 / 10000000 : ℝ) ≤ Real.exp (-(51796113 / 10000000 : ℝ)) ∧
    Real.exp (-(51796113 / 10000000 : ℝ)) ≤ (28151 / 5000000 : ℝ) := by
  have hsmall : (2939247467 / 2500000000 : ℝ) ≤ Real.exp (51796113 / 320000000 : ℝ) ∧
      Real.exp (51796113 / 320000000 : ℝ) ≤ (11756989869 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51796113 / 320000000 : ℝ))
    (a := (2939247467 / 2500000000 : ℝ)) (b := (11756989869 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_461 :
    (103477 / 10000000 : ℝ) ≤ Real.exp (-(45709893 / 10000000 : ℝ)) ∧
    Real.exp (-(45709893 / 10000000 : ℝ)) ≤ (51739 / 5000000 : ℝ) := by
  have hsmall : (11535491597 / 10000000000 : ℝ) ≤ Real.exp (45709893 / 320000000 : ℝ) ∧
      Real.exp (45709893 / 320000000 : ℝ) ≤ (5767745799 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (45709893 / 320000000 : ℝ))
    (a := (11535491597 / 10000000000 : ℝ)) (b := (5767745799 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_462 :
    (45789 / 2500000 : ℝ) ≤ Real.exp (-(4 / 1 : ℝ)) ∧
    Real.exp (-(4 / 1 : ℝ)) ≤ (183157 / 10000000 : ℝ) := by
  have hsmall : (1133148453 / 1000000000 : ℝ) ≤ Real.exp (1 / 8 : ℝ) ∧
      Real.exp (1 / 8 : ℝ) ≤ (11331484531 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 8 : ℝ))
    (a := (1133148453 / 1000000000 : ℝ)) (b := (11331484531 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_463 :
    (18682459 / 10000000 : ℝ) ≤ Real.exp (5 / 8 : ℝ) ∧
    Real.exp (5 / 8 : ℝ) ≤ (934123 / 500000 : ℝ) := by
  have hsmall : (101972323271377 / 100000000000000 : ℝ) ≤ Real.exp (5 / 256 : ℝ) ∧
      Real.exp (5 / 256 : ℝ) ≤ (50986161635689 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (5 / 256 : ℝ))
    (a := (101972323271377 / 100000000000000 : ℝ)) (b := (50986161635689 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_464 :
    (28249 / 10000000 : ℝ) ≤ Real.exp (-(29346343 / 5000000 : ℝ)) ∧
    Real.exp (-(29346343 / 5000000 : ℝ)) ≤ (113 / 40000 : ℝ) := by
  have hsmall : (2402624843 / 2000000000 : ℝ) ≤ Real.exp (29346343 / 160000000 : ℝ) ∧
      Real.exp (29346343 / 160000000 : ℝ) ≤ (1501640527 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29346343 / 160000000 : ℝ))
    (a := (2402624843 / 2000000000 : ℝ)) (b := (1501640527 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_465 :
    (28151 / 5000000 : ℝ) ≤ Real.exp (-(51796093 / 10000000 : ℝ)) ∧
    Real.exp (-(51796093 / 10000000 : ℝ)) ≤ (56303 / 10000000 : ℝ) := by
  have hsmall : (11756989133 / 10000000000 : ℝ) ≤ Real.exp (51796093 / 320000000 : ℝ) ∧
      Real.exp (51796093 / 320000000 : ℝ) ≤ (5878494567 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51796093 / 320000000 : ℝ))
    (a := (11756989133 / 10000000000 : ℝ)) (b := (5878494567 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_466 :
    (109367 / 10000000 : ℝ) ≤ Real.exp (-(289 / 64 : ℝ)) ∧
    Real.exp (-(289 / 64 : ℝ)) ≤ (13671 / 1250000 : ℝ) := by
  have hsmall : (11515550901 / 10000000000 : ℝ) ≤ Real.exp (289 / 2048 : ℝ) ∧
      Real.exp (289 / 2048 : ℝ) ≤ (5757775451 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (289 / 2048 : ℝ))
    (a := (11515550901 / 10000000000 : ℝ)) (b := (5757775451 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_467 :
    (2117 / 1000 : ℝ) ≤ Real.exp (3 / 4 : ℝ) ∧
    Real.exp (3 / 4 : ℝ) ≤ (21170001 / 10000000 : ℝ) := by
  have hsmall : (20474286332047 / 20000000000000 : ℝ) ≤ Real.exp (3 / 128 : ℝ) ∧
      Real.exp (3 / 128 : ℝ) ≤ (25592857915059 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (3 / 128 : ℝ))
    (a := (20474286332047 / 20000000000000 : ℝ)) (b := (25592857915059 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_468 :
    (1293 / 1000000 : ℝ) ≤ Real.exp (-(66507527 / 10000000 : ℝ)) ∧
    Real.exp (-(66507527 / 10000000 : ℝ)) ≤ (12931 / 10000000 : ℝ) := by
  have hsmall : (615505647 / 500000000 : ℝ) ≤ Real.exp (66507527 / 320000000 : ℝ) ∧
      Real.exp (66507527 / 320000000 : ℝ) ≤ (12310112941 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (66507527 / 320000000 : ℝ))
    (a := (615505647 / 500000000 : ℝ)) (b := (12310112941 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_469 :
    (28249 / 10000000 : ℝ) ≤ Real.exp (-(58692663 / 10000000 : ℝ)) ∧
    Real.exp (-(58692663 / 10000000 : ℝ)) ≤ (113 / 40000 : ℝ) := by
  have hsmall : (12013123351 / 10000000000 : ℝ) ≤ Real.exp (58692663 / 320000000 : ℝ) ∧
      Real.exp (58692663 / 320000000 : ℝ) ≤ (1501640419 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (58692663 / 320000000 : ℝ))
    (a := (12013123351 / 10000000000 : ℝ)) (b := (1501640419 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_470 :
    (63297 / 10000000 : ℝ) ≤ Real.exp (-(81 / 16 : ℝ)) ∧
    Real.exp (-(81 / 16 : ℝ)) ≤ (31649 / 5000000 : ℝ) := by
  have hsmall : (73212757 / 62500000 : ℝ) ≤ Real.exp (81 / 512 : ℝ) ∧
      Real.exp (81 / 512 : ℝ) ≤ (11714041121 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (81 / 512 : ℝ))
    (a := (73212757 / 62500000 : ℝ)) (b := (11714041121 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_471 :
    (44217711 / 5000000 : ℝ) ≤ Real.exp (279 / 128 : ℝ) ∧
    Real.exp (279 / 128 : ℝ) ≤ (88435423 / 10000000 : ℝ) := by
  have hsmall : (53524432923153 / 50000000000000 : ℝ) ≤ Real.exp (279 / 4096 : ℝ) ∧
      Real.exp (279 / 4096 : ℝ) ≤ (107048865846307 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (279 / 4096 : ℝ))
    (a := (53524432923153 / 50000000000000 : ℝ)) (b := (107048865846307 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_472 :
    (391 / 2000000 : ℝ) ≤ Real.exp (-(42698677 / 5000000 : ℝ)) ∧
    Real.exp (-(42698677 / 5000000 : ℝ)) ≤ (489 / 2500000 : ℝ) := by
  have hsmall : (2611732807 / 2000000000 : ℝ) ≤ Real.exp (42698677 / 160000000 : ℝ) ∧
      Real.exp (42698677 / 160000000 : ℝ) ≤ (3264666009 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (42698677 / 160000000 : ℝ))
    (a := (2611732807 / 2000000000 : ℝ)) (b := (3264666009 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_473 :
    (1293 / 1000000 : ℝ) ≤ Real.exp (-(33253751 / 5000000 : ℝ)) ∧
    Real.exp (-(33253751 / 5000000 : ℝ)) ≤ (12931 / 10000000 : ℝ) := by
  have hsmall : (12310111979 / 10000000000 : ℝ) ≤ Real.exp (33253751 / 160000000 : ℝ) ∧
      Real.exp (33253751 / 160000000 : ℝ) ≤ (615505599 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (33253751 / 160000000 : ℝ))
    (a := (12310111979 / 10000000000 : ℝ)) (b := (615505599 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_474 :
    (2413 / 1250000 : ℝ) ≤ Real.exp (-(25 / 4 : ℝ)) ∧
    Real.exp (-(25 / 4 : ℝ)) ≤ (3861 / 2000000 : ℝ) := by
  have hsmall : (2431381661 / 2000000000 : ℝ) ≤ Real.exp (25 / 128 : ℝ) ∧
      Real.exp (25 / 128 : ℝ) ≤ (6078454153 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 128 : ℝ))
    (a := (2431381661 / 2000000000 : ℝ)) (b := (6078454153 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_475 :
    (2253393 / 200000 : ℝ) ≤ Real.exp (155 / 64 : ℝ) ∧
    Real.exp (155 / 64 : ℝ) ≤ (112669651 / 10000000 : ℝ) := by
  have hsmall : (21572424753173 / 20000000000000 : ℝ) ≤ Real.exp (155 / 2048 : ℝ) ∧
      Real.exp (155 / 2048 : ℝ) ≤ (53931061882933 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (155 / 2048 : ℝ))
    (a := (21572424753173 / 20000000000000 : ℝ)) (b := (53931061882933 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_476 :
    (4481689 / 1000000 : ℝ) ≤ Real.exp (3 / 2 : ℝ) ∧
    Real.exp (3 / 2 : ℝ) ≤ (44816891 / 10000000 : ℝ) := by
  have hsmall : (104799100201663 / 100000000000000 : ℝ) ≤ Real.exp (3 / 64 : ℝ) ∧
      Real.exp (3 / 64 : ℝ) ≤ (1637485940651 / 1562500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (3 / 64 : ℝ))
    (a := (104799100201663 / 100000000000000 : ℝ)) (b := (1637485940651 / 1562500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_477 :
    (7 / 10000000 : ℝ) ≤ Real.exp (-(8799777 / 625000 : ℝ)) ∧
    Real.exp (-(8799777 / 625000 : ℝ)) ≤ (1 / 1250000 : ℝ) := by
  have hsmall : (15526899057 / 10000000000 : ℝ) ≤ Real.exp (8799777 / 20000000 : ℝ) ∧
      Real.exp (8799777 / 20000000 : ℝ) ≤ (776344953 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8799777 / 20000000 : ℝ))
    (a := (15526899057 / 10000000000 : ℝ)) (b := (776344953 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_478 :
    (391 / 2000000 : ℝ) ≤ Real.exp (-(85397323 / 10000000 : ℝ)) ∧
    Real.exp (-(85397323 / 10000000 : ℝ)) ≤ (489 / 2500000 : ℝ) := by
  have hsmall : (1305866277 / 1000000000 : ℝ) ≤ Real.exp (85397323 / 320000000 : ℝ) ∧
      Real.exp (85397323 / 320000000 : ℝ) ≤ (13058662771 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (85397323 / 320000000 : ℝ))
    (a := (1305866277 / 1000000000 : ℝ)) (b := (13058662771 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_479 :
    (617 / 5000000 : ℝ) ≤ Real.exp (-(9 / 1 : ℝ)) ∧
    Real.exp (-(9 / 1 : ℝ)) ≤ (247 / 2000000 : ℝ) := by
  have hsmall : (13247847587 / 10000000000 : ℝ) ≤ Real.exp (9 / 32 : ℝ) ∧
      Real.exp (9 / 32 : ℝ) ≤ (3311961897 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 32 : ℝ))
    (a := (13247847587 / 10000000000 : ℝ)) (b := (3311961897 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_480 :
    (91440447 / 5000000 : ℝ) ≤ Real.exp (93 / 32 : ℝ) ∧
    Real.exp (93 / 32 : ℝ) ≤ (36576179 / 2000000 : ℝ) := by
  have hsmall : (54753610839491 / 50000000000000 : ℝ) ≤ Real.exp (93 / 1024 : ℝ) ∧
      Real.exp (93 / 1024 : ℝ) ≤ (109507221678983 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 1024 : ℝ))
    (a := (54753610839491 / 50000000000000 : ℝ)) (b := (109507221678983 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_481 :
    (121824939 / 10000000 : ℝ) ≤ Real.exp (5 / 2 : ℝ) ∧
    Real.exp (5 / 2 : ℝ) ≤ (6091247 / 500000 : ℝ) := by
  have hsmall : (108125780744903 / 100000000000000 : ℝ) ≤ Real.exp (5 / 64 : ℝ) ∧
      Real.exp (5 / 64 : ℝ) ≤ (13515722593113 / 12500000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (5 / 64 : ℝ))
    (a := (108125780744903 / 100000000000000 : ℝ)) (b := (13515722593113 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_482 :
    (0 : ℝ) ≤ Real.exp (-(382724379 / 10000000 : ℝ)) ∧
    Real.exp (-(382724379 / 10000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_483 :
    (7 / 10000000 : ℝ) ≤ Real.exp (-(140796383 / 10000000 : ℝ)) ∧
    Real.exp (-(140796383 / 10000000 : ℝ)) ≤ (1 / 1250000 : ℝ) := by
  have hsmall : (388172417 / 250000000 : ℝ) ≤ Real.exp (140796383 / 320000000 : ℝ) ∧
      Real.exp (140796383 / 320000000 : ℝ) ≤ (7763448341 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (140796383 / 320000000 : ℝ))
    (a := (388172417 / 250000000 : ℝ)) (b := (7763448341 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_484 :
    (1 / 10000000 : ℝ) ≤ Real.exp (-(16 / 1 : ℝ)) ∧
    Real.exp (-(16 / 1 : ℝ)) ≤ (1 / 5000000 : ℝ) := by
  have hsmall : (16487212701 / 10000000000 : ℝ) ≤ Real.exp (1 / 2 : ℝ) ∧
      Real.exp (1 / 2 : ℝ) ≤ (4121803177 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 2 : ℝ))
    (a := (16487212701 / 10000000000 : ℝ)) (b := (4121803177 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_485 :
    (900171313 / 10000000 : ℝ) ≤ Real.exp (9 / 2 : ℝ) ∧
    Real.exp (9 / 2 : ℝ) ≤ (450085657 / 5000000 : ℝ) := by
  have hsmall : (115099294469117 / 100000000000000 : ℝ) ≤ Real.exp (9 / 64 : ℝ) ∧
      Real.exp (9 / 64 : ℝ) ≤ (57549647234559 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (9 / 64 : ℝ))
    (a := (115099294469117 / 100000000000000 : ℝ)) (b := (57549647234559 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_486 :
    (0 : ℝ) ≤ Real.exp (-(2827971899 / 10000000 : ℝ)) ∧
    Real.exp (-(2827971899 / 10000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_487 :
    (0 : ℝ) ≤ Real.exp (-(382724253 / 10000000 : ℝ)) ∧
    Real.exp (-(382724253 / 10000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_488 :
    (0 : ℝ) ≤ Real.exp (-(36 / 1 : ℝ)) ∧
    Real.exp (-(36 / 1 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_489 :
    (3344542169 / 10000000 : ℝ) ≤ Real.exp (93 / 16 : ℝ) ∧
    Real.exp (93 / 16 : ℝ) ≤ (334454217 / 1000000 : ℝ) := by
  have hsmall : (59959157999249 / 50000000000000 : ℝ) ≤ Real.exp (93 / 512 : ℝ) ∧
      Real.exp (93 / 512 : ℝ) ≤ (119918315998499 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 512 : ℝ))
    (a := (59959157999249 / 50000000000000 : ℝ)) (b := (119918315998499 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_490 :
    (665141633 / 1000000 : ℝ) ≤ Real.exp (13 / 2 : ℝ) ∧
    Real.exp (13 / 2 : ℝ) ≤ (6651416331 / 10000000 : ℝ) := by
  have hsmall : (12252256118773 / 10000000000000 : ℝ) ≤ Real.exp (13 / 64 : ℝ) ∧
      Real.exp (13 / 64 : ℝ) ≤ (122522561187731 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (13 / 64 : ℝ))
    (a := (12252256118773 / 10000000000000 : ℝ)) (b := (122522561187731 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_491 :
    (0 : ℝ) ≤ Real.exp (-(10448021493 / 5000000 : ℝ)) ∧
    Real.exp (-(10448021493 / 5000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_492 :
    (0 : ℝ) ≤ Real.exp (-(565594199 / 2000000 : ℝ)) ∧
    Real.exp (-(565594199 / 2000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_493 :
    (11607862073 / 5000000 : ℝ) ≤ Real.exp (31 / 4 : ℝ) ∧
    Real.exp (31 / 4 : ℝ) ≤ (23215724147 / 10000000 : ℝ) := by
  have hsmall : (63701652580983 / 50000000000000 : ℝ) ≤ Real.exp (31 / 128 : ℝ) ∧
      Real.exp (31 / 128 : ℝ) ≤ (127403305161967 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 128 : ℝ))
    (a := (63701652580983 / 50000000000000 : ℝ)) (b := (127403305161967 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


end MasulloRH.HeightOneExponentialProof

theorem solution :
  ∀ i : Fin 494,
    ((MasulloRH.HeightOneExponentialTable.entry i).2.1 : ℝ) ≤
      Real.exp ((MasulloRH.HeightOneExponentialTable.entry i).1 : ℝ) ∧
    Real.exp ((MasulloRH.HeightOneExponentialTable.entry i).1 : ℝ) ≤
      ((MasulloRH.HeightOneExponentialTable.entry i).2.2 : ℝ) := by
  intro i
  fin_cases i
  · change ((1570953301 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((23 / 4 : ℚ) : ℝ) ∧ Real.exp ((23 / 4 : ℚ) : ℝ) ≤ ((3141906603 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_000 using 1 <;> norm_num
  · change ((16699658537 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((19 / 2 : ℚ) : ℝ) ∧ Real.exp ((19 / 2 : ℚ) : ℝ) ≤ ((133597268297 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_001 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-13115882591 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-13115882591 / 5000000 : ℚ) : ℝ) ≤ ((1 / 1048576 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_002 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-61691179 / 1000000 : ℚ) : ℝ) ∧ Real.exp ((-61691179 / 1000000 : ℚ) : ℝ) ≤ ((1 / 1048576 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_003 using 1 <;> norm_num
  · change ((177254241 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((23 / 8 : ℚ) : ℝ) ∧ Real.exp ((23 / 8 : ℚ) : ℝ) ≤ ((88627121 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_004 using 1 <;> norm_num
  · change ((231168569 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((19 / 4 : ℚ) : ℝ) ∧ Real.exp ((19 / 4 : ℚ) : ℝ) ≤ ((577921423 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_005 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-64 / 1 : ℚ) : ℝ) ∧ Real.exp ((-64 / 1 : ℚ) : ℝ) ≤ ((1 / 1048576 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_006 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-289 / 16 : ℚ) : ℝ) ∧ Real.exp ((-289 / 16 : ℚ) : ℝ) ≤ ((1 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_007 using 1 <;> norm_num
  · change ((104579 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-289 / 128 : ℚ) : ℝ) ∧ Real.exp ((-289 / 128 : ℚ) : ℝ) ≤ ((1045791 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_008 using 1 <;> norm_num
  · change ((240913491 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((31 / 8 : ℚ) : ℝ) ∧ Real.exp ((31 / 8 : ℚ) : ℝ) ≤ ((481826983 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_009 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-616911987 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-616911987 / 10000000 : ℚ) : ℝ) ≤ ((1 / 1048576 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_010 using 1 <;> norm_num
  · change ((389 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-94606487 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-94606487 / 10000000 : ℚ) : ℝ) ≤ ((779 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_011 using 1 <;> norm_num
  · change ((34706879 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((31 / 16 : ℚ) : ℝ) ∧ Real.exp ((31 / 16 : ℚ) : ℝ) ≤ ((69413759 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_012 using 1 <;> norm_num
  · change ((17753 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-361 / 64 : ℚ) : ℝ) ∧ Real.exp ((-361 / 64 : ℚ) : ℝ) ≤ ((35507 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_013 using 1 <;> norm_num
  · change ((2831669 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-323 / 256 : ℚ) : ℝ) ∧ Real.exp ((-323 / 256 : ℚ) : ℝ) ≤ ((283167 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_014 using 1 <;> norm_num
  · change ((301519621 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((109 / 32 : ℚ) : ℝ) ∧ Real.exp ((109 / 32 : ℚ) : ℝ) ≤ ((150759811 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_015 using 1 <;> norm_num
  · change ((389 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-47303259 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-47303259 / 5000000 : ℚ) : ℝ) ≤ ((779 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_016 using 1 <;> norm_num
  · change ((26843 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-29601613 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-29601613 / 5000000 : ℚ) : ℝ) ≤ ((6711 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_017 using 1 <;> norm_num
  · change ((27455401 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((109 / 64 : ℚ) : ℝ) ∧ Real.exp ((109 / 64 : ℚ) : ℝ) ≤ ((54910803 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_018 using 1 <;> norm_num
  · change ((264159 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-3721 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-3721 / 1024 : ℚ) : ℝ) ≤ ((1651 / 62500 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_019 using 1 <;> norm_num
  · change ((1816193 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-1037 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-1037 / 1024 : ℚ) : ℝ) ≤ ((3632387 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_020 using 1 <;> norm_num
  · change ((59630413 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((203 / 64 : ℚ) : ℝ) ∧ Real.exp ((203 / 64 : ℚ) : ℝ) ≤ ((238521653 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_021 using 1 <;> norm_num
  · change ((26843 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-29601623 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-29601623 / 5000000 : ℚ) : ℝ) ≤ ((6711 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_022 using 1 <;> norm_num
  · change ((46239 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-46833607 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-46833607 / 10000000 : ℚ) : ℝ) ≤ ((92479 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_023 using 1 <;> norm_num
  · change ((24419339 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((203 / 128 : ℚ) : ℝ) ∧ Real.exp ((203 / 128 : ℚ) : ℝ) ≤ ((48838679 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_024 using 1 <;> norm_num
  · change ((611047 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-11449 / 4096 : ℚ) : ℝ) ∧ Real.exp ((-11449 / 4096 : ℚ) : ℝ) ≤ ((76381 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_025 using 1 <;> norm_num
  · change ((4114023 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1819 / 2048 : ℚ) : ℝ) ∧ Real.exp ((-1819 / 2048 : ℚ) : ℝ) ≤ ((514253 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_026 using 1 <;> norm_num
  · change ((212145549 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((391 / 128 : ℚ) : ℝ) ∧ Real.exp ((391 / 128 : ℚ) : ℝ) ≤ ((4242911 / 200000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_027 using 1 <;> norm_num
  · change ((46239 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-46833623 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-46833623 / 10000000 : ℚ) : ℝ) ≤ ((92479 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_028 using 1 <;> norm_num
  · change ((19403 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-2603417 / 625000 : ℚ) : ℝ) ∧ Real.exp ((-2603417 / 625000 : ℚ) : ℝ) ≤ ((6209 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_029 using 1 <;> norm_num
  · change ((2302963 / 500000 : ℚ) : ℝ) ≤ Real.exp ((391 / 256 : ℚ) : ℝ) ∧ Real.exp ((391 / 256 : ℚ) : ℝ) ≤ ((46059261 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_030 using 1 <;> norm_num
  · change ((2787 / 31250 : ℚ) : ℝ) ≤ Real.exp ((-39601 / 16384 : ℚ) : ℝ) ∧ Real.exp ((-39601 / 16384 : ℚ) : ℝ) ≤ ((891841 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_031 using 1 <;> norm_num
  · change ((2189143 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-3383 / 4096 : ℚ) : ℝ) ∧ Real.exp ((-3383 / 4096 : ℚ) : ℝ) ≤ ((4378287 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_032 using 1 <;> norm_num
  · change ((188686157 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((47 / 16 : ℚ) : ℝ) ∧ Real.exp ((47 / 16 : ℚ) : ℝ) ≤ ((94343079 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_033 using 1 <;> norm_num
  · change ((19403 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-20827343 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-20827343 / 5000000 : ℚ) : ℝ) ≤ ((6209 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_034 using 1 <;> norm_num
  · change ((6151 / 250000 : ℚ) : ℝ) ≤ Real.exp ((-2315527 / 625000 : ℚ) : ℝ) ∧ Real.exp ((-2315527 / 625000 : ℚ) : ℝ) ≤ ((246041 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_035 using 1 <;> norm_num
  · change ((43438019 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((47 / 32 : ℚ) : ℝ) ∧ Real.exp ((47 / 32 : ℚ) : ℝ) ≤ ((2171901 / 500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_036 using 1 <;> norm_num
  · change ((1583 / 12500 : ℚ) : ℝ) ≤ Real.exp ((-529 / 256 : ℚ) : ℝ) ∧ Real.exp ((-529 / 256 : ℚ) : ℝ) ≤ ((1266401 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_037 using 1 <;> norm_num
  · change ((4659523 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-391 / 512 : ℚ) : ℝ) ∧ Real.exp ((-391 / 512 : ℚ) : ℝ) ≤ ((1164881 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_038 using 1 <;> norm_num
  · change ((83910471 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((361 / 128 : ℚ) : ℝ) ∧ Real.exp ((361 / 128 : ℚ) : ℝ) ≤ ((167820943 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_039 using 1 <;> norm_num
  · change ((6151 / 250000 : ℚ) : ℝ) ≤ Real.exp ((-7409689 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-7409689 / 2000000 : ℚ) : ℝ) ≤ ((246041 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_040 using 1 <;> norm_num
  · change ((185311 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-16475779 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-16475779 / 5000000 : ℚ) : ℝ) ≤ ((370623 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_041 using 1 <;> norm_num
  · change ((20482977 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((361 / 256 : ℚ) : ℝ) ∧ Real.exp ((361 / 256 : ℚ) : ℝ) ≤ ((8193191 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_042 using 1 <;> norm_num
  · change ((109347 / 625000 : ℚ) : ℝ) ≤ Real.exp ((-28561 / 16384 : ℚ) : ℝ) ∧ Real.exp ((-28561 / 16384 : ℚ) : ℝ) ≤ ((1749553 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_043 using 1 <;> norm_num
  · change ((2479413 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-2873 / 4096 : ℚ) : ℝ) ∧ Real.exp ((-2873 / 4096 : ℚ) : ℝ) ≤ ((4958827 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_044 using 1 <;> norm_num
  · change ((79135111 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((707 / 256 : ℚ) : ℝ) ∧ Real.exp ((707 / 256 : ℚ) : ℝ) ≤ ((158270223 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_045 using 1 <;> norm_num
  · change ((185311 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-32951569 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-32951569 / 10000000 : ℚ) : ℝ) ≤ ((370623 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_046 using 1 <;> norm_num
  · change ((111767 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-15538139 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-15538139 / 5000000 : ℚ) : ℝ) ≤ ((447069 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_047 using 1 <;> norm_num
  · change ((3978319 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((707 / 512 : ℚ) : ℝ) ∧ Real.exp ((707 / 512 : ℚ) : ℝ) ≤ ((39783191 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_048 using 1 <;> norm_num
  · change ((407063 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-104329 / 65536 : ℚ) : ℝ) ∧ Real.exp ((-104329 / 65536 : ℚ) : ℝ) ≤ ((508829 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_049 using 1 <;> norm_num
  · change ((5115611 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-5491 / 8192 : ℚ) : ℝ) ∧ Real.exp ((-5491 / 8192 : ℚ) : ℝ) ≤ ((1278903 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_050 using 1 <;> norm_num
  · change ((37315759 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((173 / 64 : ℚ) : ℝ) ∧ Real.exp ((173 / 64 : ℚ) : ℝ) ≤ ((149263037 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_051 using 1 <;> norm_num
  · change ((111767 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-3107629 / 1000000 : ℚ) : ℝ) ∧ Real.exp ((-3107629 / 1000000 : ℚ) : ℝ) ≤ ((447069 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_052 using 1 <;> norm_num
  · change ((266779 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-14653861 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-14653861 / 5000000 : ℚ) : ℝ) ≤ ((533559 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_053 using 1 <;> norm_num
  · change ((19317287 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((173 / 128 : ℚ) : ℝ) ∧ Real.exp ((173 / 128 : ℚ) : ℝ) ≤ ((1545383 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_054 using 1 <;> norm_num
  · change ((2351551 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-5929 / 4096 : ℚ) : ℝ) ∧ Real.exp ((-5929 / 4096 : ℚ) : ℝ) ≤ ((36743 / 156250 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_055 using 1 <;> norm_num
  · change ((2638677 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-1309 / 2048 : ℚ) : ℝ) ∧ Real.exp ((-1309 / 2048 : ℚ) : ℝ) ≤ ((1055471 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_056 using 1 <;> norm_num
  · change ((2815369 / 200000 : ℚ) : ℝ) ≤ Real.exp ((677 / 256 : ℚ) : ℝ) ∧ Real.exp ((677 / 256 : ℚ) : ℝ) ≤ ((140768451 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_057 using 1 <;> norm_num
  · change ((533557 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-29307733 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-29307733 / 10000000 : ℚ) : ℝ) ≤ ((266779 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_058 using 1 <;> norm_num
  · change ((315201 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-13819907 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-13819907 / 5000000 : ℚ) : ℝ) ≤ ((630403 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_059 using 1 <;> norm_num
  · change ((37519121 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((677 / 512 : ℚ) : ℝ) ∧ Real.exp ((677 / 512 : ℚ) : ℝ) ≤ ((18759561 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_060 using 1 <;> norm_num
  · change ((269833 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-85849 / 65536 : ℚ) : ℝ) ∧ Real.exp ((-85849 / 65536 : ℚ) : ℝ) ≤ ((2698331 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_061 using 1 <;> norm_num
  · change ((5444211 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-4981 / 8192 : ℚ) : ℝ) ∧ Real.exp ((-4981 / 8192 : ℚ) : ℝ) ≤ ((1361053 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_062 using 1 <;> norm_num
  · change ((33189323 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((331 / 128 : ℚ) : ℝ) ∧ Real.exp ((331 / 128 : ℚ) : ℝ) ≤ ((132757293 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_063 using 1 <;> norm_num
  · change ((315201 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-1727489 / 625000 : ℚ) : ℝ) ∧ Real.exp ((-1727489 / 625000 : ℚ) : ℝ) ≤ ((630403 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_064 using 1 <;> norm_num
  · change ((184447 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-26066827 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-26066827 / 10000000 : ℚ) : ℝ) ≤ ((737789 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_065 using 1 <;> norm_num
  · change ((18217937 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((331 / 256 : ℚ) : ℝ) ∧ Real.exp ((331 / 256 : ℚ) : ℝ) ≤ ((291487 / 80000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_066 using 1 <;> norm_num
  · change ((3075061 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-19321 / 16384 : ℚ) : ℝ) ∧ Real.exp ((-19321 / 16384 : ℚ) : ℝ) ≤ ((1537531 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_067 using 1 <;> norm_num
  · change ((5616343 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-2363 / 4096 : ℚ) : ℝ) ∧ Real.exp ((-2363 / 4096 : ℚ) : ℝ) ≤ ((702043 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_068 using 1 <;> norm_num
  · change ((125202051 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((647 / 256 : ℚ) : ℝ) ∧ Real.exp ((647 / 256 : ℚ) : ℝ) ≤ ((31300513 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_069 using 1 <;> norm_num
  · change ((184447 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-26066837 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-26066837 / 10000000 : ℚ) : ℝ) ≤ ((737789 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_070 using 1 <;> norm_num
  · change ((213943 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-76823 / 31250 : ℚ) : ℝ) ∧ Real.exp ((-76823 / 31250 : ℚ) : ℝ) ≤ ((855773 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_071 using 1 <;> norm_num
  · change ((35383901 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((647 / 512 : ℚ) : ℝ) ∧ Real.exp ((647 / 512 : ℚ) : ℝ) ≤ ((17691951 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_072 using 1 <;> norm_num
  · change ((3480409 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-69169 / 65536 : ℚ) : ℝ) ∧ Real.exp ((-69169 / 65536 : ℚ) : ℝ) ≤ ((348041 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_073 using 1 <;> norm_num
  · change ((5793917 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-4471 / 8192 : ℚ) : ℝ) ∧ Real.exp ((-4471 / 8192 : ℚ) : ℝ) ≤ ((2896959 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_074 using 1 <;> norm_num
  · change ((5903839 / 500000 : ℚ) : ℝ) ≤ Real.exp ((79 / 32 : ℚ) : ℝ) ∧ Real.exp ((79 / 32 : ℚ) : ℝ) ≤ ((118076781 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_075 using 1 <;> norm_num
  · change ((855771 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-24583369 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-24583369 / 10000000 : ℚ) : ℝ) ≤ ((213943 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_076 using 1 <;> norm_num
  · change ((492139 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-5796079 / 2500000 : ℚ) : ℝ) ∧ Real.exp ((-5796079 / 2500000 : ℚ) : ℝ) ≤ ((984279 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_077 using 1 <;> norm_num
  · change ((17181151 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((79 / 64 : ℚ) : ℝ) ∧ Real.exp ((79 / 64 : ℚ) : ℝ) ≤ ((34362303 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_078 using 1 <;> norm_num
  · change ((3912233 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-961 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-961 / 1024 : ℚ) : ℝ) ≤ ((1956117 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_079 using 1 <;> norm_num
  · change ((2988553 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-527 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-527 / 1024 : ℚ) : ℝ) ≤ ((5977107 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_080 using 1 <;> norm_num
  · change ((111357009 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((617 / 256 : ℚ) : ℝ) ∧ Real.exp ((617 / 256 : ℚ) : ℝ) ≤ ((11135701 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_081 using 1 <;> norm_num
  · change ((984277 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-927373 / 400000 : ℚ) : ℝ) ∧ Real.exp ((-927373 / 400000 : ℚ) : ℝ) ≤ ((492139 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_082 using 1 <;> norm_num
  · change ((1123103 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-21864893 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-21864893 / 10000000 : ℚ) : ℝ) ≤ ((35097 / 312500 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_083 using 1 <;> norm_num
  · change ((33370197 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((617 / 512 : ℚ) : ℝ) ∧ Real.exp ((617 / 512 : ℚ) : ℝ) ≤ ((16685099 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_084 using 1 <;> norm_num
  · change ((4367543 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-54289 / 65536 : ℚ) : ℝ) ∧ Real.exp ((-54289 / 65536 : ℚ) : ℝ) ≤ ((545943 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_085 using 1 <;> norm_num
  · change ((6166087 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-3961 / 8192 : ℚ) : ℝ) ∧ Real.exp ((-3961 / 8192 : ℚ) : ℝ) ≤ ((770761 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_086 using 1 <;> norm_num
  · change ((52509831 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((301 / 128 : ℚ) : ℝ) ∧ Real.exp ((301 / 128 : ℚ) : ℝ) ≤ ((105019663 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_087 using 1 <;> norm_num
  · change ((561551 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-21864901 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-21864901 / 10000000 : ℚ) : ℝ) ≤ ((1123103 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_088 using 1 <;> norm_num
  · change ((635961 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-10310279 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-10310279 / 5000000 : ℚ) : ℝ) ≤ ((1271923 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_089 using 1 <;> norm_num
  · change ((32406737 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((301 / 256 : ℚ) : ℝ) ∧ Real.exp ((301 / 256 : ℚ) : ℝ) ≤ ((16203369 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_090 using 1 <;> norm_num
  · change ((4842477 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-11881 / 16384 : ℚ) : ℝ) ∧ Real.exp ((-11881 / 16384 : ℚ) : ℝ) ≤ ((2421239 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_091 using 1 <;> norm_num
  · change ((6361043 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1853 / 4096 : ℚ) : ℝ) ∧ Real.exp ((-1853 / 4096 : ℚ) : ℝ) ≤ ((1272209 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_092 using 1 <;> norm_num
  · change ((49521487 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((587 / 256 : ℚ) : ℝ) ∧ Real.exp ((587 / 256 : ℚ) : ℝ) ≤ ((3961719 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_093 using 1 <;> norm_num
  · change ((1271921 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-4124113 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-4124113 / 2000000 : ℚ) : ℝ) ≤ ((635961 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_094 using 1 <;> norm_num
  · change ((286059 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-9723519 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-9723519 / 5000000 : ℚ) : ℝ) ≤ ((178787 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_095 using 1 <;> norm_num
  · change ((31471093 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((587 / 512 : ℚ) : ℝ) ∧ Real.exp ((587 / 512 : ℚ) : ℝ) ≤ ((15735547 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_096 using 1 <;> norm_num
  · change ((1066463 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-41209 / 65536 : ℚ) : ℝ) ∧ Real.exp ((-41209 / 65536 : ℚ) : ℝ) ≤ ((1333079 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_097 using 1 <;> norm_num
  · change ((1640541 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-3451 / 8192 : ℚ) : ℝ) ∧ Real.exp ((-3451 / 8192 : ℚ) : ℝ) ≤ ((1312433 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_098 using 1 <;> norm_num
  · change ((96183417 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((1159 / 512 : ℚ) : ℝ) ∧ Real.exp ((1159 / 512 : ℚ) : ℝ) ≤ ((48091709 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_099 using 1 <;> norm_num
  · change ((715147 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-3889409 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-3889409 / 2000000 : ℚ) : ℝ) ≤ ((286059 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_100 using 1 <;> norm_num
  · change ((15129 / 100000 : ℚ) : ℝ) ≤ Real.exp ((-3777113 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-3777113 / 2000000 : ℚ) : ℝ) ≤ ((1512901 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_101 using 1 <;> norm_num
  · change ((31013451 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((1159 / 1024 : ℚ) : ℝ) ∧ Real.exp ((1159 / 1024 : ℚ) : ℝ) ≤ ((7753363 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_102 using 1 <;> norm_num
  · change ((1395281 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-152881 / 262144 : ℚ) : ℝ) ∧ Real.exp ((-152881 / 262144 : ℚ) : ℝ) ≤ ((44649 / 80000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_103 using 1 <;> norm_num
  · change ((833137 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-6647 / 16384 : ℚ) : ℝ) ∧ Real.exp ((-6647 / 16384 : ℚ) : ℝ) ≤ ((6665097 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_104 using 1 <;> norm_num
  · change ((93406421 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((143 / 64 : ℚ) : ℝ) ∧ Real.exp ((143 / 64 : ℚ) : ℝ) ≤ ((46703211 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_105 using 1 <;> norm_num
  · change ((1512899 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-18885573 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-18885573 / 10000000 : ℚ) : ℝ) ≤ ((15129 / 100000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_106 using 1 <;> norm_num
  · change ((1597683 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1146269 / 625000 : ℚ) : ℝ) ∧ Real.exp ((-1146269 / 625000 : ℚ) : ℝ) ≤ ((399421 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_107 using 1 <;> norm_num
  · change ((955077 / 312500 : ℚ) : ℝ) ≤ Real.exp ((143 / 128 : ℚ) : ℝ) ∧ Real.exp ((143 / 128 : ℚ) : ℝ) ≤ ((6112493 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_108 using 1 <;> norm_num
  · change ((1457881 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-2209 / 4096 : ℚ) : ℝ) ∧ Real.exp ((-2209 / 4096 : ℚ) : ℝ) ≤ ((233261 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_109 using 1 <;> norm_num
  · change ((6769643 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-799 / 2048 : ℚ) : ℝ) ∧ Real.exp ((-799 / 2048 : ℚ) : ℝ) ≤ ((1692411 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_110 using 1 <;> norm_num
  · change ((45354801 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((1129 / 512 : ℚ) : ℝ) ∧ Real.exp ((1129 / 512 : ℚ) : ℝ) ≤ ((90709603 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_111 using 1 <;> norm_num
  · change ((798841 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-18340311 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-18340311 / 10000000 : ℚ) : ℝ) ≤ ((1597683 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_112 using 1 <;> norm_num
  · change ((1684563 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-556587 / 312500 : ℚ) : ℝ) ∧ Real.exp ((-556587 / 312500 : ℚ) : ℝ) ≤ ((421141 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_113 using 1 <;> norm_num
  · change ((15059017 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((1129 / 1024 : ℚ) : ℝ) ∧ Real.exp ((1129 / 1024 : ℚ) : ℝ) ≤ ((6023607 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_114 using 1 <;> norm_num
  · change ((6082707 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-130321 / 262144 : ℚ) : ℝ) ∧ Real.exp ((-130321 / 262144 : ℚ) : ℝ) ≤ ((1520677 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_115 using 1 <;> norm_num
  · change ((6875829 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-6137 / 16384 : ℚ) : ℝ) ∧ Real.exp ((-6137 / 16384 : ℚ) : ℝ) ≤ ((687583 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_116 using 1 <;> norm_num
  · change ((17618129 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((557 / 256 : ℚ) : ℝ) ∧ Real.exp ((557 / 256 : ℚ) : ℝ) ≤ ((44045323 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_117 using 1 <;> norm_num
  · change ((842281 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-17810791 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-17810791 / 10000000 : ℚ) : ℝ) ≤ ((1684563 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_118 using 1 <;> norm_num
  · change ((354691 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-8648277 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-8648277 / 5000000 : ℚ) : ℝ) ≤ ((110841 / 625000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_119 using 1 <;> norm_num
  · change ((7420017 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((557 / 512 : ℚ) : ℝ) ∧ Real.exp ((557 / 512 : ℚ) : ℝ) ≤ ((29680069 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_120 using 1 <;> norm_num
  · change ((1583457 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-29929 / 65536 : ℚ) : ℝ) ∧ Real.exp ((-29929 / 65536 : ℚ) : ℝ) ≤ ((6333829 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_121 using 1 <;> norm_num
  · change ((3491841 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-2941 / 8192 : ℚ) : ℝ) ∧ Real.exp ((-2941 / 8192 : ℚ) : ℝ) ≤ ((6983683 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_122 using 1 <;> norm_num
  · change ((42773651 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((1099 / 512 : ℚ) : ℝ) ∧ Real.exp ((1099 / 512 : ℚ) : ℝ) ≤ ((85547303 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_123 using 1 <;> norm_num
  · change ((886727 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-216207 / 125000 : ℚ) : ℝ) ∧ Real.exp ((-216207 / 125000 : ℚ) : ℝ) ≤ ((354691 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_124 using 1 <;> norm_num
  · change ((1864267 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-16797169 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-16797169 / 10000000 : ℚ) : ℝ) ≤ ((466067 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_125 using 1 <;> norm_num
  · change ((2924847 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((1099 / 1024 : ℚ) : ℝ) ∧ Real.exp ((1099 / 1024 : ℚ) : ℝ) ≤ ((29248471 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_126 using 1 <;> norm_num
  · change ((6584003 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-109561 / 262144 : ℚ) : ℝ) ∧ Real.exp ((-109561 / 262144 : ℚ) : ℝ) ≤ ((1646001 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_127 using 1 <;> norm_num
  · change ((3546613 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-5627 / 16384 : ℚ) : ℝ) ∧ Real.exp ((-5627 / 16384 : ℚ) : ℝ) ≤ ((7093227 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_128 using 1 <;> norm_num
  · change ((8307739 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((271 / 128 : ℚ) : ℝ) ∧ Real.exp ((271 / 128 : ℚ) : ℝ) ≤ ((83077391 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_129 using 1 <;> norm_num
  · change ((932133 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-2099647 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-2099647 / 1250000 : ℚ) : ℝ) ≤ ((1864267 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_130 using 1 <;> norm_num
  · change ((978453 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-16312203 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-16312203 / 10000000 : ℚ) : ℝ) ≤ ((1956907 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_131 using 1 <;> norm_num
  · change ((7205787 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((271 / 256 : ℚ) : ℝ) ∧ Real.exp ((271 / 256 : ℚ) : ℝ) ≤ ((28823149 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_132 using 1 <;> norm_num
  · change ((3416161 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-6241 / 16384 : ℚ) : ℝ) ∧ Real.exp ((-6241 / 16384 : ℚ) : ℝ) ≤ ((6832323 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_133 using 1 <;> norm_num
  · change ((900561 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-1343 / 4096 : ℚ) : ℝ) ∧ Real.exp ((-1343 / 4096 : ℚ) : ℝ) ≤ ((7204489 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_134 using 1 <;> norm_num
  · change ((8067879 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((1069 / 512 : ℚ) : ℝ) ∧ Real.exp ((1069 / 512 : ℚ) : ℝ) ≤ ((80678791 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_135 using 1 <;> norm_num
  · change ((244613 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-1631221 / 1000000 : ℚ) : ℝ) ∧ Real.exp ((-1631221 / 1000000 : ℚ) : ℝ) ≤ ((391381 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_136 using 1 <;> norm_num
  · change ((1025637 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-396031 / 250000 : ℚ) : ℝ) ∧ Real.exp ((-396031 / 250000 : ℚ) : ℝ) ≤ ((82051 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_137 using 1 <;> norm_num
  · change ((7101003 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((1069 / 1024 : ℚ) : ℝ) ∧ Real.exp ((1069 / 1024 : ℚ) : ℝ) ≤ ((28404013 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_138 using 1 <;> norm_num
  · change ((3538923 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-90601 / 262144 : ℚ) : ℝ) ∧ Real.exp ((-90601 / 262144 : ℚ) : ℝ) ≤ ((7077847 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_139 using 1 <;> norm_num
  · change ((914687 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-5117 / 16384 : ℚ) : ℝ) ∧ Real.exp ((-5117 / 16384 : ℚ) : ℝ) ≤ ((7317497 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_140 using 1 <;> norm_num
  · change ((78349441 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((527 / 256 : ℚ) : ℝ) ∧ Real.exp ((527 / 256 : ℚ) : ℝ) ≤ ((39174721 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_141 using 1 <;> norm_num
  · change ((256409 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-7920623 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-7920623 / 5000000 : ℚ) : ℝ) ≤ ((2051273 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_142 using 1 <;> norm_num
  · change ((2147271 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-15383873 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-15383873 / 10000000 : ℚ) : ℝ) ≤ ((268409 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_143 using 1 <;> norm_num
  · change ((2799097 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((527 / 512 : ℚ) : ℝ) ∧ Real.exp ((527 / 512 : ℚ) : ℝ) ≤ ((27990971 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_144 using 1 <;> norm_num
  · change ((7319617 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-20449 / 65536 : ℚ) : ℝ) ∧ Real.exp ((-20449 / 65536 : ℚ) : ℝ) ≤ ((3659809 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_145 using 1 <;> norm_num
  · change ((1858069 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-2431 / 8192 : ℚ) : ℝ) ∧ Real.exp ((-2431 / 8192 : ℚ) : ℝ) ≤ ((7432277 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_146 using 1 <;> norm_num
  · change ((15217469 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((1039 / 512 : ℚ) : ℝ) ∧ Real.exp ((1039 / 512 : ℚ) : ℝ) ≤ ((38043673 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_147 using 1 <;> norm_num
  · change ((2147269 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-15383879 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-15383879 / 10000000 : ℚ) : ℝ) ≤ ((214727 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_148 using 1 <;> norm_num
  · change ((1122397 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-233433 / 156250 : ℚ) : ℝ) ∧ Real.exp ((-233433 / 156250 : ℚ) : ℝ) ≤ ((448959 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_149 using 1 <;> norm_num
  · change ((13791967 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((1039 / 1024 : ℚ) : ℝ) ∧ Real.exp ((1039 / 1024 : ℚ) : ℝ) ≤ ((5516787 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_150 using 1 <;> norm_num
  · change ((944583 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-73441 / 262144 : ℚ) : ℝ) ∧ Real.exp ((-73441 / 262144 : ℚ) : ℝ) ≤ ((1511333 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_151 using 1 <;> norm_num
  · change ((943607 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-4607 / 16384 : ℚ) : ℝ) ∧ Real.exp ((-4607 / 16384 : ℚ) : ℝ) ≤ ((7548857 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_152 using 1 <;> norm_num
  · change ((115454 / 15625 : ℚ) : ℝ) ≤ Real.exp ((2 / 1 : ℚ) : ℝ) ∧ Real.exp ((2 / 1 : ℚ) : ℝ) ≤ ((73890561 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_153 using 1 <;> norm_num
  · change ((280599 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-7469859 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-7469859 / 5000000 : ℚ) : ℝ) ≤ ((2244793 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_154 using 1 <;> norm_num
  · change ((2343739 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-7254187 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-7254187 / 5000000 : ℚ) : ℝ) ≤ ((117187 / 500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_155 using 1 <;> norm_num
  · change ((13591409 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((1 / 1 : ℚ) : ℝ) ∧ Real.exp ((1 / 1 : ℚ) : ℝ) ≤ ((27182819 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_156 using 1 <;> norm_num
  · change ((7788007 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1 / 4 : ℚ) : ℝ) ∧ Real.exp ((-1 / 4 : ℚ) : ℝ) ≤ ((973501 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_157 using 1 <;> norm_num
  · change ((1533453 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-17 / 64 : ℚ) : ℝ) ∧ Real.exp ((-17 / 64 : ℚ) : ℝ) ≤ ((3833633 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_158 using 1 <;> norm_num
  · change ((169169 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-2 / 1 : ℚ) : ℝ) ∧ Real.exp ((-2 / 1 : ℚ) : ℝ) ≤ ((1353353 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_159 using 1 <;> norm_num
  · change ((174539 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-63 / 32 : ℚ) : ℝ) ∧ Real.exp ((-63 / 32 : ℚ) : ℝ) ≤ ((1396313 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_160 using 1 <;> norm_num
  · change ((6448969 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-548331 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-548331 / 1250000 : ℚ) : ℝ) ≤ ((644897 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_161 using 1 <;> norm_num
  · change ((32683 / 50000 : ℚ) : ℝ) ≤ Real.exp ((-4251679 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-4251679 / 10000000 : ℚ) : ℝ) ≤ ((6536601 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_162 using 1 <;> norm_num
  · change ((4013691 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-225 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-225 / 1024 : ℚ) : ℝ) ≤ ((8027383 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_163 using 1 <;> norm_num
  · change ((7795617 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-255 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-255 / 1024 : ℚ) : ℝ) ≤ ((3897809 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_164 using 1 <;> norm_num
  · change ((360159 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-31 / 16 : ℚ) : ℝ) ∧ Real.exp ((-31 / 16 : ℚ) : ℝ) ≤ ((1440637 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_165 using 1 <;> norm_num
  · change ((635979 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-565737 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-565737 / 1250000 : ℚ) : ℝ) ≤ ((6359791 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_166 using 1 <;> norm_num
  · change ((1612243 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-2193321 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-2193321 / 5000000 : ℚ) : ℝ) ≤ ((6448973 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_167 using 1 <;> norm_num
  · change ((825797 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-49 / 256 : ℚ) : ℝ) ∧ Real.exp ((-49 / 256 : ℚ) : ℝ) ≤ ((8257971 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_168 using 1 <;> norm_num
  · change ((1981529 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-119 / 512 : ℚ) : ℝ) ∧ Real.exp ((-119 / 512 : ℚ) : ℝ) ≤ ((7926117 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_169 using 1 <;> norm_num
  · change ((1486367 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-61 / 32 : ℚ) : ℝ) ∧ Real.exp ((-61 / 32 : ℚ) : ℝ) ≤ ((46449 / 312500 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_170 using 1 <;> norm_num
  · change ((3134537 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-1167391 / 2500000 : ℚ) : ℝ) ∧ Real.exp ((-1167391 / 2500000 : ℚ) : ℝ) ≤ ((250763 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_171 using 1 <;> norm_num
  · change ((3179897 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-452589 / 1000000 : ℚ) : ℝ) ∧ Real.exp ((-452589 / 1000000 : ℚ) : ℝ) ≤ ((1271959 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_172 using 1 <;> norm_num
  · change ((1695721 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-169 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-169 / 1024 : ℚ) : ℝ) ≤ ((4239303 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_173 using 1 <;> norm_num
  · change ((20147 / 25000 : ℚ) : ℝ) ≤ Real.exp ((-221 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-221 / 1024 : ℚ) : ℝ) ≤ ((8058801 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_174 using 1 <;> norm_num
  · change ((1533549 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-15 / 8 : ℚ) : ℝ) ∧ Real.exp ((-15 / 8 : ℚ) : ℝ) ≤ ((30671 / 200000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_175 using 1 <;> norm_num
  · change ((1235367 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-481779 / 1000000 : ℚ) : ℝ) ∧ Real.exp ((-481779 / 1000000 : ℚ) : ℝ) ≤ ((1544209 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_176 using 1 <;> norm_num
  · change ((6269077 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-2334779 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-2334779 / 5000000 : ℚ) : ℝ) ≤ ((3134539 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_177 using 1 <;> norm_num
  · change ((173763 / 200000 : ℚ) : ℝ) ≤ Real.exp ((-9 / 64 : ℚ) : ℝ) ∧ Real.exp ((-9 / 64 : ℚ) : ℝ) ≤ ((8688151 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_178 using 1 <;> norm_num
  · change ((4096853 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-51 / 256 : ℚ) : ℝ) ∧ Real.exp ((-51 / 256 : ℚ) : ℝ) ≤ ((8193707 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_179 using 1 <;> norm_num
  · change ((1582229 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-59 / 32 : ℚ) : ℝ) ∧ Real.exp ((-59 / 32 : ℚ) : ℝ) ≤ ((158223 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_180 using 1 <;> norm_num
  · change ((608309 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-4970723 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-4970723 / 10000000 : ℚ) : ℝ) ≤ ((6083091 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_181 using 1 <;> norm_num
  · change ((3088419 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-963557 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-963557 / 2000000 : ℚ) : ℝ) ≤ ((6176839 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_182 using 1 <;> norm_num
  · change ((4442751 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-121 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-121 / 1024 : ℚ) : ℝ) ≤ ((8885503 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_183 using 1 <;> norm_num
  · change ((833087 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-187 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-187 / 1024 : ℚ) : ℝ) ≤ ((8330871 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_184 using 1 <;> norm_num
  · change ((326491 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-29 / 16 : ℚ) : ℝ) ∧ Real.exp ((-29 / 16 : ℚ) : ℝ) ≤ ((204057 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_185 using 1 <;> norm_num
  · change ((2993929 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-5128513 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-5128513 / 10000000 : ℚ) : ℝ) ≤ ((5987859 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_186 using 1 <;> norm_num
  · change ((6083093 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-4970717 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-4970717 / 10000000 : ℚ) : ℝ) ≤ ((3041547 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_187 using 1 <;> norm_num
  · change ((4534803 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-25 / 256 : ℚ) : ℝ) ∧ Real.exp ((-25 / 256 : ℚ) : ℝ) ≤ ((9069607 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_188 using 1 <;> norm_num
  · change ((8470329 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-85 / 512 : ℚ) : ℝ) ∧ Real.exp ((-85 / 512 : ℚ) : ℝ) ≤ ((8470331 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_189 using 1 <;> norm_num
  · change ((842137 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-57 / 32 : ℚ) : ℝ) ∧ Real.exp ((-57 / 32 : ℚ) : ℝ) ≤ ((67371 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_190 using 1 <;> norm_num
  · change ((184099 / 312500 : ℚ) : ℝ) ≤ Real.exp ((-5291307 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-5291307 / 10000000 : ℚ) : ℝ) ≤ ((5891169 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_191 using 1 <;> norm_num
  · change ((5987861 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-5128507 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-5128507 / 10000000 : ℚ) : ℝ) ≤ ((2993931 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_192 using 1 <;> norm_num
  · change ((461973 / 500000 : ℚ) : ℝ) ≤ Real.exp ((-81 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-81 / 1024 : ℚ) : ℝ) ≤ ((9239461 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_193 using 1 <;> norm_num
  · change ((2153031 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-153 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-153 / 1024 : ℚ) : ℝ) ≤ ((68897 / 80000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_194 using 1 <;> norm_num
  · change ((1737739 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-7 / 4 : ℚ) : ℝ) ∧ Real.exp ((-7 / 4 : ℚ) : ℝ) ≤ ((86887 / 500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_195 using 1 <;> norm_num
  · change ((1448261 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-682409 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-682409 / 1250000 : ℚ) : ℝ) ≤ ((1158609 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_196 using 1 <;> norm_num
  · change ((1472793 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-5291301 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-5291301 / 10000000 : ℚ) : ℝ) ≤ ((5891173 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_197 using 1 <;> norm_num
  · change ((939413 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-1 / 16 : ℚ) : ℝ) ∧ Real.exp ((-1 / 16 : ℚ) : ℝ) ≤ ((9394131 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_198 using 1 <;> norm_num
  · change ((2189073 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-17 / 128 : ℚ) : ℝ) ∧ Real.exp ((-17 / 128 : ℚ) : ℝ) ≤ ((8756293 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_199 using 1 <;> norm_num
  · change ((1792901 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-55 / 32 : ℚ) : ℝ) ∧ Real.exp ((-55 / 32 : ℚ) : ℝ) ≤ ((896451 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_200 using 1 <;> norm_num
  · change ((5693517 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-5632569 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-5632569 / 10000000 : ℚ) : ℝ) ≤ ((2846759 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_201 using 1 <;> norm_num
  · change ((5793047 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-2729633 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-2729633 / 5000000 : ℚ) : ℝ) ≤ ((724131 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_202 using 1 <;> norm_num
  · change ((595797 / 625000 : ℚ) : ℝ) ≤ Real.exp ((-49 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-49 / 1024 : ℚ) : ℝ) ≤ ((9532753 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_203 using 1 <;> norm_num
  · change ((4451437 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-119 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-119 / 1024 : ℚ) : ℝ) ≤ ((71223 / 80000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_204 using 1 <;> norm_num
  · change ((1849813 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-27 / 16 : ℚ) : ℝ) ∧ Real.exp ((-27 / 16 : ℚ) : ℝ) ≤ ((369963 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_205 using 1 <;> norm_num
  · change ((5592623 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-2905683 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-2905683 / 5000000 : ℚ) : ℝ) ≤ ((349539 / 625000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_206 using 1 <;> norm_num
  · change ((71169 / 125000 : ℚ) : ℝ) ≤ Real.exp ((-5632563 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-5632563 / 10000000 : ℚ) : ℝ) ≤ ((5693521 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_207 using 1 <;> norm_num
  · change ((1930909 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-9 / 256 : ℚ) : ℝ) ∧ Real.exp ((-9 / 256 : ℚ) : ℝ) ≤ ((4827273 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_208 using 1 <;> norm_num
  · change ((9051909 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-51 / 512 : ℚ) : ℝ) ∧ Real.exp ((-51 / 512 : ℚ) : ℝ) ≤ ((905191 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_209 using 1 <;> norm_num
  · change ((1908533 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-53 / 32 : ℚ) : ℝ) ∧ Real.exp ((-53 / 32 : ℚ) : ℝ) ≤ ((954267 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_210 using 1 <;> norm_num
  · change ((6863 / 12500 : ℚ) : ℝ) ≤ Real.exp ((-2997919 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-2997919 / 5000000 : ℚ) : ℝ) ≤ ((5490401 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_211 using 1 <;> norm_num
  · change ((1398157 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-5811357 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-5811357 / 10000000 : ℚ) : ℝ) ≤ ((5592629 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_212 using 1 <;> norm_num
  · change ((1951763 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-25 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-25 / 1024 : ℚ) : ℝ) ≤ ((304963 / 312500 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_213 using 1 <;> norm_num
  · change ((9203439 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-85 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-85 / 1024 : ℚ) : ℝ) ≤ ((115043 / 125000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_214 using 1 <;> norm_num
  · change ((492279 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-13 / 8 : ℚ) : ℝ) ∧ Real.exp ((-13 / 8 : ℚ) : ℝ) ≤ ((1969117 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_215 using 1 <;> norm_num
  · change ((5386891 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1237233 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-1237233 / 2000000 : ℚ) : ℝ) ≤ ((1346723 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_216 using 1 <;> norm_num
  · change ((1372601 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-749479 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-749479 / 1250000 : ℚ) : ℝ) ≤ ((1098081 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_217 using 1 <;> norm_num
  · change ((2461241 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-1 / 64 : ℚ) : ℝ) ∧ Real.exp ((-1 / 64 : ℚ) : ℝ) ≤ ((1968993 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_218 using 1 <;> norm_num
  · change ((4678753 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-17 / 256 : ℚ) : ℝ) ∧ Real.exp ((-17 / 256 : ℚ) : ℝ) ≤ ((9357507 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_219 using 1 <;> norm_num
  · change ((2031623 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-51 / 32 : ℚ) : ℝ) ∧ Real.exp ((-51 / 32 : ℚ) : ℝ) ≤ ((253953 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_220 using 1 <;> norm_num
  · change ((264107 / 500000 : ℚ) : ℝ) ≤ Real.exp ((-797817 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-797817 / 1250000 : ℚ) : ℝ) ≤ ((5282141 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_221 using 1 <;> norm_num
  · change ((1077379 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-6186159 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-6186159 / 10000000 : ℚ) : ℝ) ≤ ((336681 / 625000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_222 using 1 <;> norm_num
  · change ((4956247 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-9 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-9 / 1024 : ℚ) : ℝ) ≤ ((1982499 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_223 using 1 <;> norm_num
  · change ((1189269 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-51 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-51 / 1024 : ℚ) : ℝ) ≤ ((9514153 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_224 using 1 <;> norm_num
  · change ((2096113 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-25 / 16 : ℚ) : ℝ) ∧ Real.exp ((-25 / 16 : ℚ) : ℝ) ≤ ((1048057 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_225 using 1 <;> norm_num
  · change ((25881 / 50000 : ℚ) : ℝ) ≤ Real.exp ((-3292569 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-3292569 / 5000000 : ℚ) : ℝ) ≤ ((5176201 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_226 using 1 <;> norm_num
  · change ((165067 / 312500 : ℚ) : ℝ) ≤ Real.exp ((-638253 / 1000000 : ℚ) : ℝ) ∧ Real.exp ((-638253 / 1000000 : ℚ) : ℝ) ≤ ((1056429 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_227 using 1 <;> norm_num
  · change ((9961013 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1 / 256 : ℚ) : ℝ) ∧ Real.exp ((-1 / 256 : ℚ) : ℝ) ≤ ((4980507 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_228 using 1 <;> norm_num
  · change ((483671 / 500000 : ℚ) : ℝ) ≤ Real.exp ((-17 / 512 : ℚ) : ℝ) ∧ Real.exp ((-17 / 512 : ℚ) : ℝ) ≤ ((9673421 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_229 using 1 <;> norm_num
  · change ((2162651 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-49 / 32 : ℚ) : ℝ) ∧ Real.exp ((-49 / 32 : ℚ) : ℝ) ≤ ((540663 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_230 using 1 <;> norm_num
  · change ((2534561 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-6794173 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-6794173 / 10000000 : ℚ) : ℝ) ≤ ((5069123 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_231 using 1 <;> norm_num
  · change ((1294051 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-6585131 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-6585131 / 10000000 : ℚ) : ℝ) ≤ ((1035241 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_232 using 1 <;> norm_num
  · change ((9990239 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-1 / 1024 : ℚ) : ℝ) ≤ ((62439 / 62500 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_233 using 1 <;> norm_num
  · change ((4917677 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-17 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-17 / 1024 : ℚ) : ℝ) ≤ ((1967071 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_234 using 1 <;> norm_num
  · change ((2231301 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-3 / 2 : ℚ) : ℝ) ∧ Real.exp ((-3 / 2 : ℚ) : ℝ) ≤ ((1115651 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_235 using 1 <;> norm_num
  · change ((4960967 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-7009843 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-7009843 / 10000000 : ℚ) : ℝ) ≤ ((620121 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_236 using 1 <;> norm_num
  · change ((40553 / 80000 : ℚ) : ℝ) ≤ Real.exp ((-6794167 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-6794167 / 10000000 : ℚ) : ℝ) ≤ ((2534563 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_237 using 1 <;> norm_num
  · change ((1 / 1 : ℚ) : ℝ) ≤ Real.exp ((0 / 1 : ℚ) : ℝ) ∧ Real.exp ((0 / 1 : ℚ) : ℝ) ≤ ((1 / 1 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_238 using 1 <;> norm_num
  · change ((230213 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-47 / 32 : ℚ) : ℝ) ∧ Real.exp ((-47 / 32 : ℚ) : ℝ) ≤ ((2302131 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_239 using 1 <;> norm_num
  · change ((4851797 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-7232359 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-7232359 / 10000000 : ℚ) : ℝ) ≤ ((2425899 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_240 using 1 <;> norm_num
  · change ((496097 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-7009837 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-7009837 / 10000000 : ℚ) : ℝ) ≤ ((4960971 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_241 using 1 <;> norm_num
  · change ((10307363 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((31 / 1024 : ℚ) : ℝ) ∧ Real.exp ((31 / 1024 : ℚ) : ℝ) ≤ ((2576841 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_242 using 1 <;> norm_num
  · change ((296901 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-23 / 16 : ℚ) : ℝ) ∧ Real.exp ((-23 / 16 : ℚ) : ℝ) ≤ ((2375209 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_243 using 1 <;> norm_num
  · change ((2370839 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-373097 / 500000 : ℚ) : ℝ) ∧ Real.exp ((-373097 / 500000 : ℚ) : ℝ) ≤ ((4741679 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_244 using 1 <;> norm_num
  · change ((24259 / 50000 : ℚ) : ℝ) ≤ Real.exp ((-7232353 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-7232353 / 10000000 : ℚ) : ℝ) ≤ ((4851801 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_245 using 1 <;> norm_num
  · change ((10624173 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((31 / 512 : ℚ) : ℝ) ∧ Real.exp ((31 / 512 : ℚ) : ℝ) ≤ ((5312087 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_246 using 1 <;> norm_num
  · change ((490121 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-45 / 32 : ℚ) : ℝ) ∧ Real.exp ((-45 / 32 : ℚ) : ℝ) ≤ ((1225303 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_247 using 1 <;> norm_num
  · change ((4630683 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-7698807 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-7698807 / 10000000 : ℚ) : ℝ) ≤ ((1157671 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_248 using 1 <;> norm_num
  · change ((59271 / 125000 : ℚ) : ℝ) ≤ Real.exp ((-3730967 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-3730967 / 5000000 : ℚ) : ℝ) ≤ ((4741681 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_249 using 1 <;> norm_num
  · change ((5475361 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((93 / 1024 : ℚ) : ℝ) ∧ Real.exp ((93 / 1024 : ℚ) : ℝ) ≤ ((10950723 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_250 using 1 <;> norm_num
  · change ((505679 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-11 / 8 : ℚ) : ℝ) ∧ Real.exp ((-11 / 8 : ℚ) : ℝ) ≤ ((632099 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_251 using 1 <;> norm_num
  · change ((4518887 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-992899 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-992899 / 1250000 : ℚ) : ℝ) ≤ ((564861 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_252 using 1 <;> norm_num
  · change ((926137 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-7698801 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-7698801 / 10000000 : ℚ) : ℝ) ≤ ((2315343 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_253 using 1 <;> norm_num
  · change ((11287307 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((31 / 256 : ℚ) : ℝ) ∧ Real.exp ((31 / 256 : ℚ) : ℝ) ≤ ((2821827 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_254 using 1 <;> norm_num
  · change ((521731 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-43 / 32 : ℚ) : ℝ) ∧ Real.exp ((-43 / 32 : ℚ) : ℝ) ≤ ((163041 / 625000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_255 using 1 <;> norm_num
  · change ((4406371 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1024417 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-1024417 / 1250000 : ℚ) : ℝ) ≤ ((1101593 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_256 using 1 <;> norm_num
  · change ((451889 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-1588637 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-1588637 / 2000000 : ℚ) : ℝ) ≤ ((4518891 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_257 using 1 <;> norm_num
  · change ((11634237 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((155 / 1024 : ℚ) : ℝ) ∧ Real.exp ((155 / 1024 : ℚ) : ℝ) ≤ ((5817119 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_258 using 1 <;> norm_num
  · change ((2691463 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-21 / 16 : ℚ) : ℝ) ∧ Real.exp ((-21 / 16 : ℚ) : ℝ) ≤ ((336433 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_259 using 1 <;> norm_num
  · change ((2146609 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-1691097 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-1691097 / 2000000 : ℚ) : ℝ) ≤ ((4293219 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_260 using 1 <;> norm_num
  · change ((2203187 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-8195329 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-8195329 / 10000000 : ℚ) : ℝ) ≤ ((35251 / 80000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_261 using 1 <;> norm_num
  · change ((11991831 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((93 / 512 : ℚ) : ℝ) ∧ Real.exp ((93 / 512 : ℚ) : ℝ) ≤ ((1498979 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_262 using 1 <;> norm_num
  · change ((2776899 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-41 / 32 : ℚ) : ℝ) ∧ Real.exp ((-41 / 32 : ℚ) : ℝ) ≤ ((27769 / 100000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_263 using 1 <;> norm_num
  · change ((2089759 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-872389 / 1000000 : ℚ) : ℝ) ∧ Real.exp ((-872389 / 1000000 : ℚ) : ℝ) ≤ ((4179519 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_264 using 1 <;> norm_num
  · change ((4293221 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-4227739 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-4227739 / 5000000 : ℚ) : ℝ) ≤ ((2146611 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_265 using 1 <;> norm_num
  · change ((386263 / 312500 : ℚ) : ℝ) ≤ Real.exp ((217 / 1024 : ℚ) : ℝ) ∧ Real.exp ((217 / 1024 : ℚ) : ℝ) ≤ ((12360417 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_266 using 1 <;> norm_num
  · change ((2865047 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-5 / 4 : ℚ) : ℝ) ∧ Real.exp ((-5 / 4 : ℚ) : ℝ) ≤ ((358131 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_267 using 1 <;> norm_num
  · change ((813073 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-1800163 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-1800163 / 2000000 : ℚ) : ℝ) ≤ ((2032683 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_268 using 1 <;> norm_num
  · change ((4179521 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-8723883 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-8723883 / 10000000 : ℚ) : ℝ) ≤ ((2089761 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_269 using 1 <;> norm_num
  · change ((1274033 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((31 / 128 : ℚ) : ℝ) ∧ Real.exp ((31 / 128 : ℚ) : ℝ) ≤ ((12740331 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_270 using 1 <;> norm_num
  · change ((1477997 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-39 / 32 : ℚ) : ℝ) ∧ Real.exp ((-39 / 32 : ℚ) : ℝ) ≤ ((591199 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_271 using 1 <;> norm_num
  · change ((3950853 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-4643267 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-4643267 / 5000000 : ℚ) : ℝ) ≤ ((1975427 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_272 using 1 <;> norm_num
  · change ((508171 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-1125101 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-1125101 / 1250000 : ℚ) : ℝ) ≤ ((4065369 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_273 using 1 <;> norm_num
  · change ((13131921 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((279 / 1024 : ℚ) : ℝ) ∧ Real.exp ((279 / 1024 : ℚ) : ℝ) ≤ ((6565961 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_274 using 1 <;> norm_num
  · change ((3049827 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-19 / 16 : ℚ) : ℝ) ∧ Real.exp ((-19 / 16 : ℚ) : ℝ) ≤ ((762457 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_275 using 1 <;> norm_num
  · change ((479511 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-9581319 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-9581319 / 10000000 : ℚ) : ℝ) ≤ ((3836089 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_276 using 1 <;> norm_num
  · change ((493857 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-9286527 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-9286527 / 10000000 : ℚ) : ℝ) ≤ ((3950857 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_277 using 1 <;> norm_num
  · change ((3383887 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((155 / 512 : ℚ) : ℝ) ∧ Real.exp ((155 / 512 : ℚ) : ℝ) ≤ ((13535549 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_278 using 1 <;> norm_num
  · change ((3146639 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-37 / 32 : ℚ) : ℝ) ∧ Real.exp ((-37 / 32 : ℚ) : ℝ) ≤ ((39333 / 125000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_279 using 1 <;> norm_num
  · change ((930293 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-9885463 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-9885463 / 10000000 : ℚ) : ℝ) ≤ ((3721173 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_280 using 1 <;> norm_num
  · change ((3836091 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-74854 / 78125 : ℚ) : ℝ) ∧ Real.exp ((-74854 / 78125 : ℚ) : ℝ) ≤ ((959023 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_281 using 1 <;> norm_num
  · change ((13951581 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((341 / 1024 : ℚ) : ℝ) ∧ Real.exp ((341 / 1024 : ℚ) : ℝ) ≤ ((6975791 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_282 using 1 <;> norm_num
  · change ((811631 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-9 / 8 : ℚ) : ℝ) ∧ Real.exp ((-9 / 8 : ℚ) : ℝ) ≤ ((129861 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_283 using 1 <;> norm_num
  · change ((721243 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-10199261 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-10199261 / 10000000 : ℚ) : ℝ) ≤ ((450777 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_284 using 1 <;> norm_num
  · change ((148847 / 400000 : ℚ) : ℝ) ≤ Real.exp ((-1977091 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-1977091 / 2000000 : ℚ) : ℝ) ≤ ((465147 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_285 using 1 <;> norm_num
  · change ((7190201 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((93 / 256 : ℚ) : ℝ) ∧ Real.exp ((93 / 256 : ℚ) : ℝ) ≤ ((14380403 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_286 using 1 <;> norm_num
  · change ((167479 / 500000 : ℚ) : ℝ) ≤ Real.exp ((-35 / 32 : ℚ) : ℝ) ∧ Real.exp ((-35 / 32 : ℚ) : ℝ) ≤ ((3349581 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_287 using 1 <;> norm_num
  · change ((349133 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-10523021 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-10523021 / 10000000 : ℚ) : ℝ) ≤ ((3491331 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_288 using 1 <;> norm_num
  · change ((1803109 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-10199253 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-10199253 / 10000000 : ℚ) : ℝ) ≤ ((3606219 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_289 using 1 <;> norm_num
  · change ((14822403 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((403 / 1024 : ℚ) : ℝ) ∧ Real.exp ((403 / 1024 : ℚ) : ℝ) ≤ ((3705601 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_290 using 1 <;> norm_num
  · change ((3455907 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-17 / 16 : ℚ) : ℝ) ∧ Real.exp ((-17 / 16 : ℚ) : ℝ) ≤ ((863977 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_291 using 1 <;> norm_num
  · change ((1688317 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-10857057 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-10857057 / 10000000 : ℚ) : ℝ) ≤ ((675327 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_292 using 1 <;> norm_num
  · change ((3491333 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-10523013 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-10523013 / 10000000 : ℚ) : ℝ) ≤ ((1745667 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_293 using 1 <;> norm_num
  · change ((15277989 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((217 / 512 : ℚ) : ℝ) ∧ Real.exp ((217 / 512 : ℚ) : ℝ) ≤ ((1527799 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_294 using 1 <;> norm_num
  · change ((3565609 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-33 / 32 : ℚ) : ℝ) ∧ Real.exp ((-33 / 32 : ℚ) : ℝ) ≤ ((356561 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_295 using 1 <;> norm_num
  · change ((815561 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-350053 / 312500 : ℚ) : ℝ) ∧ Real.exp ((-350053 / 312500 : ℚ) : ℝ) ≤ ((652449 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_296 using 1 <;> norm_num
  · change ((844159 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-10857049 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-10857049 / 10000000 : ℚ) : ℝ) ≤ ((3376637 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_297 using 1 <;> norm_num
  · change ((15747579 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((465 / 1024 : ℚ) : ℝ) ∧ Real.exp ((465 / 1024 : ℚ) : ℝ) ≤ ((787379 / 500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_298 using 1 <;> norm_num
  · change ((1839397 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-1 / 1 : ℚ) : ℝ) ∧ Real.exp ((-1 / 1 : ℚ) : ℝ) ≤ ((735759 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_299 using 1 <;> norm_num
  · change ((3148283 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-11557277 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-11557277 / 10000000 : ℚ) : ℝ) ≤ ((787071 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_300 using 1 <;> norm_num
  · change ((3262247 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1400211 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-1400211 / 1250000 : ℚ) : ℝ) ≤ ((407781 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_301 using 1 <;> norm_num
  · change ((8115801 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((31 / 64 : ℚ) : ℝ) ∧ Real.exp ((31 / 64 : ℚ) : ℝ) ≤ ((16231603 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_302 using 1 <;> norm_num
  · change ((3795571 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-31 / 32 : ℚ) : ℝ) ∧ Real.exp ((-31 / 32 : ℚ) : ℝ) ≤ ((948893 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_303 using 1 <;> norm_num
  · change ((758719 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-11924143 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-11924143 / 10000000 : ℚ) : ℝ) ≤ ((3034877 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_304 using 1 <;> norm_num
  · change ((1574143 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-11557269 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-11557269 / 10000000 : ℚ) : ℝ) ≤ ((3148287 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_305 using 1 <;> norm_num
  · change ((1885257 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-289 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-289 / 1024 : ℚ) : ℝ) ≤ ((7541029 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_306 using 1 <;> norm_num
  · change ((8365251 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((527 / 1024 : ℚ) : ℝ) ∧ Real.exp ((527 / 1024 : ℚ) : ℝ) ≤ ((16730503 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_307 using 1 <;> norm_num
  · change ((489507 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-15 / 16 : ℚ) : ℝ) ∧ Real.exp ((-15 / 16 : ℚ) : ℝ) ≤ ((3916057 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_308 using 1 <;> norm_num
  · change ((730537 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-6151329 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-6151329 / 5000000 : ℚ) : ℝ) ≤ ((2922149 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_309 using 1 <;> norm_num
  · change ((3034879 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-2384827 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-2384827 / 2000000 : ℚ) : ℝ) ≤ ((4742 / 15625 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_310 using 1 <;> norm_num
  · change ((7287633 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-81 / 256 : ℚ) : ℝ) ∧ Real.exp ((-81 / 256 : ℚ) : ℝ) ≤ ((3643817 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_311 using 1 <;> norm_num
  · change ((269449 / 156250 : ℚ) : ℝ) ≤ Real.exp ((279 / 512 : ℚ) : ℝ) ∧ Real.exp ((279 / 512 : ℚ) : ℝ) ≤ ((17244737 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_312 using 1 <;> norm_num
  · change ((808073 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-29 / 32 : ℚ) : ℝ) ∧ Real.exp ((-29 / 32 : ℚ) : ℝ) ≤ ((2020183 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_313 using 1 <;> norm_num
  · change ((281023 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-6346593 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-6346593 / 5000000 : ℚ) : ℝ) ≤ ((2810231 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_314 using 1 <;> norm_num
  · change ((2922151 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-246053 / 200000 : ℚ) : ℝ) ∧ Real.exp ((-246053 / 200000 : ℚ) : ℝ) ≤ ((365269 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_315 using 1 <;> norm_num
  · change ((7029011 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-361 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-361 / 1024 : ℚ) : ℝ) ≤ ((1757253 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_316 using 1 <;> norm_num
  · change ((2221847 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((589 / 1024 : ℚ) : ℝ) ∧ Real.exp ((589 / 1024 : ℚ) : ℝ) ≤ ((17774777 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_317 using 1 <;> norm_num
  · change ((208431 / 500000 : ℚ) : ℝ) ≤ Real.exp ((-7 / 8 : ℚ) : ℝ) ∧ Real.exp ((-7 / 8 : ℚ) : ℝ) ≤ ((4168621 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_318 using 1 <;> norm_num
  · change ((10797 / 40000 : ℚ) : ℝ) ≤ Real.exp ((-13096111 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-13096111 / 10000000 : ℚ) : ℝ) ≤ ((2699251 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_319 using 1 <;> norm_num
  · change ((351279 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-6346589 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-6346589 / 5000000 : ℚ) : ℝ) ≤ ((2810233 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_320 using 1 <;> norm_num
  · change ((3383169 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-25 / 64 : ℚ) : ℝ) ∧ Real.exp ((-25 / 64 : ℚ) : ℝ) ≤ ((6766339 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_321 using 1 <;> norm_num
  · change ((4580277 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((155 / 256 : ℚ) : ℝ) ∧ Real.exp ((155 / 256 : ℚ) : ℝ) ≤ ((18321109 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_322 using 1 <;> norm_num
  · change ((2150473 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-27 / 32 : ℚ) : ℝ) ∧ Real.exp ((-27 / 32 : ℚ) : ℝ) ≤ ((4300947 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_323 using 1 <;> norm_num
  · change ((1294669 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-540473 / 400000 : ℚ) : ℝ) ∧ Real.exp ((-540473 / 400000 : ℚ) : ℝ) ≤ ((2589339 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_324 using 1 <;> norm_num
  · change ((674813 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-13096103 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-13096103 / 10000000 : ℚ) : ℝ) ≤ ((2699253 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_325 using 1 <;> norm_num
  · change ((1625193 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-441 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-441 / 1024 : ℚ) : ℝ) ≤ ((6500773 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_326 using 1 <;> norm_num
  · change ((18884231 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((651 / 1024 : ℚ) : ℝ) ∧ Real.exp ((651 / 1024 : ℚ) : ℝ) ≤ ((2360529 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_327 using 1 <;> norm_num
  · change ((4437473 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-13 / 16 : ℚ) : ℝ) ∧ Real.exp ((-13 / 16 : ℚ) : ℝ) ≤ ((2218737 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_328 using 1 <;> norm_num
  · change ((1240313 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-6970369 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-6970369 / 5000000 : ℚ) : ℝ) ≤ ((2480627 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_329 using 1 <;> norm_num
  · change ((129467 / 500000 : ℚ) : ℝ) ≤ Real.exp ((-13511817 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-13511817 / 10000000 : ℚ) : ℝ) ≤ ((2589341 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_330 using 1 <;> norm_num
  · change ((6233443 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-121 / 256 : ℚ) : ℝ) ∧ Real.exp ((-121 / 256 : ℚ) : ℝ) ≤ ((1558361 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_331 using 1 <;> norm_num
  · change ((19464663 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((341 / 512 : ℚ) : ℝ) ∧ Real.exp ((341 / 512 : ℚ) : ℝ) ≤ ((2433083 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_332 using 1 <;> norm_num
  · change ((4578333 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-25 / 32 : ℚ) : ℝ) ∧ Real.exp ((-25 / 32 : ℚ) : ℝ) ≤ ((2289167 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_333 using 1 <;> norm_num
  · change ((1186623 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-14383263 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-14383263 / 10000000 : ℚ) : ℝ) ≤ ((2373247 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_334 using 1 <;> norm_num
  · change ((2480629 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-13940729 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-13940729 / 10000000 : ℚ) : ℝ) ≤ ((248063 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_335 using 1 <;> norm_num
  · change ((1491361 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-529 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-529 / 1024 : ℚ) : ℝ) ≤ ((1193089 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_336 using 1 <;> norm_num
  · change ((2507867 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((713 / 1024 : ℚ) : ℝ) ∧ Real.exp ((713 / 1024 : ℚ) : ℝ) ≤ ((20062937 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_337 using 1 <;> norm_num
  · change ((944733 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-3 / 4 : ℚ) : ℝ) ∧ Real.exp ((-3 / 4 : ℚ) : ℝ) ≤ ((2361833 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_338 using 1 <;> norm_num
  · change ((1133663 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-14839837 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-14839837 / 10000000 : ℚ) : ℝ) ≤ ((2267327 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_339 using 1 <;> norm_num
  · change ((18541 / 78125 : ℚ) : ℝ) ≤ Real.exp ((-7191627 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-7191627 / 5000000 : ℚ) : ℝ) ≤ ((2373249 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_340 using 1 <;> norm_num
  · change ((1424457 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-9 / 16 : ℚ) : ℝ) ∧ Real.exp ((-9 / 16 : ℚ) : ℝ) ≤ ((5697829 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_341 using 1 <;> norm_num
  · change ((20679597 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((93 / 128 : ℚ) : ℝ) ∧ Real.exp ((93 / 128 : ℚ) : ℝ) ≤ ((10339799 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_342 using 1 <;> norm_num
  · change ((487361 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-23 / 32 : ℚ) : ℝ) ∧ Real.exp ((-23 / 32 : ℚ) : ℝ) ≤ ((4873611 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_343 using 1 <;> norm_num
  · change ((2162997 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-15310903 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-15310903 / 10000000 : ℚ) : ℝ) ≤ ((1081499 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_344 using 1 <;> norm_num
  · change ((35427 / 156250 : ℚ) : ℝ) ≤ Real.exp ((-3709957 / 2500000 : ℚ) : ℝ) ∧ Real.exp ((-3709957 / 2500000 : ℚ) : ℝ) ≤ ((2267329 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_345 using 1 <;> norm_num
  · change ((2715799 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-625 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-625 / 1024 : ℚ) : ℝ) ≤ ((5431599 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_346 using 1 <;> norm_num
  · change ((5328803 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((775 / 1024 : ℚ) : ℝ) ∧ Real.exp ((775 / 1024 : ℚ) : ℝ) ≤ ((21315213 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_347 using 1 <;> norm_num
  · change ((1005663 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-11 / 16 : ℚ) : ℝ) ∧ Real.exp ((-11 / 16 : ℚ) : ℝ) ≤ ((1257079 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_348 using 1 <;> norm_num
  · change ((64387 / 312500 : ℚ) : ℝ) ≤ Real.exp ((-15796923 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-15796923 / 10000000 : ℚ) : ℝ) ≤ ((412077 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_349 using 1 <;> norm_num
  · change ((2162999 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-7655447 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-7655447 / 5000000 : ℚ) : ℝ) ≤ ((2163 / 10000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_350 using 1 <;> norm_num
  · change ((1033541 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-169 / 256 : ℚ) : ℝ) ∧ Real.exp ((-169 / 256 : ℚ) : ℝ) ≤ ((2583853 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_351 using 1 <;> norm_num
  · change ((5492591 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((403 / 512 : ℚ) : ℝ) ∧ Real.exp ((403 / 512 : ℚ) : ℝ) ≤ ((4394073 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_352 using 1 <;> norm_num
  · change ((5187931 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-21 / 32 : ℚ) : ℝ) ∧ Real.exp ((-21 / 32 : ℚ) : ℝ) ≤ ((1296983 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_353 using 1 <;> norm_num
  · change ((979807 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-16298371 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-16298371 / 10000000 : ℚ) : ℝ) ≤ ((391923 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_354 using 1 <;> norm_num
  · change ((1030193 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-7898457 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-7898457 / 5000000 : ℚ) : ℝ) ≤ ((2060387 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_355 using 1 <;> norm_num
  · change ((30669 / 62500 : ℚ) : ℝ) ≤ Real.exp ((-729 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-729 / 1024 : ℚ) : ℝ) ≤ ((4907041 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_356 using 1 <;> norm_num
  · change ((5661413 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((837 / 1024 : ℚ) : ℝ) ∧ Real.exp ((837 / 1024 : ℚ) : ℝ) ≤ ((22645653 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_357 using 1 <;> norm_num
  · change ((2676307 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-5 / 8 : ℚ) : ℝ) ∧ Real.exp ((-5 / 8 : ℚ) : ℝ) ≤ ((1070523 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_358 using 1 <;> norm_num
  · change ((232601 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-8407869 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-8407869 / 5000000 : ℚ) : ℝ) ≤ ((1860809 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_359 using 1 <;> norm_num
  · change ((30619 / 156250 : ℚ) : ℝ) ≤ Real.exp ((-8149181 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-8149181 / 5000000 : ℚ) : ℝ) ≤ ((1959617 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_360 using 1 <;> norm_num
  · change ((4650431 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-49 / 64 : ℚ) : ℝ) ∧ Real.exp ((-49 / 64 : ℚ) : ℝ) ≤ ((72663 / 156250 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_361 using 1 <;> norm_num
  · change ((23341697 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((217 / 256 : ℚ) : ℝ) ∧ Real.exp ((217 / 256 : ℚ) : ℝ) ≤ ((11670849 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_362 using 1 <;> norm_num
  · change ((1380631 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-19 / 32 : ℚ) : ℝ) ∧ Real.exp ((-19 / 32 : ℚ) : ℝ) ≤ ((220901 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_363 using 1 <;> norm_num
  · change ((352817 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-8674763 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-8674763 / 5000000 : ℚ) : ℝ) ≤ ((882043 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_364 using 1 <;> norm_num
  · change ((186081 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-16815729 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-16815729 / 10000000 : ℚ) : ℝ) ≤ ((1860811 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_365 using 1 <;> norm_num
  · change ((2199321 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-841 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-841 / 1024 : ℚ) : ℝ) ≤ ((4398643 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_366 using 1 <;> norm_num
  · change ((4811827 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((899 / 1024 : ℚ) : ℝ) ∧ Real.exp ((899 / 1024 : ℚ) : ℝ) ≤ ((187962 / 78125 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_367 using 1 <;> norm_num
  · change ((834779 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-895013 / 500000 : ℚ) : ℝ) ∧ Real.exp ((-895013 / 500000 : ℚ) : ℝ) ≤ ((1669559 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_368 using 1 <;> norm_num
  · change ((1764087 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-17349517 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-17349517 / 10000000 : ℚ) : ℝ) ≤ ((220511 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_369 using 1 <;> norm_num
  · change ((259523 / 625000 : ℚ) : ℝ) ≤ Real.exp ((-225 / 256 : ℚ) : ℝ) ∧ Real.exp ((-225 / 256 : ℚ) : ℝ) ≤ ((4152369 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_370 using 1 <;> norm_num
  · change ((198389 / 80000 : ℚ) : ℝ) ≤ Real.exp ((465 / 512 : ℚ) : ℝ) ∧ Real.exp ((465 / 512 : ℚ) : ℝ) ≤ ((12399313 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_371 using 1 <;> norm_num
  · change ((734837 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-17 / 32 : ℚ) : ℝ) ∧ Real.exp ((-17 / 32 : ℚ) : ℝ) ≤ ((5878697 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_372 using 1 <;> norm_num
  · change ((197167 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-9234237 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-9234237 / 5000000 : ℚ) : ℝ) ≤ ((1577337 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_373 using 1 <;> norm_num
  · change ((1669559 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-71601 / 40000 : ℚ) : ℝ) ∧ Real.exp ((-71601 / 40000 : ℚ) : ℝ) ≤ ((41739 / 250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_374 using 1 <;> norm_num
  · change ((6390211 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((961 / 1024 : ℚ) : ℝ) ∧ Real.exp ((961 / 1024 : ℚ) : ℝ) ≤ ((5112169 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_375 using 1 <;> norm_num
  · change ((3032653 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-1 / 2 : ℚ) : ℝ) ∧ Real.exp ((-1 / 2 : ℚ) : ℝ) ≤ ((6065307 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_376 using 1 <;> norm_num
  · change ((1487523 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-19054727 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-19054727 / 10000000 : ℚ) : ℝ) ≤ ((371881 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_377 using 1 <;> norm_num
  · change ((788669 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-1154279 / 625000 : ℚ) : ℝ) ∧ Real.exp ((-1154279 / 625000 : ℚ) : ℝ) ≤ ((1577339 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_378 using 1 <;> norm_num
  · change ((2634649 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((31 / 32 : ℚ) : ℝ) ∧ Real.exp ((31 / 32 : ℚ) : ℝ) ≤ ((26346491 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_379 using 1 <;> norm_num
  · change ((78223 / 125000 : ℚ) : ℝ) ≤ Real.exp ((-15 / 32 : ℚ) : ℝ) ∧ Real.exp ((-15 / 32 : ℚ) : ℝ) ≤ ((6257841 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_380 using 1 <;> norm_num
  · change ((280043 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-1965959 / 1000000 : ℚ) : ℝ) ∧ Real.exp ((-1965959 / 1000000 : ℚ) : ℝ) ≤ ((175027 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_381 using 1 <;> norm_num
  · change ((371881 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-4763679 / 2500000 : ℚ) : ℝ) ∧ Real.exp ((-4763679 / 2500000 : ℚ) : ℝ) ≤ ((59501 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_382 using 1 <;> norm_num
  · change ((1726267 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-1089 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-1089 / 1024 : ℚ) : ℝ) ≤ ((690507 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_383 using 1 <;> norm_num
  · change ((5431257 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((1023 / 1024 : ℚ) : ℝ) ∧ Real.exp ((1023 / 1024 : ℚ) : ℝ) ≤ ((13578143 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_384 using 1 <;> norm_num
  · change ((1291297 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-7 / 16 : ℚ) : ℝ) ∧ Real.exp ((-7 / 16 : ℚ) : ℝ) ≤ ((3228243 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_385 using 1 <;> norm_num
  · change ((82219 / 625000 : ℚ) : ℝ) ≤ Real.exp ((-5070913 / 2500000 : ℚ) : ℝ) ∧ Real.exp ((-5070913 / 2500000 : ℚ) : ℝ) ≤ ((263101 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_386 using 1 <;> norm_num
  · change ((175027 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-982979 / 500000 : ℚ) : ℝ) ∧ Real.exp ((-982979 / 500000 : ℚ) : ℝ) ≤ ((1400217 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_387 using 1 <;> norm_num
  · change ((3233867 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-289 / 256 : ℚ) : ℝ) ∧ Real.exp ((-289 / 256 : ℚ) : ℝ) ≤ ((808467 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_388 using 1 <;> norm_num
  · change ((1665359 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-13 / 32 : ℚ) : ℝ) ∧ Real.exp ((-13 / 32 : ℚ) : ℝ) ≤ ((6661437 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_389 using 1 <;> norm_num
  · change ((1233471 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-5231881 / 2500000 : ℚ) : ℝ) ∧ Real.exp ((-5231881 / 2500000 : ℚ) : ℝ) ≤ ((19273 / 156250 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_390 using 1 <;> norm_num
  · change ((263101 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-20283641 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-20283641 / 10000000 : ℚ) : ℝ) ≤ ((657753 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_391 using 1 <;> norm_num
  · change ((151157 / 500000 : ℚ) : ℝ) ≤ Real.exp ((-1225 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-1225 / 1024 : ℚ) : ℝ) ≤ ((3023141 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_392 using 1 <;> norm_num
  · change ((2885131 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((1085 / 1024 : ℚ) : ℝ) ∧ Real.exp ((1085 / 1024 : ℚ) : ℝ) ≤ ((28851311 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_393 using 1 <;> norm_num
  · change ((1718223 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-3 / 8 : ℚ) : ℝ) ∧ Real.exp ((-3 / 8 : ℚ) : ℝ) ≤ ((6872893 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_394 using 1 <;> norm_num
  · change ((1154193 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-21591833 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-21591833 / 10000000 : ℚ) : ℝ) ≤ ((577097 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_395 using 1 <;> norm_num
  · change ((19273 / 156250 : ℚ) : ℝ) ≤ Real.exp ((-10463757 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-10463757 / 5000000 : ℚ) : ℝ) ≤ ((1233473 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_396 using 1 <;> norm_num
  · change ((2820629 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-81 / 64 : ℚ) : ℝ) ∧ Real.exp ((-81 / 64 : ℚ) : ℝ) ≤ ((282063 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_397 using 1 <;> norm_num
  · change ((29738093 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((279 / 256 : ℚ) : ℝ) ∧ Real.exp ((279 / 256 : ℚ) : ℝ) ≤ ((14869047 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_398 using 1 <;> norm_num
  · change ((7091061 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-11 / 32 : ℚ) : ℝ) ∧ Real.exp ((-11 / 32 : ℚ) : ℝ) ≤ ((3545531 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_399 using 1 <;> norm_num
  · change ((215547 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-22277231 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-22277231 / 10000000 : ℚ) : ℝ) ≤ ((134717 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_400 using 1 <;> norm_num
  · change ((577097 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-10795911 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-10795911 / 5000000 : ℚ) : ℝ) ≤ ((230839 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_401 using 1 <;> norm_num
  · change ((2626549 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1369 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-1369 / 1024 : ℚ) : ℝ) ≤ ((52531 / 200000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_402 using 1 <;> norm_num
  · change ((30652133 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((1147 / 1024 : ℚ) : ℝ) ∧ Real.exp ((1147 / 1024 : ℚ) : ℝ) ≤ ((15326067 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_403 using 1 <;> norm_num
  · change ((1829039 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-5 / 16 : ℚ) : ℝ) ∧ Real.exp ((-5 / 16 : ℚ) : ℝ) ≤ ((7316157 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_404 using 1 <;> norm_num
  · change ((502077 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-5746097 / 2500000 : ℚ) : ℝ) ∧ Real.exp ((-5746097 / 2500000 : ℚ) : ℝ) ≤ ((200831 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_405 using 1 <;> norm_num
  · change ((134717 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-1113861 / 500000 : ℚ) : ℝ) ∧ Real.exp ((-1113861 / 500000 : ℚ) : ℝ) ≤ ((1077737 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_406 using 1 <;> norm_num
  · change ((2441051 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-361 / 256 : ℚ) : ℝ) ∧ Real.exp ((-361 / 256 : ℚ) : ℝ) ≤ ((610263 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_407 using 1 <;> norm_num
  · change ((7898567 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((589 / 512 : ℚ) : ℝ) ∧ Real.exp ((589 / 512 : ℚ) : ℝ) ≤ ((31594269 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_408 using 1 <;> norm_num
  · change ((1509679 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-9 / 32 : ℚ) : ℝ) ∧ Real.exp ((-9 / 32 : ℚ) : ℝ) ≤ ((7548397 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_409 using 1 <;> norm_num
  · change ((1867 / 20000 : ℚ) : ℝ) ≤ Real.exp ((-2964249 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-2964249 / 1250000 : ℚ) : ℝ) ≤ ((933501 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_410 using 1 <;> norm_num
  · change ((251039 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-22984377 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-22984377 / 10000000 : ℚ) : ℝ) ≤ ((1004157 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_411 using 1 <;> norm_num
  · change ((2264227 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1521 / 1024 : ℚ) : ℝ) ∧ Real.exp ((-1521 / 1024 : ℚ) : ℝ) ≤ ((566057 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_412 using 1 <;> norm_num
  · change ((407067 / 125000 : ℚ) : ℝ) ≤ Real.exp ((1209 / 1024 : ℚ) : ℝ) ∧ Real.exp ((1209 / 1024 : ℚ) : ℝ) ≤ ((32565361 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_413 using 1 <;> norm_num
  · change ((865809 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-382293 / 156250 : ℚ) : ℝ) ∧ Real.exp ((-382293 / 156250 : ℚ) : ℝ) ≤ ((86581 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_414 using 1 <;> norm_num
  · change ((933501 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-23713977 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-23713977 / 10000000 : ℚ) : ℝ) ≤ ((466751 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_415 using 1 <;> norm_num
  · change ((335663 / 100000 : ℚ) : ℝ) ≤ Real.exp ((155 / 128 : ℚ) : ℝ) ∧ Real.exp ((155 / 128 : ℚ) : ℝ) ≤ ((33566301 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_416 using 1 <;> norm_num
  · change ((8290291 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-3 / 16 : ℚ) : ℝ) ∧ Real.exp ((-3 / 16 : ℚ) : ℝ) ≤ ((2072573 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_417 using 1 <;> norm_num
  · change ((739421 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-6511181 / 2500000 : ℚ) : ℝ) ∧ Real.exp ((-6511181 / 2500000 : ℚ) : ℝ) ≤ ((369711 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_418 using 1 <;> norm_num
  · change ((86581 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-1223337 / 500000 : ℚ) : ℝ) ∧ Real.exp ((-1223337 / 500000 : ℚ) : ℝ) ≤ ((865811 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_419 using 1 <;> norm_num
  · change ((1785911 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-441 / 256 : ℚ) : ℝ) ∧ Real.exp ((-441 / 256 : ℚ) : ℝ) ≤ ((223239 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_420 using 1 <;> norm_num
  · change ((35661421 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((651 / 512 : ℚ) : ℝ) ∧ Real.exp ((651 / 512 : ℚ) : ℝ) ≤ ((17830711 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_421 using 1 <;> norm_num
  · change ((8824969 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-1 / 8 : ℚ) : ℝ) ∧ Real.exp ((-1 / 8 : ℚ) : ℝ) ≤ ((882497 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_422 using 1 <;> norm_num
  · change ((9767 / 156250 : ℚ) : ℝ) ≤ Real.exp ((-1732779 / 625000 : ℚ) : ℝ) ∧ Real.exp ((-1732779 / 625000 : ℚ) : ℝ) ≤ ((625089 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_423 using 1 <;> norm_num
  · change ((369711 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-26044711 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-26044711 / 10000000 : ℚ) : ℝ) ≤ ((739423 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_424 using 1 <;> norm_num
  · change ((754887 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-121 / 64 : ℚ) : ℝ) ∧ Real.exp ((-121 / 64 : ℚ) : ℝ) ≤ ((60391 / 400000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_425 using 1 <;> norm_num
  · change ((18943657 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((341 / 256 : ℚ) : ℝ) ∧ Real.exp ((341 / 256 : ℚ) : ℝ) ≤ ((7577463 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_426 using 1 <;> norm_num
  · change ((522741 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-29512537 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-29512537 / 10000000 : ℚ) : ℝ) ≤ ((261371 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_427 using 1 <;> norm_num
  · change ((625089 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-6931113 / 2500000 : ℚ) : ℝ) ∧ Real.exp ((-6931113 / 2500000 : ℚ) : ℝ) ≤ ((62509 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_428 using 1 <;> norm_num
  · change ((40252141 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((713 / 512 : ℚ) : ℝ) ∧ Real.exp ((713 / 512 : ℚ) : ℝ) ≤ ((20126071 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_429 using 1 <;> norm_num
  · change ((432139 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-3141593 / 1000000 : ℚ) : ℝ) ∧ Real.exp ((-3141593 / 1000000 : ℚ) : ℝ) ≤ ((21607 / 500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_430 using 1 <;> norm_num
  · change ((261371 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-29512523 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-29512523 / 10000000 : ℚ) : ℝ) ≤ ((522743 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_431 using 1 <;> norm_num
  · change ((131749 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-9 / 4 : ℚ) : ℝ) ∧ Real.exp ((-9 / 4 : ℚ) : ℝ) ≤ ((1053993 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_432 using 1 <;> norm_num
  · change ((1710583 / 400000 : ℚ) : ℝ) ≤ Real.exp ((93 / 64 : ℚ) : ℝ) ∧ Real.exp ((93 / 64 : ℚ) : ℝ) ≤ ((1336393 / 312500 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_433 using 1 <;> norm_num
  · change ((665309 / 625000 : ℚ) : ℝ) ≤ Real.exp ((1 / 16 : ℚ) : ℝ) ∧ Real.exp ((1 / 16 : ℚ) : ℝ) ≤ ((2128989 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_434 using 1 <;> norm_num
  · change ((352881 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-6688417 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-6688417 / 2000000 : ℚ) : ℝ) ≤ ((176441 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_435 using 1 <;> norm_num
  · change ((432139 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-392699 / 125000 : ℚ) : ℝ) ∧ Real.exp ((-392699 / 125000 : ℚ) : ℝ) ≤ ((21607 / 500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_436 using 1 <;> norm_num
  · change ((870383 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-625 / 256 : ℚ) : ℝ) ∧ Real.exp ((-625 / 256 : ℚ) : ℝ) ≤ ((54399 / 625000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_437 using 1 <;> norm_num
  · change ((45433829 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((775 / 512 : ℚ) : ℝ) ∧ Real.exp ((775 / 512 : ℚ) : ℝ) ≤ ((4543383 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_438 using 1 <;> norm_num
  · change ((2832871 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((1 / 8 : ℚ) : ℝ) ∧ Real.exp ((1 / 8 : ℚ) : ℝ) ≤ ((2266297 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_439 using 1 <;> norm_num
  · change ((284419 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-17799457 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-17799457 / 5000000 : ℚ) : ℝ) ≤ ((14221 / 500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_440 using 1 <;> norm_num
  · change ((352881 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-3344207 / 1000000 : ℚ) : ℝ) ∧ Real.exp ((-3344207 / 1000000 : ℚ) : ℝ) ≤ ((176441 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_441 using 1 <;> norm_num
  · change ((356583 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-169 / 64 : ℚ) : ℝ) ∧ Real.exp ((-169 / 64 : ℚ) : ℝ) ≤ ((713167 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_442 using 1 <;> norm_num
  · change ((4826969 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((403 / 256 : ℚ) : ℝ) ∧ Real.exp ((403 / 256 : ℚ) : ℝ) ≤ ((48269691 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_443 using 1 <;> norm_num
  · change ((6031151 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((3 / 16 : ℚ) : ℝ) ∧ Real.exp ((3 / 16 : ℚ) : ℝ) ≤ ((12062303 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_444 using 1 <;> norm_num
  · change ((28259 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-37894847 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-37894847 / 10000000 : ℚ) : ℝ) ≤ ((226073 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_445 using 1 <;> norm_num
  · change ((284419 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-35598899 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-35598899 / 10000000 : ℚ) : ℝ) ≤ ((14221 / 500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_446 using 1 <;> norm_num
  · change ((2899 / 50000 : ℚ) : ℝ) ≤ Real.exp ((-729 / 256 : ℚ) : ℝ) ∧ Real.exp ((-729 / 256 : ℚ) : ℝ) ≤ ((579801 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_447 using 1 <;> norm_num
  · change ((51282559 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((837 / 512 : ℚ) : ℝ) ∧ Real.exp ((837 / 512 : ℚ) : ℝ) ≤ ((80129 / 15625 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_448 using 1 <;> norm_num
  · change ((6420127 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((1 / 4 : ℚ) : ℝ) ∧ Real.exp ((1 / 4 : ℚ) : ℝ) ≤ ((2568051 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_449 using 1 <;> norm_num
  · change ((177053 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-5042357 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-5042357 / 1250000 : ℚ) : ℝ) ≤ ((35411 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_450 using 1 <;> norm_num
  · change ((28259 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-37894831 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-37894831 / 10000000 : ℚ) : ℝ) ≤ ((226073 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_451 using 1 <;> norm_num
  · change ((233853 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-49 / 16 : ℚ) : ℝ) ∧ Real.exp ((-49 / 16 : ℚ) : ℝ) ≤ ((467707 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_452 using 1 <;> norm_num
  · change ((54483483 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((217 / 128 : ℚ) : ℝ) ∧ Real.exp ((217 / 128 : ℚ) : ℝ) ≤ ((13620871 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_453 using 1 <;> norm_num
  · change ((7274957 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((3 / 8 : ℚ) : ℝ) ∧ Real.exp ((3 / 8 : ℚ) : ℝ) ≤ ((2909983 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_454 using 1 <;> norm_num
  · change ((25869 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-5713739 / 1250000 : ℚ) : ℝ) ∧ Real.exp ((-5713739 / 1250000 : ℚ) : ℝ) ≤ ((103477 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_455 using 1 <;> norm_num
  · change ((88527 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-40338839 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-40338839 / 10000000 : ℚ) : ℝ) ≤ ((35411 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_456 using 1 <;> norm_num
  · change ((74323 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-225 / 64 : ℚ) : ℝ) ∧ Real.exp ((-225 / 64 : ℚ) : ℝ) ≤ ((297293 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_457 using 1 <;> norm_num
  · change ((61497181 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((465 / 256 : ℚ) : ℝ) ∧ Real.exp ((465 / 256 : ℚ) : ℝ) ≤ ((30748591 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_458 using 1 <;> norm_num
  · change ((4121803 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((1 / 2 : ℚ) : ℝ) ∧ Real.exp ((1 / 2 : ℚ) : ℝ) ≤ ((16487213 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_459 using 1 <;> norm_num
  · change ((56301 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-51796113 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-51796113 / 10000000 : ℚ) : ℝ) ≤ ((28151 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_460 using 1 <;> norm_num
  · change ((103477 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-45709893 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-45709893 / 10000000 : ℚ) : ℝ) ≤ ((51739 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_461 using 1 <;> norm_num
  · change ((45789 / 2500000 : ℚ) : ℝ) ≤ Real.exp ((-4 / 1 : ℚ) : ℝ) ∧ Real.exp ((-4 / 1 : ℚ) : ℝ) ≤ ((183157 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_462 using 1 <;> norm_num
  · change ((18682459 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((5 / 8 : ℚ) : ℝ) ∧ Real.exp ((5 / 8 : ℚ) : ℝ) ≤ ((934123 / 500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_463 using 1 <;> norm_num
  · change ((28249 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-29346343 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-29346343 / 5000000 : ℚ) : ℝ) ≤ ((113 / 40000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_464 using 1 <;> norm_num
  · change ((28151 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-51796093 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-51796093 / 10000000 : ℚ) : ℝ) ≤ ((56303 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_465 using 1 <;> norm_num
  · change ((109367 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-289 / 64 : ℚ) : ℝ) ∧ Real.exp ((-289 / 64 : ℚ) : ℝ) ≤ ((13671 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_466 using 1 <;> norm_num
  · change ((2117 / 1000 : ℚ) : ℝ) ≤ Real.exp ((3 / 4 : ℚ) : ℝ) ∧ Real.exp ((3 / 4 : ℚ) : ℝ) ≤ ((21170001 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_467 using 1 <;> norm_num
  · change ((1293 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-66507527 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-66507527 / 10000000 : ℚ) : ℝ) ≤ ((12931 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_468 using 1 <;> norm_num
  · change ((28249 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-58692663 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-58692663 / 10000000 : ℚ) : ℝ) ≤ ((113 / 40000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_469 using 1 <;> norm_num
  · change ((63297 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-81 / 16 : ℚ) : ℝ) ∧ Real.exp ((-81 / 16 : ℚ) : ℝ) ≤ ((31649 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_470 using 1 <;> norm_num
  · change ((44217711 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((279 / 128 : ℚ) : ℝ) ∧ Real.exp ((279 / 128 : ℚ) : ℝ) ≤ ((88435423 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_471 using 1 <;> norm_num
  · change ((391 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-42698677 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-42698677 / 5000000 : ℚ) : ℝ) ≤ ((489 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_472 using 1 <;> norm_num
  · change ((1293 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((-33253751 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-33253751 / 5000000 : ℚ) : ℝ) ≤ ((12931 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_473 using 1 <;> norm_num
  · change ((2413 / 1250000 : ℚ) : ℝ) ≤ Real.exp ((-25 / 4 : ℚ) : ℝ) ∧ Real.exp ((-25 / 4 : ℚ) : ℝ) ≤ ((3861 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_474 using 1 <;> norm_num
  · change ((2253393 / 200000 : ℚ) : ℝ) ≤ Real.exp ((155 / 64 : ℚ) : ℝ) ∧ Real.exp ((155 / 64 : ℚ) : ℝ) ≤ ((112669651 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_475 using 1 <;> norm_num
  · change ((4481689 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((3 / 2 : ℚ) : ℝ) ∧ Real.exp ((3 / 2 : ℚ) : ℝ) ≤ ((44816891 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_476 using 1 <;> norm_num
  · change ((7 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-8799777 / 625000 : ℚ) : ℝ) ∧ Real.exp ((-8799777 / 625000 : ℚ) : ℝ) ≤ ((1 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_477 using 1 <;> norm_num
  · change ((391 / 2000000 : ℚ) : ℝ) ≤ Real.exp ((-85397323 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-85397323 / 10000000 : ℚ) : ℝ) ≤ ((489 / 2500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_478 using 1 <;> norm_num
  · change ((617 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((-9 / 1 : ℚ) : ℝ) ∧ Real.exp ((-9 / 1 : ℚ) : ℝ) ≤ ((247 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_479 using 1 <;> norm_num
  · change ((91440447 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((93 / 32 : ℚ) : ℝ) ∧ Real.exp ((93 / 32 : ℚ) : ℝ) ≤ ((36576179 / 2000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_480 using 1 <;> norm_num
  · change ((121824939 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((5 / 2 : ℚ) : ℝ) ∧ Real.exp ((5 / 2 : ℚ) : ℝ) ≤ ((6091247 / 500000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_481 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-382724379 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-382724379 / 10000000 : ℚ) : ℝ) ≤ ((1 / 1048576 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_482 using 1 <;> norm_num
  · change ((7 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-140796383 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-140796383 / 10000000 : ℚ) : ℝ) ≤ ((1 / 1250000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_483 using 1 <;> norm_num
  · change ((1 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((-16 / 1 : ℚ) : ℝ) ∧ Real.exp ((-16 / 1 : ℚ) : ℝ) ≤ ((1 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_484 using 1 <;> norm_num
  · change ((900171313 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((9 / 2 : ℚ) : ℝ) ∧ Real.exp ((9 / 2 : ℚ) : ℝ) ≤ ((450085657 / 5000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_485 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-2827971899 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-2827971899 / 10000000 : ℚ) : ℝ) ≤ ((1 / 1048576 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_486 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-382724253 / 10000000 : ℚ) : ℝ) ∧ Real.exp ((-382724253 / 10000000 : ℚ) : ℝ) ≤ ((1 / 1048576 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_487 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-36 / 1 : ℚ) : ℝ) ∧ Real.exp ((-36 / 1 : ℚ) : ℝ) ≤ ((1 / 1048576 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_488 using 1 <;> norm_num
  · change ((3344542169 / 10000000 : ℚ) : ℝ) ≤ Real.exp ((93 / 16 : ℚ) : ℝ) ∧ Real.exp ((93 / 16 : ℚ) : ℝ) ≤ ((334454217 / 1000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_489 using 1 <;> norm_num
  · change ((665141633 / 1000000 : ℚ) : ℝ) ≤ Real.exp ((13 / 2 : ℚ) : ℝ) ∧ Real.exp ((13 / 2 : ℚ) : ℝ) ≤ ((6651416331 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_490 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-10448021493 / 5000000 : ℚ) : ℝ) ∧ Real.exp ((-10448021493 / 5000000 : ℚ) : ℝ) ≤ ((1 / 1048576 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_491 using 1 <;> norm_num
  · change ((0 / 1 : ℚ) : ℝ) ≤ Real.exp ((-565594199 / 2000000 : ℚ) : ℝ) ∧ Real.exp ((-565594199 / 2000000 : ℚ) : ℝ) ≤ ((1 / 1048576 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_492 using 1 <;> norm_num
  · change ((11607862073 / 5000000 : ℚ) : ℝ) ≤ Real.exp ((31 / 4 : ℚ) : ℝ) ∧ Real.exp ((31 / 4 : ℚ) : ℝ) ≤ ((23215724147 / 10000000 : ℚ) : ℝ)
    convert MasulloRH.HeightOneExponentialProof.n1_exp_493 using 1 <;> norm_num
