-- Prove2me | solution 1 for IntMul.HvdH.rosser_schoenfeld_thm4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T00:25:57.849028+00:00
-- url     : https://prove2.me/submissions/b9afae66-c489-478e-8ed8-be9cdfa950aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic
import Theorems.Thm_IntMul_HvdH_rosser_schoenfeld_theta_upper

open Real

namespace RSThm4

/-- The primes up to 1307 (the largest segment start used below). -/
def L : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307]

set_option maxRecDepth 100000 in
lemma L_prime : ∀ p ∈ L, p.Prime := by
  simp only [L, List.forall_mem_cons]
  norm_num

set_option maxRecDepth 100000 in
lemma L_nodup : L.Nodup := by decide

/-- θ(a) is at least the log of the product of the listed primes `≤ a`. -/
lemma log_prod_le_theta (a : ℕ) :
    Real.log (((L.filter (· ≤ a)).prod : ℕ) : ℝ) ≤ Chebyshev.theta a := by
  have hnd : (L.filter (· ≤ a)).Nodup := L_nodup.filter _
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  have hprod : (L.filter (· ≤ a)).prod = ∏ p ∈ (L.filter (· ≤ a)).toFinset, p := by
    rw [List.prod_toFinset _ hnd, List.map_id']
  rw [hprod, Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [List.mem_toFinset, List.mem_filter] at hp
      rw [Nat.mem_primesLE]
      exact ⟨by simpa using hp.2, L_prime p hp.1⟩
    · intro p _ _
      exact Real.log_natCast_nonneg p
  · intro p hp
    rw [List.mem_toFinset, List.mem_filter] at hp
    exact_mod_cast (L_prime p hp.1).ne_zero

/-- One certified segment `[a, b]` of the finite range. -/
lemma seg (a b ja ma jb mb : ℕ) (hja : 0 < ja) (hjb : 0 < jb)
    (hA : 2 ^ ma ≤ (L.filter (· ≤ a)).prod ^ ja) (hB : b ^ jb ≤ 2 ^ mb)
    (ha : 563 ≤ a)
    (hnum : (b : ℝ) * (1 - 1 / (2 * ((mb : ℝ) / jb * 0.6931471808))) <
      (ma : ℝ) / ja * 0.6931471803)
    (y : ℝ) (hay : (a : ℝ) ≤ y) (hyb : y ≤ b) :
    y - y / (2 * Real.log y) < Chebyshev.theta y := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have hja' : (0 : ℝ) < ja := by exact_mod_cast hja
  have hjb' : (0 : ℝ) < jb := by exact_mod_cast hjb
  have ha' : (563 : ℝ) ≤ a := by exact_mod_cast ha
  -- lower bound for θ(a)
  set N := (L.filter (· ≤ a)).prod with hN
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by
      rw [hN]; apply List.prod_pos
      intro p hp; exact (L_prime p (List.mem_filter.1 hp).1).pos
    exact_mod_cast this
  have hlamN : (ma : ℝ) / ja * 0.6931471803 ≤ Real.log N := by
    have h1 : Real.log ((2 : ℝ) ^ ma) ≤ Real.log ((N : ℝ) ^ ja) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hA)
    rw [Real.log_pow, Real.log_pow] at h1
    rw [div_mul_eq_mul_div, div_le_iff₀ hja']
    nlinarith
  have hθa := log_prod_le_theta a
  have hθy : Chebyshev.theta a ≤ Chebyshev.theta y := Chebyshev.theta_mono hay
  -- upper bound for log b
  have hb' : (563 : ℝ) ≤ b := ha'.trans (hay.trans hyb)
  have hU : Real.log b ≤ (mb : ℝ) / jb * 0.6931471808 := by
    have h1 : Real.log ((b : ℝ) ^ jb) ≤ Real.log ((2 : ℝ) ^ mb) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hB)
    rw [Real.log_pow, Real.log_pow] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hjb']
    nlinarith
  -- compare
  have hy0 : (1 : ℝ) < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy0
  have hlogyb : Real.log y ≤ Real.log b := Real.log_le_log (by linarith) hyb
  set U := (mb : ℝ) / jb * 0.6931471808 with hUdef
  have hU1 : 1 ≤ U := by
    have : (1 : ℝ) < Real.log b := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hk : y / (2 * U) ≤ y / (2 * Real.log y) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
  have hc : 0 ≤ 1 - 1 / (2 * U) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have : y - y / (2 * U) ≤ (b : ℝ) * (1 - 1 / (2 * U)) := by
    have : y - y / (2 * U) = y * (1 - 1 / (2 * U)) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hyb hc
  linarith

theorem finite_range (y : ℝ) (h1 : 563 ≤ y) (h2 : y ≤ 1340) :
    y - y / (2 * Real.log y) < Chebyshev.theta y := by
  rcases le_or_gt y 569 with h0 | h0
  · exact seg 563 569 11 8328 13 119 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 571 with h1 | h1
  · exact seg 569 571 37 28351 19 174 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 577 with h2 | h2
  · exact seg 571 577 5 3877 23 211 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 587 with h3 | h3
  · exact seg 577 587 7 5492 5 46 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 593 with h4 | h4
  · exact seg 587 593 35 27782 33 304 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 601 with h5 | h5
  · exact seg 593 601 40 32119 30 277 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 617 with h6 | h6
  · exact seg 601 617 34 27929 26 241 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 631 with h7 | h7
  · exact seg 617 631 14 11889 33 307 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 647 with h8 | h8
  · exact seg 631 647 19 16488 38 355 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 661 with h9 | h9
  · exact seg 647 661 32 28665 27 253 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 691 with h10 | h10
  · exact seg 661 691 37 34183 30 283 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 719 with h11 | h11
  · exact seg 691 719 2 1923 2 19 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 739 with h12 | h12
  · exact seg 719 739 13 12869 32 305 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 761 with h13 | h13
  · exact seg 739 761 21 21388 40 383 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 787 with h14 | h14
  · exact seg 761 787 10 10567 29 279 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 811 with h15 | h15
  · exact seg 787 811 2 2171 3 29 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 829 with h16 | h16
  · exact seg 811 829 28 31205 23 223 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 863 with h17 | h17
  · exact seg 829 863 23 26524 37 361 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 887 with h18 | h18
  · exact seg 863 887 11 13221 29 284 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 919 with h19 | h19
  · exact seg 887 919 21 26062 13 128 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 947 with h20 | h20
  · exact seg 919 947 31 39387 9 89 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 977 with h21 | h21
  · exact seg 947 977 22 28821 15 149 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 997 with h22 | h22
  · exact seg 977 997 7 9448 26 259 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 1021 with h23 | h23
  · exact seg 997 1021 37 51044 1 10 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 1051 with h24 | h24
  · exact seg 1021 1051 23 32649 26 261 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 1097 with h25 | h25
  · exact seg 1051 1097 11 16166 10 101 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 1129 with h26 | h26
  · exact seg 1097 1129 40 61607 7 71 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 1181 with h27 | h27
  · exact seg 1129 1181 39 62041 34 347 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 1223 with h28 | h28
  · exact seg 1181 1223 25 41043 39 400 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 1259 with h29 | h29
  · exact seg 1223 1259 15 25547 10 103 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 1307 with h30 | h30
  · exact seg 1259 1307 27 47372 17 176 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  exact seg 1307 1340 28 51731 18 187 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)

end RSThm4

theorem solution (y : ℝ) (hy : 563 ≤ y) :
    y - y / (2 * Real.log y) < Chebyshev.theta y ∧
      Chebyshev.theta y < y + y / (2 * Real.log y) := by
  refine ⟨?_, IntMul.HvdH.rosser_schoenfeld_theta_upper y hy⟩
  rcases le_or_gt y 1340 with h | h
  · exact RSThm4.finite_range y hy h
  · have h1 := TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic y h.le
    have h2 : y * (1 - 1 / (2 * Real.log y)) = y - y / (2 * Real.log y) := by ring
    linarith
