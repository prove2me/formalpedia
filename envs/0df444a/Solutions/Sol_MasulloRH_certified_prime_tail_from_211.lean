-- Prove2me | solution 1 for MasulloRH.certified_prime_tail_from_211
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:09:10.547717+00:00
-- url     : https://prove2.me/submissions/4cd2d971-646b-4a6f-8a42-6534677d005f

-- Fixed-point prime certificate for the Masullo finite-prime frontier.
import Mathlib
open ArithmeticFunction
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000

private def logFloor (p : ℕ) : ℕ := if 486 ≤ p then 6 else 5
-- Ten greedy binary steps give a certified lower approximation to 10 times the square root.
private def rootBits (t : ℕ) : ℕ → ℕ → ℕ
  | 0, a => a
  | k+1, a =>
    let b := a + 2^k
    rootBits t k (if b*b ≤ t then b else a)

private theorem rootBits_sq (t k a : ℕ) (ha : a*a ≤ t) :
    rootBits t k a * rootBits t k a ≤ t := by
  induction k generalizing a with
  | zero => exact ha
  | succ k ih =>
    by_cases hb : (a + 2^k) * (a + 2^k) ≤ t
    · simpa only [rootBits, if_pos hb] using ih (a + 2^k) hb
    · simpa only [rootBits, if_neg hb] using ih a ha

private def root10 (p : ℕ) := rootBits (100*p) 10 10

private def billionths (p : ℕ) : ℕ :=
  logFloor p * (root10 p - 10) * 100000000 / p^3

private def block0 : List ℕ := [211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317]
private def block1 : List ℕ := [331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443]
private def block2 : List ℕ := [449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577]
private def block3 : List ℕ := [587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701]
private def block4 : List ℕ := [709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839]
private def block5 : List ℕ := [853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983]
private def block6 : List ℕ := [991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109]
private def block7 : List ℕ := [1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277]
private def block8 : List ℕ := [1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429]
private def block9 : List ℕ := [1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559]
private def block10 : List ℕ := [1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699]
private def block11 : List ℕ := [1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871]
private def block12 : List ℕ := [1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017]
private def block13 : List ℕ := [2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161]
private def block14 : List ℕ := [2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339]
private def block15 : List ℕ := [2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473]
private def block16 : List ℕ := [2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663]
private def block17 : List ℕ := [2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791]
private def block18 : List ℕ := [2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957]
private def block19 : List ℕ := [2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137]
private def block20 : List ℕ := [3163, 3167, 3169, 3181, 3187, 3191]

private def budgetList : List ℕ := block0 ++ block1 ++ block2 ++ block3 ++ block4 ++ block5 ++ block6 ++ block7 ++ block8 ++ block9 ++ block10 ++ block11 ++ block12 ++ block13 ++ block14 ++ block15 ++ block16 ++ block17 ++ block18 ++ block19 ++ block20
private def budgetPrimes : Finset ℕ := budgetList.toFinset
private theorem block0_value : (block0.map billionths).sum = 87310 := by decide +kernel
private theorem block0_good : block0.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block1_value : (block1.map billionths).sum = 33039 := by decide +kernel
private theorem block1_good : block1.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block2_value : (block2.map billionths).sum = 18613 := by decide +kernel
private theorem block2_good : block2.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block3_value : (block3.map billionths).sum = 11235 := by decide +kernel
private theorem block3_good : block3.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block4_value : (block4.map billionths).sum = 6951 := by decide +kernel
private theorem block4_good : block4.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block5_value : (block5.map billionths).sum = 4605 := by decide +kernel
private theorem block5_good : block5.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block6_value : (block6.map billionths).sum = 3248 := by decide +kernel
private theorem block6_good : block6.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block7_value : (block7.map billionths).sum = 2361 := by decide +kernel
private theorem block7_good : block7.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block8_value : (block8.map billionths).sum = 1760 := by decide +kernel
private theorem block8_good : block8.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block9_value : (block9.map billionths).sum = 1350 := by decide +kernel
private theorem block9_good : block9.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block10_value : (block10.map billionths).sum = 1085 := by decide +kernel
private theorem block10_good : block10.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block11_value : (block11.map billionths).sum = 859 := by decide +kernel
private theorem block11_good : block11.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block12_value : (block12.map billionths).sum = 690 := by decide +kernel
private theorem block12_good : block12.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block13_value : (block13.map billionths).sum = 573 := by decide +kernel
private theorem block13_good : block13.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block14_value : (block14.map billionths).sum = 471 := by decide +kernel
private theorem block14_good : block14.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block15_value : (block15.map billionths).sum = 405 := by decide +kernel
private theorem block15_good : block15.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block16_value : (block16.map billionths).sum = 339 := by decide +kernel
private theorem block16_good : block16.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block17_value : (block17.map billionths).sum = 293 := by decide +kernel
private theorem block17_good : block17.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block18_value : (block18.map billionths).sum = 256 := by decide +kernel
private theorem block18_good : block18.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block19_value : (block19.map billionths).sum = 219 := by decide +kernel
private theorem block19_good : block19.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem block20_value : (block20.map billionths).sum = 60 := by decide +kernel
private theorem block20_good : block20.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by decide +kernel
private theorem budget_good (p : ℕ) (hp : p ∈ budgetPrimes) : p.Prime ∧ 211 ≤ p ∧ p ≤ 3200 := by
  have h : budgetList.all (fun p ↦ decide (Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200)) = true := by
    simp only [budgetList, List.all_append, block0_good, block1_good, block2_good, block3_good, block4_good, block5_good, block6_good, block7_good, block8_good, block9_good, block10_good, block11_good, block12_good, block13_good, block14_good, block15_good, block16_good, block17_good, block18_good, block19_good, block20_good, Bool.and_self]
  have hcheck : Nat.gcd p (Nat.factorial 57) = 1 ∧ 211 ≤ p ∧ p ≤ 3200 := by
    simpa using List.all_eq_true.mp h p (List.mem_toFinset.mp hp)
  refine ⟨?_, hcheck.2⟩
  by_contra hnot
  have hpos : 0 < p := by omega
  have hsq := Nat.minFac_sq_le_self hpos hnot
  have hm : p.minFac ≤ 57 := by nlinarith [hcheck.2.2]
  have hd := Nat.dvd_gcd (Nat.minFac_dvd p) (Nat.dvd_factorial (Nat.minFac_pos p) hm)
  rw [hcheck.1] at hd
  have hone := Nat.dvd_one.mp hd
  exact (Nat.minFac_prime (by omega : p ≠ 1)).ne_one hone
private theorem budget_total : 175000 ≤ ∑ p ∈ budgetPrimes, billionths p := by
  have hn : budgetList.Nodup := by
    have hc : budgetList.IsChain (· < ·) := by decide +kernel
    exact hc.sortedLT.pairwise.nodup
  rw [budgetPrimes, List.sum_toFinset _ hn]
  simp only [budgetList, List.map_append, List.sum_append, block0_value, block1_value, block2_value, block3_value, block4_value, block5_value, block6_value, block7_value, block8_value, block9_value, block10_value, block11_value, block12_value, block13_value, block14_value, block15_value, block16_value, block17_value, block18_value, block19_value, block20_value]
  decide


private theorem billionths_le_term (p : ℕ) (hp : p ∈ budgetPrimes) :
    (billionths p : ℝ) / 1000000000 ≤
    ArithmeticFunction.vonMangoldt p / (p:ℝ)^(5/2:ℝ) -
      ArithmeticFunction.vonMangoldt p / (p:ℝ)^(3:ℝ) := by
  obtain ⟨hprime, hlo, _⟩ := budget_good p hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hl : (logFloor p : ℝ) ≤ Real.log p := by
    unfold logFloor
    split_ifs with h
    · have he := Real.log_le_log (by norm_num : (0:ℝ) < 2 * 3^5)
          (show (2:ℝ)*3^5 ≤ p by exact_mod_cast (by omega : 2*3^5 ≤ p))
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at he
      norm_num only [Nat.cast_ofNat] at he ⊢
      linarith [Real.log_three_gt_d9, Real.log_two_gt_d9]
    · have he := Real.log_le_log (by norm_num : (0:ℝ) < 2 * 3^4)
          (show (2:ℝ)*3^4 ≤ p by exact_mod_cast (by omega : 2*3^4 ≤ p))
      rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at he
      norm_num at he ⊢
      linarith [Real.log_three_gt_d9, Real.log_two_gt_d9]
  have hs : (root10 p : ℝ) ≤ 10 * Real.sqrt p := by
    have hsq : ((root10 p : ℝ))^2 ≤ 100*(p:ℝ) := by
      have h := rootBits_sq (100*p) 10 10 (by omega)
      change root10 p * root10 p ≤ 100*p at h
      exact_mod_cast (by simpa only [sq] using h : (root10 p)^2 ≤ 100*p)
    nlinarith [Real.sq_sqrt hp0.le, Real.sqrt_nonneg (p:ℝ)]
  have hbase (t k a : ℕ) : a ≤ rootBits t k a := by
    induction k generalizing a with
    | zero => exact le_rfl
    | succ k ih =>
      by_cases hb : (a + 2^k) * (a + 2^k) ≤ t
      · simpa only [rootBits, if_pos hb] using (Nat.le_add_right a (2^k)).trans (ih (a + 2^k))
      · simpa only [rootBits, if_neg hb] using ih a
  have h10 : 10 ≤ root10 p := hbase _ _ _
  have hnat := Nat.div_mul_le_self (logFloor p * (root10 p - 10) * 100000000) (p^3)
  have hreal : (billionths p : ℝ) * (p:ℝ)^3 ≤
        (logFloor p : ℝ) * ((root10 p : ℝ)-10) * 100000000 := by
    unfold billionths
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub h10, Nat.cast_ofNat]
      using (Nat.cast_le (α := ℝ)).mpr hnat
  have hprod : (logFloor p:ℝ)*((root10 p:ℝ)-10) ≤
      Real.log p * (10 * Real.sqrt p - 10) :=
    mul_le_mul hl (by linarith) (sub_nonneg.mpr (by exact_mod_cast h10))
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p)))
  have hkey : (p:ℝ)^(5/2:ℝ) * Real.sqrt p = (p:ℝ)^3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp0, show (5/2:ℝ)+1/2=3 by norm_num, Real.rpow_ofNat]
  rw [ArithmeticFunction.vonMangoldt_apply_prime hprime, Real.rpow_ofNat]
  have hden : (p:ℝ)^(5/2:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hp0 _).ne'
  have heq : Real.log p / (p:ℝ)^(5/2:ℝ) - Real.log p/(p:ℝ)^3 =
      Real.log p * (Real.sqrt p - 1)/(p:ℝ)^3 := by
    rw [← hkey]
    field_simp [hden, (Real.sqrt_pos.mpr hp0).ne']
  rw [heq, le_div_iff₀ (by positivity)]
  nlinarith only [hreal, hprod]


theorem solution : ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 211 ≤ p ∧ p ≤ 3200) ∧
      175000/1000000000 ≤ ∑ p ∈ P,
        (vonMangoldt p/(p:ℝ)^(5/2:ℝ) - vonMangoldt p/(p:ℝ)^(3:ℝ)) := by
  refine ⟨budgetPrimes, budget_good, ?_⟩
  calc (175000/1000000000:ℝ) ≤ ∑ p ∈ budgetPrimes, (billionths p:ℝ)/1000000000 := by
         rw [← Finset.sum_div]
         apply div_le_div_of_nonneg_right _ (by positivity)
         exact_mod_cast budget_total
       _ ≤ _ := Finset.sum_le_sum billionths_le_term
