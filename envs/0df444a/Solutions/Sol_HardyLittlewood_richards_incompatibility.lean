-- Prove2me | solution 1 for HardyLittlewood.richards_incompatibility
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-20T14:33:38.907884+00:00
-- url     : https://prove2.me/submissions/8e211b9e-eae3-4b54-b207-6429a53c5c27

import Definitions.Def_HardyLittlewood_constellation
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_HardyLittlewood_counting
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Theorems.Thm_HardyLittlewood_first_implies_infinite_constellations

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HLRichardsCert

-- Engelsma's 447-element admissible pattern, MIT/Polymath prime-gaps database.
-- https://math.mit.edu/~primegaps/tuples/admissible_447_3158.txt
def offsets : List ℕ := [0, 2, 6, 8, 12, 20, 30, 32, 42, 48, 50, 56, 68, 72, 78, 90, 92, 96, 98, 102, 110, 116, 128, 132, 138, 146, 152, 156, 158, 162, 176, 186, 200, 210, 212, 216, 228, 230, 240, 242, 246, 252, 260, 266, 272, 278, 282, 288, 300, 306, 308, 312, 320, 326, 336, 338, 342, 350, 366, 372, 378, 380, 386, 396, 398, 420, 422, 428, 432, 438, 440, 450, 462, 470, 476, 482, 488, 492, 498, 506, 510, 512, 516, 518, 536, 546, 548, 558, 572, 576, 590, 600, 602, 606, 618, 620, 638, 648, 650, 656, 662, 672, 690, 692, 702, 708, 716, 722, 726, 740, 746, 756, 762, 768, 776, 782, 792, 798, 806, 810, 812, 818, 828, 840, 846, 858, 860, 866, 870, 872, 876, 882, 888, 890, 900, 912, 926, 930, 938, 942, 950, 956, 960, 966, 968, 980, 986, 992, 1008, 1020, 1022, 1026, 1040, 1052, 1056, 1058, 1062, 1068, 1080, 1082, 1086, 1098, 1110, 1112, 1118, 1122, 1142, 1146, 1148, 1166, 1170, 1176, 1178, 1188, 1190, 1196, 1202, 1212, 1220, 1236, 1238, 1250, 1260, 1262, 1266, 1272, 1278, 1290, 1296, 1302, 1308, 1328, 1332, 1346, 1350, 1352, 1356, 1370, 1376, 1392, 1400, 1406, 1416, 1418, 1428, 1430, 1436, 1442, 1448, 1458, 1470, 1476, 1478, 1488, 1496, 1500, 1502, 1520, 1530, 1532, 1538, 1542, 1560, 1566, 1568, 1580, 1590, 1602, 1608, 1610, 1626, 1632, 1638, 1640, 1646, 1652, 1656, 1670, 1680, 1682, 1692, 1706, 1712, 1716, 1722, 1728, 1730, 1748, 1758, 1766, 1770, 1772, 1790, 1796, 1800, 1806, 1812, 1818, 1826, 1832, 1836, 1838, 1848, 1850, 1862, 1866, 1868, 1878, 1880, 1892, 1896, 1898, 1902, 1910, 1916, 1926, 1932, 1938, 1940, 1946, 1962, 1980, 1982, 1988, 1992, 2000, 2006, 2016, 2022, 2028, 2036, 2046, 2048, 2052, 2060, 2066, 2070, 2072, 2076, 2078, 2088, 2102, 2108, 2112, 2120, 2130, 2132, 2148, 2162, 2178, 2186, 2190, 2192, 2198, 2202, 2210, 2226, 2240, 2252, 2256, 2258, 2268, 2280, 2286, 2310, 2312, 2316, 2318, 2322, 2336, 2342, 2352, 2358, 2360, 2366, 2372, 2388, 2396, 2400, 2406, 2408, 2412, 2430, 2438, 2442, 2450, 2456, 2462, 2468, 2478, 2486, 2490, 2492, 2496, 2508, 2510, 2522, 2528, 2538, 2540, 2552, 2562, 2570, 2576, 2580, 2582, 2592, 2598, 2606, 2616, 2618, 2622, 2630, 2640, 2648, 2652, 2658, 2660, 2666, 2676, 2682, 2690, 2696, 2706, 2708, 2718, 2732, 2736, 2742, 2750, 2756, 2760, 2762, 2778, 2786, 2790, 2798, 2808, 2820, 2822, 2826, 2828, 2850, 2856, 2858, 2862, 2868, 2882, 2888, 2892, 2900, 2910, 2912, 2918, 2928, 2930, 2940, 2952, 2958, 2966, 2970, 2972, 2982, 2990, 2996, 3002, 3018, 3036, 3042, 3050, 3056, 3060, 3066, 3072, 3080, 3086, 3092, 3098, 3102, 3110, 3122, 3126, 3128, 3138, 3150, 3152, 3158]

def omitted (q : ℕ) : ℕ := match q with
  | 2 => 1
  | 3 => 1
  | 5 => 4
  | 7 => 3
  | 11 => 5
  | 13 => 10
  | 17 => 1
  | 19 => 9
  | 23 => 11
  | 29 => 4
  | 31 => 15
  | 37 => 34
  | 41 => 4
  | 43 => 21
  | 47 => 23
  | 53 => 44
  | 59 => 29
  | 61 => 26
  | 67 => 33
  | 71 => 35
  | 73 => 39
  | 79 => 39
  | 83 => 41
  | 89 => 51
  | 97 => 4
  | 101 => 25
  | 103 => 51
  | 107 => 53
  | 109 => 89
  | 113 => 13
  | 127 => 63
  | 131 => 65
  | 137 => 40
  | 139 => 69
  | 149 => 64
  | 151 => 75
  | 157 => 9
  | 163 => 81
  | 167 => 26
  | 173 => 15
  | 179 => 1
  | 181 => 39
  | 191 => 41
  | 193 => 28
  | 197 => 5
  | 199 => 28
  | 211 => 9
  | 223 => 35
  | 227 => 24
  | 229 => 55
  | 233 => 64
  | 239 => 46
  | 241 => 13
  | 251 => 19
  | 257 => 77
  | 263 => 1
  | 269 => 14
  | 271 => 25
  | 277 => 26
  | 281 => 5
  | 283 => 31
  | 293 => 17
  | 307 => 11
  | 311 => 3
  | 313 => 16
  | 317 => 1
  | 331 => 9
  | 337 => 19
  | 347 => 7
  | 349 => 41
  | 353 => 11
  | 359 => 14
  | 367 => 14
  | 373 => 9
  | 379 => 25
  | 383 => 4
  | 389 => 5
  | 397 => 9
  | 401 => 3
  | 409 => 17
  | 419 => 10
  | 421 => 10
  | 431 => 5
  | 433 => 1
  | 439 => 5
  | 443 => 5
  | _ => 0

theorem length_ok : offsets.length = 447 := by decide +kernel
theorem nodup_ok : offsets.Nodup := by decide +kernel
theorem bounds_ok : ∀ x ∈ offsets, x ≤ 3158 ∧ x % 2 = 0 := by decide +kernel

private def trialDivisors : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19]

private def qCandidate (q : ℕ) : Prop :=
  2 ≤ q ∧ ∀ d ∈ trialDivisors, d = q ∨ q % d ≠ 0

private instance qCandidateDecidable (q : ℕ) : Decidable (qCandidate q) := by
  unfold qCandidate trialDivisors
  infer_instance

private theorem prime_candidate (q : ℕ) (hq : q.Prime) : qCandidate q := by
  refine ⟨hq.two_le, ?_⟩
  intro d hd
  have hd2 : 2 ≤ d := (show ∀ d ∈ trialDivisors, 2 ≤ d by decide +kernel) d hd
  by_cases heq : d = q
  · exact Or.inl heq
  · right
    intro hmod
    have hdiv := hq.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod)
    omega

private theorem candidate_moduli_ok : ∀ q ∈ List.range 448, qCandidate q →
    omitted q < q ∧ ∀ x ∈ offsets, x % q ≠ omitted q := by decide +kernel

theorem small_moduli_ok : ∀ q ∈ List.range 448, q.Prime →
    omitted q < q ∧ ∀ x ∈ offsets, x % q ≠ omitted q := by
  intro q hq hprime
  exact candidate_moduli_ok q hq (prime_candidate q hprime)

def raw (i : Fin 447) : ℕ := offsets.get (Fin.cast length_ok.symm i)
def tuple (i : Fin 447) : ℕ := raw i / 2

theorem raw_mem (i : Fin 447) : raw i ∈ offsets :=
  List.get_mem _ _

theorem double_tuple (i : Fin 447) : 2 * tuple i = raw i := by
  have h := (bounds_ok (raw i) (raw_mem i)).2
  dsimp [tuple]
  omega

theorem tuple_zero : tuple 0 = 0 := by decide +kernel

theorem tuple_injective : Function.Injective tuple := by
  intro i j hij
  have hraw : raw i = raw j := by rw [← double_tuple i, ← double_tuple j, hij]
  have hget := (List.nodup_iff_injective_get.mp nodup_ok) hraw
  apply Fin.ext
  exact congrArg Fin.val hget

theorem tuple_bound (i : Fin 447) : 2 * tuple i ≤ 3158 := by
  rw [double_tuple]
  exact (bounds_ok (raw i) (raw_mem i)).1

theorem tuple_admissible : HardyLittlewood.IsAdmissibleTuple tuple := by
  intro q hq hs
  haveI : NeZero q := ⟨hq.ne_zero⟩
  by_cases hsmall : q ≤ 447
  · have hc := small_moduli_ok q (List.mem_range.mpr (by omega)) hq
    obtain ⟨i, hi⟩ := hs (omitted q : ZMod q)
    have heq : ((2 * tuple i : ℕ) : ZMod q) = (omitted q : ZMod q) := by
      exact_mod_cast hi
    rw [ZMod.natCast_eq_natCast_iff'] at heq
    rw [Nat.mod_eq_of_lt hc.1, double_tuple] at heq
    exact hc.2 (raw i) (raw_mem i) heq
  · have hcard := Fintype.card_le_of_surjective _ hs
    simp only [Fintype.card_fin, ZMod.card] at hcard
    omega

end HLRichardsCert



set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HLRichardsFastSieve

private def smallPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53}

private theorem smallPrimes_two_le : ∀ d ∈ smallPrimes, 2 ≤ d := by decide +kernel

private def candidate (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ d ∈ smallPrimes, d = n ∨ n % d ≠ 0

private instance candidateDecidable (n : ℕ) : Decidable (candidate n) := by
  unfold candidate
  infer_instance

theorem prime_is_candidate (n : ℕ) (hp : n.Prime) : candidate n := by
  refine ⟨hp.two_le, ?_⟩
  intro d hd
  have hd2 := smallPrimes_two_le d hd
  by_cases hdn : d = n
  · exact Or.inl hdn
  · right
    intro hdvd
    have h := hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hdvd)
    omega

theorem candidate_count : ((Finset.range 3160).filter candidate).card = 446 := by decide +kernel

theorem primeCounting_le : HardyLittlewood.primeCounting 3159 ≤ 446 := by
  classical
  have hs : {p : ℕ | p ≤ 3159 ∧ p.Prime} =
      (((Finset.range 3160).filter Nat.Prime : Finset ℕ) : Set ℕ) := by
    ext p
    change (p ≤ 3159 ∧ p.Prime) ↔ p ∈ (Finset.range 3160).filter Nat.Prime
    rw [Finset.mem_filter, Finset.mem_range]
    exact and_congr_left (fun _ => by omega)
  have hsub : (Finset.range 3160).filter Nat.Prime ⊆
      (Finset.range 3160).filter candidate := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpr, hprime⟩
    exact Finset.mem_filter.mpr ⟨hpr, prime_is_candidate p hprime⟩
  have hc := Finset.card_le_card hsub
  rw [candidate_count] at hc
  simpa only [HardyLittlewood.primeCounting, hs, Set.ncard_coe_finset] using hc


end HLRichardsFastSieve


open HardyLittlewood

namespace HLRichards

private def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

private theorem mem_primesUpTo (n a : ℕ) :
    a ∈ primesUpTo n ↔ a ≤ n ∧ a.Prime := by
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
  exact and_congr_left (fun _ => Nat.lt_succ_iff)

private theorem count_eq_card (n : ℕ) :
    primeCounting n = (primesUpTo n).card := by
  unfold primeCounting
  have hs : {a : ℕ | a ≤ n ∧ a.Prime} = (primesUpTo n : Set ℕ) := by
    ext a
    exact (mem_primesUpTo n a).symm
  rw [hs, Set.ncard_coe_finset]

/-- A finite admissible pattern denser than the initial prime segment is
incompatible with universal prime-counting subadditivity once that pattern
occurs arbitrarily far out. The analytic infinitude theorem is an explicit
argument of this purely combinatorial bridge. -/
theorem contradiction_from_dense_tuple {k : ℕ} (m : Fin k.succ → ℕ)
    (H : ℕ) (hH : 1 ≤ H)
    (hinj : Function.Injective m) (hbound : ∀ i, 2 * m i ≤ H)
    (hdense : primeCounting (H + 1) < k + 1)
    (hinf : ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ IsPrimeConstellation m p)
    (hsecond : ∀ x y : ℕ, 2 ≤ x → 2 ≤ y → secondHardyLittlewoodFor x y) :
    False := by
  classical
  obtain ⟨p, hp, hconst⟩ := hinf 3
  have hprime : ∀ i : Fin k.succ, (p + 2 * m i).Prime := hconst.2.2
  let x := p - 1
  let y := H + 1
  let Q : Finset ℕ := Finset.univ.image (fun i : Fin k.succ => p + 2 * m i)
  have hmap : Function.Injective (fun i : Fin k.succ => p + 2 * m i) := by
    intro i j hij
    apply hinj
    change p + 2 * m i = p + 2 * m j at hij
    omega
  have hQ : Q.card = k + 1 := by
    rw [Finset.card_image_of_injective _ hmap]
    simp
  have hdisjoint : Disjoint (primesUpTo x) Q := by
    apply Finset.disjoint_left.mpr
    intro a ha haQ
    have hax := (mem_primesUpTo x a).mp ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp haQ
    dsimp [x] at hax
    omega
  have hsub : primesUpTo x ∪ Q ⊆ primesUpTo (x + y) := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases (mem_primesUpTo x a).mp ha with ⟨hax, hap⟩
      exact (mem_primesUpTo (x + y) a).mpr ⟨by omega, hap⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      apply (mem_primesUpTo (x + y) (p + 2 * m i)).mpr
      refine ⟨?_, hprime i⟩
      have hi := hbound i
      dsimp [x, y]
      omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisjoint, hQ] at hc
  have hcard : primeCounting x + (k + 1) ≤ primeCounting (x + y) := by
    simpa only [count_eq_card] using hc
  have hx : 2 ≤ x := by dsimp [x]; omega
  have hy : 2 ≤ y := by dsimp [y]; omega
  have hupper := hsecond x y hx hy
  change primeCounting (x + y) ≤ primeCounting x + primeCounting y at hupper
  change primeCounting y < k + 1 at hdense
  omega


end HLRichards


open HardyLittlewood

/-- Richards' incompatibility theorem, using Engelsma's explicit finite
admissible pattern and the mission's previously verified infinitude lemma. -/
theorem solution
    (h1 : ∀ (k : ℕ) (m : Fin k.succ → ℕ), firstHardyLittlewoodFor m)
    (h2 : ∀ (x y : ℕ), 2 ≤ x → 2 ≤ y → secondHardyLittlewoodFor x y) :
    False := by
  apply HLRichards.contradiction_from_dense_tuple (k := 446)
    HLRichardsCert.tuple 3158 (by decide)
    HLRichardsCert.tuple_injective HLRichardsCert.tuple_bound
  · change HardyLittlewood.primeCounting 3159 < 447
    have hc := HLRichardsFastSieve.primeCounting_le
    omega
  · intro N
    exact first_implies_infinite_constellations HLRichardsCert.tuple
      HLRichardsCert.tuple_zero HLRichardsCert.tuple_injective
      HLRichardsCert.tuple_admissible (h1 446 HLRichardsCert.tuple) N
  · exact h2

#print axioms solution
