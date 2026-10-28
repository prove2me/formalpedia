-- Prove2me | solution 1 for OAI.OddGoldbach23.finite_sieve_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:45:48.067901+00:00
-- url     : https://prove2.me/submissions/2e6ffca0-db78-43ae-93a9-bc1793b1bf07

import Theorems.Thm_OAI_OddGoldbach23_table_certificate
import Theorems.Thm_OAI_OddGoldbach23_pair_sum_certificate
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
open Finset Real
namespace P27
noncomputable def Kf (s : ℕ) : ℝ :=
  ∏ p ∈ s.primeFactors, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1


set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000
def Qc0 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
def Qc1 : List ℕ := [37, 41, 43, 47, 53, 59, 61, 67, 71, 73]
def Qc2 : List ℕ := [79, 83, 89, 97, 101, 103, 107, 109, 113, 127]
def Qc3 : List ℕ := [131, 137, 139, 149, 151, 157, 163, 167, 173, 179]
def Qc4 : List ℕ := [181, 191, 193, 197, 199, 211, 223, 227, 229, 233]
def Qc5 : List ℕ := [239, 241, 251, 257, 263, 269, 271, 277, 281, 283]
def Qc6 : List ℕ := [293, 307, 311, 313, 317, 331, 337, 347, 349, 353]
def Qc7 : List ℕ := [359, 367, 373, 379, 383, 389, 397, 401, 409, 419]
def Qc8 : List ℕ := [421, 431, 433, 439, 443, 449, 457, 461, 463, 467]
def Qc9 : List ℕ := [479, 487, 491, 499, 503, 509, 521, 523, 541, 547]
def Qc10 : List ℕ := [557, 563, 569, 571, 577, 587, 593, 599, 601, 607]
def Qc11 : List ℕ := [613, 617, 619, 631, 641, 643, 647, 653, 659, 661]
def Qc12 : List ℕ := [673, 677, 683, 691, 701, 709, 719, 727, 733, 739]
def Qc13 : List ℕ := [743, 751, 757, 761, 769, 773, 787, 797, 809, 811]
def Qc14 : List ℕ := [821, 823, 827, 829, 839, 853, 857, 859, 863, 877]
def Qc15 : List ℕ := [881, 883, 887, 907, 911, 919, 929, 937, 941, 947]
def Qc16 : List ℕ := [953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019]
def Qc17 : List ℕ := [1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087]
def Qc18 : List ℕ := [1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153]
def Qc19 : List ℕ := [1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229]
def Qc20 : List ℕ := [1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297]
def Qc21 : List ℕ := [1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381]
def Qc22 : List ℕ := [1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453]
def Qc23 : List ℕ := [1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523]
def Qc24 : List ℕ := [1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597]
def Qc25 : List ℕ := [1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663]
def Qc26 : List ℕ := [1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741]
def Qc27 : List ℕ := [1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823]
def Qc28 : List ℕ := [1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901]
def Qc29 : List ℕ := [1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993]
def Qc30 : List ℕ := [1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063]
def Qc31 : List ℕ := [2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131]
def Qc32 : List ℕ := [2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221]
def Qc33 : List ℕ := [2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293]
def Qc34 : List ℕ := [2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371]
def Qc35 : List ℕ := [2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437]
def Qc36 : List ℕ := [2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539]
def Qc37 : List ℕ := [2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621]
def Qc38 : List ℕ := [2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689]
def Qc39 : List ℕ := [2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749]
def Qc40 : List ℕ := [2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833]
def Qc41 : List ℕ := [2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909]
def Qc42 : List ℕ := [2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001]
def Qc43 : List ℕ := [3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083]
def Qc44 : List ℕ := [3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187]
def Qc45 : List ℕ := [3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259]
def Qc46 : List ℕ := [3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343]
def Qc47 : List ℕ := [3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433]
def Qc48 : List ℕ := [3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517]
def Qc49 : List ℕ := [3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581]
def Qc50 : List ℕ := [3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659]
def Qc51 : List ℕ := [3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733]
def Qc52 : List ℕ := [3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823]
def Qc53 : List ℕ := [3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911]
def Qc54 : List ℕ := [3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001]
def Qc55 : List ℕ := [4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073]
def Qc56 : List ℕ := [4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153]
def Qc57 : List ℕ := [4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241]
def Qc58 : List ℕ := [4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327]
def Qc59 : List ℕ := [4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421]
def Qc60 : List ℕ := [4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507]
def Qc61 : List ℕ := [4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591]
def Qc62 : List ℕ := [4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663]
def Qc63 : List ℕ := [4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759]
def Qc64 : List ℕ := [4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861]
def Qc65 : List ℕ := [4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943]
def Qc66 : List ℕ := [4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009]
def Qc67 : List ℕ := [5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099]
def Qc68 : List ℕ := [5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189]
def Qc69 : List ℕ := [5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281]
def Qc70 : List ℕ := [5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393]
def Qc71 : List ℕ := [5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449]
def Qc72 : List ℕ := [5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527]
def Qc73 : List ℕ := [5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641]
def Qc74 : List ℕ := [5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701]
def Qc75 : List ℕ := [5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801]
def Qc76 : List ℕ := [5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861]
def Qc77 : List ℕ := [5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953]
def Qc78 : List ℕ := [5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067]
def Qc79 : List ℕ := [6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143]
def Qc80 : List ℕ := [6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229]
def Qc81 : List ℕ := [6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311]
def Qc82 : List ℕ := [6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373]
def Qc83 : List ℕ := [6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481]
def Qc84 : List ℕ := [6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577]
def Qc85 : List ℕ := [6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679]
def Qc86 : List ℕ := [6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763]
def Qc87 : List ℕ := [6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841]
def Qc88 : List ℕ := [6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947]
def Qc89 : List ℕ := [6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001]
def Qc90 : List ℕ := [7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109]
def Qc91 : List ℕ := [7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211]
def Qc92 : List ℕ := [7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307]
def Qc93 : List ℕ := [7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417]
def Qc94 : List ℕ := [7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507]
def Qc95 : List ℕ := [7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573]
def Qc96 : List ℕ := [7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649]
def Qc97 : List ℕ := [7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727]
def Qc98 : List ℕ := [7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841]
def Qc99 : List ℕ := [7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927]
abbrev Qlist := OAI.OddGoldbach23.Cert.Qlist
theorem Qlist_nodup : Qlist.Nodup := by
  have h : List.IsChain (· < ·) Qlist := by decide +kernel
  exact (List.sortedLT_iff_isChain.mpr h).nodup
def Qs : Finset ℕ := ⟨(Qlist : Multiset ℕ), Multiset.coe_nodup.2 Qlist_nodup⟩
theorem Qc0_prime : ∀ p ∈ Qc0, p.Prime := by
  simp only [Qc0, List.forall_mem_cons]
  norm_num
theorem Qc1_prime : ∀ p ∈ Qc1, p.Prime := by
  simp only [Qc1, List.forall_mem_cons]
  norm_num
theorem Qc2_prime : ∀ p ∈ Qc2, p.Prime := by
  simp only [Qc2, List.forall_mem_cons]
  norm_num
theorem Qc3_prime : ∀ p ∈ Qc3, p.Prime := by
  simp only [Qc3, List.forall_mem_cons]
  norm_num
theorem Qc4_prime : ∀ p ∈ Qc4, p.Prime := by
  simp only [Qc4, List.forall_mem_cons]
  norm_num
theorem Qc5_prime : ∀ p ∈ Qc5, p.Prime := by
  simp only [Qc5, List.forall_mem_cons]
  norm_num
theorem Qc6_prime : ∀ p ∈ Qc6, p.Prime := by
  simp only [Qc6, List.forall_mem_cons]
  norm_num
theorem Qc7_prime : ∀ p ∈ Qc7, p.Prime := by
  simp only [Qc7, List.forall_mem_cons]
  norm_num
theorem Qc8_prime : ∀ p ∈ Qc8, p.Prime := by
  simp only [Qc8, List.forall_mem_cons]
  norm_num
theorem Qc9_prime : ∀ p ∈ Qc9, p.Prime := by
  simp only [Qc9, List.forall_mem_cons]
  norm_num
theorem Qc10_prime : ∀ p ∈ Qc10, p.Prime := by
  simp only [Qc10, List.forall_mem_cons]
  norm_num
theorem Qc11_prime : ∀ p ∈ Qc11, p.Prime := by
  simp only [Qc11, List.forall_mem_cons]
  norm_num
theorem Qc12_prime : ∀ p ∈ Qc12, p.Prime := by
  simp only [Qc12, List.forall_mem_cons]
  norm_num
theorem Qc13_prime : ∀ p ∈ Qc13, p.Prime := by
  simp only [Qc13, List.forall_mem_cons]
  norm_num
theorem Qc14_prime : ∀ p ∈ Qc14, p.Prime := by
  simp only [Qc14, List.forall_mem_cons]
  norm_num
theorem Qc15_prime : ∀ p ∈ Qc15, p.Prime := by
  simp only [Qc15, List.forall_mem_cons]
  norm_num
theorem Qc16_prime : ∀ p ∈ Qc16, p.Prime := by
  simp only [Qc16, List.forall_mem_cons]
  norm_num
theorem Qc17_prime : ∀ p ∈ Qc17, p.Prime := by
  simp only [Qc17, List.forall_mem_cons]
  norm_num
theorem Qc18_prime : ∀ p ∈ Qc18, p.Prime := by
  simp only [Qc18, List.forall_mem_cons]
  norm_num
theorem Qc19_prime : ∀ p ∈ Qc19, p.Prime := by
  simp only [Qc19, List.forall_mem_cons]
  norm_num
theorem Qc20_prime : ∀ p ∈ Qc20, p.Prime := by
  simp only [Qc20, List.forall_mem_cons]
  norm_num
theorem Qc21_prime : ∀ p ∈ Qc21, p.Prime := by
  simp only [Qc21, List.forall_mem_cons]
  norm_num
theorem Qc22_prime : ∀ p ∈ Qc22, p.Prime := by
  simp only [Qc22, List.forall_mem_cons]
  norm_num
theorem Qc23_prime : ∀ p ∈ Qc23, p.Prime := by
  simp only [Qc23, List.forall_mem_cons]
  norm_num
theorem Qc24_prime : ∀ p ∈ Qc24, p.Prime := by
  simp only [Qc24, List.forall_mem_cons]
  norm_num
theorem Qc25_prime : ∀ p ∈ Qc25, p.Prime := by
  simp only [Qc25, List.forall_mem_cons]
  norm_num
theorem Qc26_prime : ∀ p ∈ Qc26, p.Prime := by
  simp only [Qc26, List.forall_mem_cons]
  norm_num
theorem Qc27_prime : ∀ p ∈ Qc27, p.Prime := by
  simp only [Qc27, List.forall_mem_cons]
  norm_num
theorem Qc28_prime : ∀ p ∈ Qc28, p.Prime := by
  simp only [Qc28, List.forall_mem_cons]
  norm_num
theorem Qc29_prime : ∀ p ∈ Qc29, p.Prime := by
  simp only [Qc29, List.forall_mem_cons]
  norm_num
theorem Qc30_prime : ∀ p ∈ Qc30, p.Prime := by
  simp only [Qc30, List.forall_mem_cons]
  norm_num
theorem Qc31_prime : ∀ p ∈ Qc31, p.Prime := by
  simp only [Qc31, List.forall_mem_cons]
  norm_num
theorem Qc32_prime : ∀ p ∈ Qc32, p.Prime := by
  simp only [Qc32, List.forall_mem_cons]
  norm_num
theorem Qc33_prime : ∀ p ∈ Qc33, p.Prime := by
  simp only [Qc33, List.forall_mem_cons]
  norm_num
theorem Qc34_prime : ∀ p ∈ Qc34, p.Prime := by
  simp only [Qc34, List.forall_mem_cons]
  norm_num
theorem Qc35_prime : ∀ p ∈ Qc35, p.Prime := by
  simp only [Qc35, List.forall_mem_cons]
  norm_num
theorem Qc36_prime : ∀ p ∈ Qc36, p.Prime := by
  simp only [Qc36, List.forall_mem_cons]
  norm_num
theorem Qc37_prime : ∀ p ∈ Qc37, p.Prime := by
  simp only [Qc37, List.forall_mem_cons]
  norm_num
theorem Qc38_prime : ∀ p ∈ Qc38, p.Prime := by
  simp only [Qc38, List.forall_mem_cons]
  norm_num
theorem Qc39_prime : ∀ p ∈ Qc39, p.Prime := by
  simp only [Qc39, List.forall_mem_cons]
  norm_num
theorem Qc40_prime : ∀ p ∈ Qc40, p.Prime := by
  simp only [Qc40, List.forall_mem_cons]
  norm_num
theorem Qc41_prime : ∀ p ∈ Qc41, p.Prime := by
  simp only [Qc41, List.forall_mem_cons]
  norm_num
theorem Qc42_prime : ∀ p ∈ Qc42, p.Prime := by
  simp only [Qc42, List.forall_mem_cons]
  norm_num
theorem Qc43_prime : ∀ p ∈ Qc43, p.Prime := by
  simp only [Qc43, List.forall_mem_cons]
  norm_num
theorem Qc44_prime : ∀ p ∈ Qc44, p.Prime := by
  simp only [Qc44, List.forall_mem_cons]
  norm_num
theorem Qc45_prime : ∀ p ∈ Qc45, p.Prime := by
  simp only [Qc45, List.forall_mem_cons]
  norm_num
theorem Qc46_prime : ∀ p ∈ Qc46, p.Prime := by
  simp only [Qc46, List.forall_mem_cons]
  norm_num
theorem Qc47_prime : ∀ p ∈ Qc47, p.Prime := by
  simp only [Qc47, List.forall_mem_cons]
  norm_num
theorem Qc48_prime : ∀ p ∈ Qc48, p.Prime := by
  simp only [Qc48, List.forall_mem_cons]
  norm_num
theorem Qc49_prime : ∀ p ∈ Qc49, p.Prime := by
  simp only [Qc49, List.forall_mem_cons]
  norm_num
theorem Qc50_prime : ∀ p ∈ Qc50, p.Prime := by
  simp only [Qc50, List.forall_mem_cons]
  norm_num
theorem Qc51_prime : ∀ p ∈ Qc51, p.Prime := by
  simp only [Qc51, List.forall_mem_cons]
  norm_num
theorem Qc52_prime : ∀ p ∈ Qc52, p.Prime := by
  simp only [Qc52, List.forall_mem_cons]
  norm_num
theorem Qc53_prime : ∀ p ∈ Qc53, p.Prime := by
  simp only [Qc53, List.forall_mem_cons]
  norm_num
theorem Qc54_prime : ∀ p ∈ Qc54, p.Prime := by
  simp only [Qc54, List.forall_mem_cons]
  norm_num
theorem Qc55_prime : ∀ p ∈ Qc55, p.Prime := by
  simp only [Qc55, List.forall_mem_cons]
  norm_num
theorem Qc56_prime : ∀ p ∈ Qc56, p.Prime := by
  simp only [Qc56, List.forall_mem_cons]
  norm_num
theorem Qc57_prime : ∀ p ∈ Qc57, p.Prime := by
  simp only [Qc57, List.forall_mem_cons]
  norm_num
theorem Qc58_prime : ∀ p ∈ Qc58, p.Prime := by
  simp only [Qc58, List.forall_mem_cons]
  norm_num
theorem Qc59_prime : ∀ p ∈ Qc59, p.Prime := by
  simp only [Qc59, List.forall_mem_cons]
  norm_num
theorem Qc60_prime : ∀ p ∈ Qc60, p.Prime := by
  simp only [Qc60, List.forall_mem_cons]
  norm_num
theorem Qc61_prime : ∀ p ∈ Qc61, p.Prime := by
  simp only [Qc61, List.forall_mem_cons]
  norm_num
theorem Qc62_prime : ∀ p ∈ Qc62, p.Prime := by
  simp only [Qc62, List.forall_mem_cons]
  norm_num
theorem Qc63_prime : ∀ p ∈ Qc63, p.Prime := by
  simp only [Qc63, List.forall_mem_cons]
  norm_num
theorem Qc64_prime : ∀ p ∈ Qc64, p.Prime := by
  simp only [Qc64, List.forall_mem_cons]
  norm_num
theorem Qc65_prime : ∀ p ∈ Qc65, p.Prime := by
  simp only [Qc65, List.forall_mem_cons]
  norm_num
theorem Qc66_prime : ∀ p ∈ Qc66, p.Prime := by
  simp only [Qc66, List.forall_mem_cons]
  norm_num
theorem Qc67_prime : ∀ p ∈ Qc67, p.Prime := by
  simp only [Qc67, List.forall_mem_cons]
  norm_num
theorem Qc68_prime : ∀ p ∈ Qc68, p.Prime := by
  simp only [Qc68, List.forall_mem_cons]
  norm_num
theorem Qc69_prime : ∀ p ∈ Qc69, p.Prime := by
  simp only [Qc69, List.forall_mem_cons]
  norm_num
theorem Qc70_prime : ∀ p ∈ Qc70, p.Prime := by
  simp only [Qc70, List.forall_mem_cons]
  norm_num
theorem Qc71_prime : ∀ p ∈ Qc71, p.Prime := by
  simp only [Qc71, List.forall_mem_cons]
  norm_num
theorem Qc72_prime : ∀ p ∈ Qc72, p.Prime := by
  simp only [Qc72, List.forall_mem_cons]
  norm_num
theorem Qc73_prime : ∀ p ∈ Qc73, p.Prime := by
  simp only [Qc73, List.forall_mem_cons]
  norm_num
theorem Qc74_prime : ∀ p ∈ Qc74, p.Prime := by
  simp only [Qc74, List.forall_mem_cons]
  norm_num
theorem Qc75_prime : ∀ p ∈ Qc75, p.Prime := by
  simp only [Qc75, List.forall_mem_cons]
  norm_num
theorem Qc76_prime : ∀ p ∈ Qc76, p.Prime := by
  simp only [Qc76, List.forall_mem_cons]
  norm_num
theorem Qc77_prime : ∀ p ∈ Qc77, p.Prime := by
  simp only [Qc77, List.forall_mem_cons]
  norm_num
theorem Qc78_prime : ∀ p ∈ Qc78, p.Prime := by
  simp only [Qc78, List.forall_mem_cons]
  norm_num
theorem Qc79_prime : ∀ p ∈ Qc79, p.Prime := by
  simp only [Qc79, List.forall_mem_cons]
  norm_num
theorem Qc80_prime : ∀ p ∈ Qc80, p.Prime := by
  simp only [Qc80, List.forall_mem_cons]
  norm_num
theorem Qc81_prime : ∀ p ∈ Qc81, p.Prime := by
  simp only [Qc81, List.forall_mem_cons]
  norm_num
theorem Qc82_prime : ∀ p ∈ Qc82, p.Prime := by
  simp only [Qc82, List.forall_mem_cons]
  norm_num
theorem Qc83_prime : ∀ p ∈ Qc83, p.Prime := by
  simp only [Qc83, List.forall_mem_cons]
  norm_num
theorem Qc84_prime : ∀ p ∈ Qc84, p.Prime := by
  simp only [Qc84, List.forall_mem_cons]
  norm_num
theorem Qc85_prime : ∀ p ∈ Qc85, p.Prime := by
  simp only [Qc85, List.forall_mem_cons]
  norm_num
theorem Qc86_prime : ∀ p ∈ Qc86, p.Prime := by
  simp only [Qc86, List.forall_mem_cons]
  norm_num
theorem Qc87_prime : ∀ p ∈ Qc87, p.Prime := by
  simp only [Qc87, List.forall_mem_cons]
  norm_num
theorem Qc88_prime : ∀ p ∈ Qc88, p.Prime := by
  simp only [Qc88, List.forall_mem_cons]
  norm_num
theorem Qc89_prime : ∀ p ∈ Qc89, p.Prime := by
  simp only [Qc89, List.forall_mem_cons]
  norm_num
theorem Qc90_prime : ∀ p ∈ Qc90, p.Prime := by
  simp only [Qc90, List.forall_mem_cons]
  norm_num
theorem Qc91_prime : ∀ p ∈ Qc91, p.Prime := by
  simp only [Qc91, List.forall_mem_cons]
  norm_num
theorem Qc92_prime : ∀ p ∈ Qc92, p.Prime := by
  simp only [Qc92, List.forall_mem_cons]
  norm_num
theorem Qc93_prime : ∀ p ∈ Qc93, p.Prime := by
  simp only [Qc93, List.forall_mem_cons]
  norm_num
theorem Qc94_prime : ∀ p ∈ Qc94, p.Prime := by
  simp only [Qc94, List.forall_mem_cons]
  norm_num
theorem Qc95_prime : ∀ p ∈ Qc95, p.Prime := by
  simp only [Qc95, List.forall_mem_cons]
  norm_num
theorem Qc96_prime : ∀ p ∈ Qc96, p.Prime := by
  simp only [Qc96, List.forall_mem_cons]
  norm_num
theorem Qc97_prime : ∀ p ∈ Qc97, p.Prime := by
  simp only [Qc97, List.forall_mem_cons]
  norm_num
theorem Qc98_prime : ∀ p ∈ Qc98, p.Prime := by
  simp only [Qc98, List.forall_mem_cons]
  norm_num
theorem Qc99_prime : ∀ p ∈ Qc99, p.Prime := by
  simp only [Qc99, List.forall_mem_cons]
  norm_num
theorem Qlist_prime : ∀ p ∈ Qlist, p.Prime := List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨Qc0_prime, Qc1_prime⟩, Qc2_prime⟩, Qc3_prime⟩, Qc4_prime⟩, Qc5_prime⟩, Qc6_prime⟩, Qc7_prime⟩, Qc8_prime⟩, Qc9_prime⟩, Qc10_prime⟩, Qc11_prime⟩, Qc12_prime⟩, Qc13_prime⟩, Qc14_prime⟩, Qc15_prime⟩, Qc16_prime⟩, Qc17_prime⟩, Qc18_prime⟩, Qc19_prime⟩, Qc20_prime⟩, Qc21_prime⟩, Qc22_prime⟩, Qc23_prime⟩, Qc24_prime⟩, Qc25_prime⟩, Qc26_prime⟩, Qc27_prime⟩, Qc28_prime⟩, Qc29_prime⟩, Qc30_prime⟩, Qc31_prime⟩, Qc32_prime⟩, Qc33_prime⟩, Qc34_prime⟩, Qc35_prime⟩, Qc36_prime⟩, Qc37_prime⟩, Qc38_prime⟩, Qc39_prime⟩, Qc40_prime⟩, Qc41_prime⟩, Qc42_prime⟩, Qc43_prime⟩, Qc44_prime⟩, Qc45_prime⟩, Qc46_prime⟩, Qc47_prime⟩, Qc48_prime⟩, Qc49_prime⟩, Qc50_prime⟩, Qc51_prime⟩, Qc52_prime⟩, Qc53_prime⟩, Qc54_prime⟩, Qc55_prime⟩, Qc56_prime⟩, Qc57_prime⟩, Qc58_prime⟩, Qc59_prime⟩, Qc60_prime⟩, Qc61_prime⟩, Qc62_prime⟩, Qc63_prime⟩, Qc64_prime⟩, Qc65_prime⟩, Qc66_prime⟩, Qc67_prime⟩, Qc68_prime⟩, Qc69_prime⟩, Qc70_prime⟩, Qc71_prime⟩, Qc72_prime⟩, Qc73_prime⟩, Qc74_prime⟩, Qc75_prime⟩, Qc76_prime⟩, Qc77_prime⟩, Qc78_prime⟩, Qc79_prime⟩, Qc80_prime⟩, Qc81_prime⟩, Qc82_prime⟩, Qc83_prime⟩, Qc84_prime⟩, Qc85_prime⟩, Qc86_prime⟩, Qc87_prime⟩, Qc88_prime⟩, Qc89_prime⟩, Qc90_prime⟩, Qc91_prime⟩, Qc92_prime⟩, Qc93_prime⟩, Qc94_prime⟩, Qc95_prime⟩, Qc96_prime⟩, Qc97_prime⟩, Qc98_prime⟩, Qc99_prime⟩
theorem Qs_prop (p : ℕ) (hp : p ∈ Qs) : p.Prime ∧ p ≠ 2 ∧ p ≤ 7927 := by
  have hp' : p ∈ Qlist := Multiset.mem_coe.1 (Finset.mem_def.1 hp)
  refine ⟨Qlist_prime p hp', ?_, ?_⟩
  · have : ∀ q ∈ Qlist, q ≠ 2 := by decide +kernel
    exact this p hp'
  · have : ∀ q ∈ Qlist, q ≤ 7927 := by decide +kernel
    exact this p hp'
theorem Qs_card : Qs.card = 1000 := by decide +kernel
abbrev KR := OAI.OddGoldbach23.Cert.KR
abbrev WC := OAI.OddGoldbach23.Cert.WC
lemma kr_cast (d : ℕ) : (KR d : ℝ) = Kf d := by
  simp only [KR, OAI.OddGoldbach23.Cert.KR, Kf, Rat.cast_prod]
  apply prod_congr rfl
  intro p hp
  split_ifs <;> push_cast <;> rfl
lemma wc_bound (d : ℕ) : Kf d ≤ (WC d : ℝ) / 1000 := by
  have h : 1000 * KR d ≤ (WC d : ℚ) := by
    have hi : (⌈1000 * KR d⌉ : ℤ) ≤ (WC d : ℤ) := by unfold WC OAI.OddGoldbach23.Cert.WC KR; omega
    exact (Int.le_ceil _).trans (by exact_mod_cast hi)
  have hr : (1000 : ℝ) * (KR d : ℝ) ≤ (WC d : ℝ) := by exact_mod_cast h
  rw [kr_cast] at hr
  linarith
abbrev WP := OAI.OddGoldbach23.Cert.WP
lemma wp_bound (d : ℕ) (hd : d < 7928) : Kf d ≤ (WP d : ℝ) / 1000 := by
  have h : (WC d : ℝ) ≤ WP d := by exact_mod_cast OAI.OddGoldbach23.table_certificate d hd
  linarith [wc_bound d]
def rowW (a : ℕ) : ℕ := (Qlist.map fun b => if b < a then WP (a-b) else 0).sum
theorem sum_Qs {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∑ a ∈ Qs, f a = (Qlist.map f).sum := by
  show Multiset.sum (Multiset.map f (Qlist : Multiset ℕ)) = _
  rw [Multiset.map_coe, Multiset.sum_coe]
theorem Qlist_eq : Qlist = Qc0 ++ Qc1 ++ Qc2 ++ Qc3 ++ Qc4 ++ Qc5 ++ Qc6 ++ Qc7 ++ Qc8 ++ Qc9 ++ Qc10 ++ Qc11 ++ Qc12 ++ Qc13 ++ Qc14 ++ Qc15 ++ Qc16 ++ Qc17 ++ Qc18 ++ Qc19 ++ Qc20 ++ Qc21 ++ Qc22 ++ Qc23 ++ Qc24 ++ Qc25 ++ Qc26 ++ Qc27 ++ Qc28 ++ Qc29 ++ Qc30 ++ Qc31 ++ Qc32 ++ Qc33 ++ Qc34 ++ Qc35 ++ Qc36 ++ Qc37 ++ Qc38 ++ Qc39 ++ Qc40 ++ Qc41 ++ Qc42 ++ Qc43 ++ Qc44 ++ Qc45 ++ Qc46 ++ Qc47 ++ Qc48 ++ Qc49 ++ Qc50 ++ Qc51 ++ Qc52 ++ Qc53 ++ Qc54 ++ Qc55 ++ Qc56 ++ Qc57 ++ Qc58 ++ Qc59 ++ Qc60 ++ Qc61 ++ Qc62 ++ Qc63 ++ Qc64 ++ Qc65 ++ Qc66 ++ Qc67 ++ Qc68 ++ Qc69 ++ Qc70 ++ Qc71 ++ Qc72 ++ Qc73 ++ Qc74 ++ Qc75 ++ Qc76 ++ Qc77 ++ Qc78 ++ Qc79 ++ Qc80 ++ Qc81 ++ Qc82 ++ Qc83 ++ Qc84 ++ Qc85 ++ Qc86 ++ Qc87 ++ Qc88 ++ Qc89 ++ Qc90 ++ Qc91 ++ Qc92 ++ Qc93 ++ Qc94 ++ Qc95 ++ Qc96 ++ Qc97 ++ Qc98 ++ Qc99 := rfl
theorem row_eq (a : ℕ) : (∑ b ∈ Qs, if b < a then WP (a-b) else 0) = rowW a := by
  rw [sum_Qs]; rfl
theorem half_le : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then WP (a-b) else 0) ≤ 867860452 := by
  have h1 : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then WP (a-b) else 0) = (Qlist.map rowW).sum := by
    rw [sum_Qs]
    simp only [row_eq]
  rw [h1]
  exact OAI.OddGoldbach23.pair_sum_certificate
theorem T_bound : ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a-b) else 0) ≤ (867861 : ℝ) := by
  have hterm : ∀ a ∈ Qs, ∀ b ∈ Qs, (if b < a then Kf (a-b) else 0) ≤
      ((if b < a then WP (a-b) else 0 : ℕ) : ℝ) / 1000 := by
    intro a ha b hb
    have haM := (Qs_prop a ha).2.2
    split_ifs with hab
    · exact wp_bound _ (by omega)
    · simp
  have hHle : ((∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then WP (a-b) else 0 : ℕ) : ℝ) ≤ 867860452 := by
    exact_mod_cast half_le
  have hc : ((∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then WP (a-b) else 0 : ℕ) : ℝ) =
      ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then WP (a-b) else 0 : ℕ) : ℝ) := by
    rw [Nat.cast_sum]; exact sum_congr rfl fun a _ => Nat.cast_sum _ _
  have hsum := sum_le_sum (s := Qs) (fun a ha => sum_le_sum (s := Qs) (fun b hb => hterm a ha b hb))
  simp_rw [← sum_div] at hsum
  rw [← hc] at hsum
  linarith

#print axioms T_bound
end P27
theorem solution :
    ∃ Q : Finset ℕ, Q.card = 1000 ∧
    (∀ p ∈ Q, p.Prime ∧ p ≠ 2 ∧ p ≤ 7927) ∧
    (∑ a ∈ Q, ∑ b ∈ Q, if b < a then
      (∏ p ∈ (a-b).primeFactors, if 2 < p then ((p : ℝ)-1)/((p : ℝ)-2) else 1)
      else 0) ≤ (867861 : ℝ) := by
  exact ⟨P27.Qs, P27.Qs_card, P27.Qs_prop, P27.T_bound⟩

#print axioms solution
