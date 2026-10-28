-- Prove2me | solution 1 for OAI.OddGoldbach23.pair_quarter_1
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:50:14.137262+00:00
-- url     : https://prove2.me/submissions/5a3deb3c-aa06-43cb-9821-619e8d92d3e8

import Definitions.Def_OAI_OddGoldbach23_CertificateData
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
set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 10000
namespace OAI.OddGoldbach23.Cert
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
def rowW (a : ℕ) : ℕ := (Qlist.map fun b => if b < a then WP (a-b) else 0).sum
theorem chunk25 : (Qc25.map rowW).sum ≤ 4410383 := by decide +kernel
theorem chunk26 : (Qc26.map rowW).sum ≤ 4581510 := by decide +kernel
theorem chunk27 : (Qc27.map rowW).sum ≤ 4747506 := by decide +kernel
theorem chunk28 : (Qc28.map rowW).sum ≤ 4929051 := by decide +kernel
theorem chunk29 : (Qc29.map rowW).sum ≤ 5115544 := by decide +kernel
theorem chunk30 : (Qc30.map rowW).sum ≤ 5273740 := by decide +kernel
theorem chunk31 : (Qc31.map rowW).sum ≤ 5454387 := by decide +kernel
theorem chunk32 : (Qc32.map rowW).sum ≤ 5623360 := by decide +kernel
theorem chunk33 : (Qc33.map rowW).sum ≤ 5800442 := by decide +kernel
theorem chunk34 : (Qc34.map rowW).sum ≤ 5973751 := by decide +kernel
theorem chunk35 : (Qc35.map rowW).sum ≤ 6154952 := by decide +kernel
theorem chunk36 : (Qc36.map rowW).sum ≤ 6323291 := by decide +kernel
theorem chunk37 : (Qc37.map rowW).sum ≤ 6504540 := by decide +kernel
theorem chunk38 : (Qc38.map rowW).sum ≤ 6668707 := by decide +kernel
theorem chunk39 : (Qc39.map rowW).sum ≤ 6841002 := by decide +kernel
theorem chunk40 : (Qc40.map rowW).sum ≤ 7028735 := by decide +kernel
theorem chunk41 : (Qc41.map rowW).sum ≤ 7215797 := by decide +kernel
theorem chunk42 : (Qc42.map rowW).sum ≤ 7387566 := by decide +kernel
theorem chunk43 : (Qc43.map rowW).sum ≤ 7525173 := by decide +kernel
theorem chunk44 : (Qc44.map rowW).sum ≤ 7705959 := by decide +kernel
theorem chunk45 : (Qc45.map rowW).sum ≤ 7903600 := by decide +kernel
theorem chunk46 : (Qc46.map rowW).sum ≤ 8042444 := by decide +kernel
theorem chunk47 : (Qc47.map rowW).sum ≤ 8251594 := by decide +kernel
theorem chunk48 : (Qc48.map rowW).sum ≤ 8407466 := by decide +kernel
theorem chunk49 : (Qc49.map rowW).sum ≤ 8589743 := by decide +kernel
end OAI.OddGoldbach23.Cert
open OAI.OddGoldbach23.Cert
theorem solution : (((OAI.OddGoldbach23.Cert.Qlist.drop 250).take 250).map (fun a => (OAI.OddGoldbach23.Cert.Qlist.map (fun b => if b < a then OAI.OddGoldbach23.Cert.WP (a-b) else 0)).sum)).sum ≤ 162460243 := by
  change (((OAI.OddGoldbach23.Cert.Qlist.drop 250).take 250).map rowW).sum ≤ 162460243
  have h : (OAI.OddGoldbach23.Cert.Qlist.drop 250).take 250 = Qc25 ++ Qc26 ++ Qc27 ++ Qc28 ++ Qc29 ++ Qc30 ++ Qc31 ++ Qc32 ++ Qc33 ++ Qc34 ++ Qc35 ++ Qc36 ++ Qc37 ++ Qc38 ++ Qc39 ++ Qc40 ++ Qc41 ++ Qc42 ++ Qc43 ++ Qc44 ++ Qc45 ++ Qc46 ++ Qc47 ++ Qc48 ++ Qc49 := by decide +kernel
  rw [h]
  simp only [List.map_append, List.sum_append]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add chunk25 chunk26) chunk27) chunk28) chunk29) chunk30) chunk31) chunk32) chunk33) chunk34) chunk35) chunk36) chunk37) chunk38) chunk39) chunk40) chunk41) chunk42) chunk43) chunk44) chunk45) chunk46) chunk47) chunk48) chunk49).trans_eq (by norm_num)
#print axioms solution
