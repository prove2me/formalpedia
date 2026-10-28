-- Prove2me | solution 1 for OAI.OddGoldbach23.pair_quarter_0
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:50:12.93581+00:00
-- url     : https://prove2.me/submissions/5c71ebbc-72cc-4cdc-84c6-328b33e9989d

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
def rowW (a : ℕ) : ℕ := (Qlist.map fun b => if b < a then WP (a-b) else 0).sum
theorem chunk0 : (Qc0.map rowW).sum ≤ 64098 := by decide +kernel
theorem chunk1 : (Qc1.map rowW).sum ≤ 233006 := by decide +kernel
theorem chunk2 : (Qc2.map rowW).sum ≤ 404738 := by decide +kernel
theorem chunk3 : (Qc3.map rowW).sum ≤ 579936 := by decide +kernel
theorem chunk4 : (Qc4.map rowW).sum ≤ 747806 := by decide +kernel
theorem chunk5 : (Qc5.map rowW).sum ≤ 928731 := by decide +kernel
theorem chunk6 : (Qc6.map rowW).sum ≤ 1101396 := by decide +kernel
theorem chunk7 : (Qc7.map rowW).sum ≤ 1270118 := by decide +kernel
theorem chunk8 : (Qc8.map rowW).sum ≤ 1445724 := by decide +kernel
theorem chunk9 : (Qc9.map rowW).sum ≤ 1621789 := by decide +kernel
theorem chunk10 : (Qc10.map rowW).sum ≤ 1801282 := by decide +kernel
theorem chunk11 : (Qc11.map rowW).sum ≤ 1967635 := by decide +kernel
theorem chunk12 : (Qc12.map rowW).sum ≤ 2137977 := by decide +kernel
theorem chunk13 : (Qc13.map rowW).sum ≤ 2318394 := by decide +kernel
theorem chunk14 : (Qc14.map rowW).sum ≤ 2491819 := by decide +kernel
theorem chunk15 : (Qc15.map rowW).sum ≤ 2672100 := by decide +kernel
theorem chunk16 : (Qc16.map rowW).sum ≤ 2849132 := by decide +kernel
theorem chunk17 : (Qc17.map rowW).sum ≤ 2998028 := by decide +kernel
theorem chunk18 : (Qc18.map rowW).sum ≤ 3190432 := by decide +kernel
theorem chunk19 : (Qc19.map rowW).sum ≤ 3374913 := by decide +kernel
theorem chunk20 : (Qc20.map rowW).sum ≤ 3526648 := by decide +kernel
theorem chunk21 : (Qc21.map rowW).sum ≤ 3720049 := by decide +kernel
theorem chunk22 : (Qc22.map rowW).sum ≤ 3882745 := by decide +kernel
theorem chunk23 : (Qc23.map rowW).sum ≤ 4066261 := by decide +kernel
theorem chunk24 : (Qc24.map rowW).sum ≤ 4224612 := by decide +kernel
end OAI.OddGoldbach23.Cert
open OAI.OddGoldbach23.Cert
theorem solution : (((OAI.OddGoldbach23.Cert.Qlist.drop 0).take 250).map (fun a => (OAI.OddGoldbach23.Cert.Qlist.map (fun b => if b < a then OAI.OddGoldbach23.Cert.WP (a-b) else 0)).sum)).sum ≤ 53619369 := by
  change (((OAI.OddGoldbach23.Cert.Qlist.drop 0).take 250).map rowW).sum ≤ 53619369
  have h : (OAI.OddGoldbach23.Cert.Qlist.drop 0).take 250 = Qc0 ++ Qc1 ++ Qc2 ++ Qc3 ++ Qc4 ++ Qc5 ++ Qc6 ++ Qc7 ++ Qc8 ++ Qc9 ++ Qc10 ++ Qc11 ++ Qc12 ++ Qc13 ++ Qc14 ++ Qc15 ++ Qc16 ++ Qc17 ++ Qc18 ++ Qc19 ++ Qc20 ++ Qc21 ++ Qc22 ++ Qc23 ++ Qc24 := by decide +kernel
  rw [h]
  simp only [List.map_append, List.sum_append]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add chunk0 chunk1) chunk2) chunk3) chunk4) chunk5) chunk6) chunk7) chunk8) chunk9) chunk10) chunk11) chunk12) chunk13) chunk14) chunk15) chunk16) chunk17) chunk18) chunk19) chunk20) chunk21) chunk22) chunk23) chunk24).trans_eq (by norm_num)
#print axioms solution
