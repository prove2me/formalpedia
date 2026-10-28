-- Prove2me | solution 1 for OAI.OddGoldbach23.pair_quarter_2
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:50:15.293286+00:00
-- url     : https://prove2.me/submissions/95f1aeb8-b83d-4574-9bba-979aaa8a5f90

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
def rowW (a : ℕ) : ℕ := (Qlist.map fun b => if b < a then WP (a-b) else 0).sum
theorem chunk50 : (Qc50.map rowW).sum ≤ 8757104 := by decide +kernel
theorem chunk51 : (Qc51.map rowW).sum ≤ 8937439 := by decide +kernel
theorem chunk52 : (Qc52.map rowW).sum ≤ 9114767 := by decide +kernel
theorem chunk53 : (Qc53.map rowW).sum ≤ 9288264 := by decide +kernel
theorem chunk54 : (Qc54.map rowW).sum ≤ 9467586 := by decide +kernel
theorem chunk55 : (Qc55.map rowW).sum ≤ 9640736 := by decide +kernel
theorem chunk56 : (Qc56.map rowW).sum ≤ 9807080 := by decide +kernel
theorem chunk57 : (Qc57.map rowW).sum ≤ 9979360 := by decide +kernel
theorem chunk58 : (Qc58.map rowW).sum ≤ 10158534 := by decide +kernel
theorem chunk59 : (Qc59.map rowW).sum ≤ 10354714 := by decide +kernel
theorem chunk60 : (Qc60.map rowW).sum ≤ 10516087 := by decide +kernel
theorem chunk61 : (Qc61.map rowW).sum ≤ 10670478 := by decide +kernel
theorem chunk62 : (Qc62.map rowW).sum ≤ 10840502 := by decide +kernel
theorem chunk63 : (Qc63.map rowW).sum ≤ 11040967 := by decide +kernel
theorem chunk64 : (Qc64.map rowW).sum ≤ 11193810 := by decide +kernel
theorem chunk65 : (Qc65.map rowW).sum ≤ 11400186 := by decide +kernel
theorem chunk66 : (Qc66.map rowW).sum ≤ 11541241 := by decide +kernel
theorem chunk67 : (Qc67.map rowW).sum ≤ 11735452 := by decide +kernel
theorem chunk68 : (Qc68.map rowW).sum ≤ 11886222 := by decide +kernel
theorem chunk69 : (Qc69.map rowW).sum ≤ 12074470 := by decide +kernel
theorem chunk70 : (Qc70.map rowW).sum ≤ 12302675 := by decide +kernel
theorem chunk71 : (Qc71.map rowW).sum ≤ 12397292 := by decide +kernel
theorem chunk72 : (Qc72.map rowW).sum ≤ 12614747 := by decide +kernel
theorem chunk73 : (Qc73.map rowW).sum ≤ 12753722 := by decide +kernel
theorem chunk74 : (Qc74.map rowW).sum ≤ 12938538 := by decide +kernel
end OAI.OddGoldbach23.Cert
open OAI.OddGoldbach23.Cert
theorem solution : (((OAI.OddGoldbach23.Cert.Qlist.drop 500).take 250).map (fun a => (OAI.OddGoldbach23.Cert.Qlist.map (fun b => if b < a then OAI.OddGoldbach23.Cert.WP (a-b) else 0)).sum)).sum ≤ 271411973 := by
  change (((OAI.OddGoldbach23.Cert.Qlist.drop 500).take 250).map rowW).sum ≤ 271411973
  have h : (OAI.OddGoldbach23.Cert.Qlist.drop 500).take 250 = Qc50 ++ Qc51 ++ Qc52 ++ Qc53 ++ Qc54 ++ Qc55 ++ Qc56 ++ Qc57 ++ Qc58 ++ Qc59 ++ Qc60 ++ Qc61 ++ Qc62 ++ Qc63 ++ Qc64 ++ Qc65 ++ Qc66 ++ Qc67 ++ Qc68 ++ Qc69 ++ Qc70 ++ Qc71 ++ Qc72 ++ Qc73 ++ Qc74 := by decide +kernel
  rw [h]
  simp only [List.map_append, List.sum_append]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add chunk50 chunk51) chunk52) chunk53) chunk54) chunk55) chunk56) chunk57) chunk58) chunk59) chunk60) chunk61) chunk62) chunk63) chunk64) chunk65) chunk66) chunk67) chunk68) chunk69) chunk70) chunk71) chunk72) chunk73) chunk74).trans_eq (by norm_num)
#print axioms solution
