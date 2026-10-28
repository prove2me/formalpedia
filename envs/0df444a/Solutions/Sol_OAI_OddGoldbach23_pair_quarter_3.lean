-- Prove2me | solution 1 for OAI.OddGoldbach23.pair_quarter_3
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:50:16.360499+00:00
-- url     : https://prove2.me/submissions/ef671f3e-f941-486c-acad-39e1937c9508

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
def rowW (a : ℕ) : ℕ := (Qlist.map fun b => if b < a then WP (a-b) else 0).sum
theorem chunk75 : (Qc75.map rowW).sum ≤ 13121199 := by decide +kernel
theorem chunk76 : (Qc76.map rowW).sum ≤ 13296899 := by decide +kernel
theorem chunk77 : (Qc77.map rowW).sum ≤ 13482371 := by decide +kernel
theorem chunk78 : (Qc78.map rowW).sum ≤ 13670707 := by decide +kernel
theorem chunk79 : (Qc79.map rowW).sum ≤ 13822466 := by decide +kernel
theorem chunk80 : (Qc80.map rowW).sum ≤ 13978711 := by decide +kernel
theorem chunk81 : (Qc81.map rowW).sum ≤ 14182838 := by decide +kernel
theorem chunk82 : (Qc82.map rowW).sum ≤ 14345943 := by decide +kernel
theorem chunk83 : (Qc83.map rowW).sum ≤ 14468506 := by decide +kernel
theorem chunk84 : (Qc84.map rowW).sum ≤ 14690825 := by decide +kernel
theorem chunk85 : (Qc85.map rowW).sum ≤ 14847572 := by decide +kernel
theorem chunk86 : (Qc86.map rowW).sum ≤ 15039766 := by decide +kernel
theorem chunk87 : (Qc87.map rowW).sum ≤ 15216852 := by decide +kernel
theorem chunk88 : (Qc88.map rowW).sum ≤ 15408666 := by decide +kernel
theorem chunk89 : (Qc89.map rowW).sum ≤ 15564593 := by decide +kernel
theorem chunk90 : (Qc90.map rowW).sum ≤ 15739841 := by decide +kernel
theorem chunk91 : (Qc91.map rowW).sum ≤ 15923198 := by decide +kernel
theorem chunk92 : (Qc92.map rowW).sum ≤ 16089380 := by decide +kernel
theorem chunk93 : (Qc93.map rowW).sum ≤ 16207069 := by decide +kernel
theorem chunk94 : (Qc94.map rowW).sum ≤ 16446996 := by decide +kernel
theorem chunk95 : (Qc95.map rowW).sum ≤ 16618332 := by decide +kernel
theorem chunk96 : (Qc96.map rowW).sum ≤ 16792711 := by decide +kernel
theorem chunk97 : (Qc97.map rowW).sum ≤ 16938108 := by decide +kernel
theorem chunk98 : (Qc98.map rowW).sum ≤ 17144511 := by decide +kernel
theorem chunk99 : (Qc99.map rowW).sum ≤ 17330807 := by decide +kernel
end OAI.OddGoldbach23.Cert
open OAI.OddGoldbach23.Cert
theorem solution : (((OAI.OddGoldbach23.Cert.Qlist.drop 750).take 250).map (fun a => (OAI.OddGoldbach23.Cert.Qlist.map (fun b => if b < a then OAI.OddGoldbach23.Cert.WP (a-b) else 0)).sum)).sum ≤ 380368867 := by
  change (((OAI.OddGoldbach23.Cert.Qlist.drop 750).take 250).map rowW).sum ≤ 380368867
  have h : (OAI.OddGoldbach23.Cert.Qlist.drop 750).take 250 = Qc75 ++ Qc76 ++ Qc77 ++ Qc78 ++ Qc79 ++ Qc80 ++ Qc81 ++ Qc82 ++ Qc83 ++ Qc84 ++ Qc85 ++ Qc86 ++ Qc87 ++ Qc88 ++ Qc89 ++ Qc90 ++ Qc91 ++ Qc92 ++ Qc93 ++ Qc94 ++ Qc95 ++ Qc96 ++ Qc97 ++ Qc98 ++ Qc99 := by decide +kernel
  rw [h]
  simp only [List.map_append, List.sum_append]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add chunk75 chunk76) chunk77) chunk78) chunk79) chunk80) chunk81) chunk82) chunk83) chunk84) chunk85) chunk86) chunk87) chunk88) chunk89) chunk90) chunk91) chunk92) chunk93) chunk94) chunk95) chunk96) chunk97) chunk98) chunk99).trans_eq (by norm_num)
#print axioms solution
