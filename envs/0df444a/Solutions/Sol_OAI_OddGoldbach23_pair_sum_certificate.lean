-- Prove2me | solution 1 for OAI.OddGoldbach23.pair_sum_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-25T07:58:30.18119+00:00
-- url     : https://prove2.me/submissions/732233ec-db3b-43e5-a372-d9fd1c15dde3

import Theorems.Thm_OAI_OddGoldbach23_pair_quarter_0
import Theorems.Thm_OAI_OddGoldbach23_pair_quarter_1
import Theorems.Thm_OAI_OddGoldbach23_pair_quarter_2
import Theorems.Thm_OAI_OddGoldbach23_pair_quarter_3
import Mathlib.Tactic.NormNum
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem four_parts (L : List ℕ) (f : ℕ → ℕ) (hlen : L.length ≤ 1000)
    (a b c d : ℕ)
    (ha : (((L.drop 0).take 250).map f).sum ≤ a)
    (hb : (((L.drop 250).take 250).map f).sum ≤ b)
    (hc : (((L.drop 500).take 250).map f).sum ≤ c)
    (hd : (((L.drop 750).take 250).map f).sum ≤ d) :
    (L.map f).sum ≤ a + b + c + d := by
  have h : L = (L.drop 0).take 250 ++ (L.drop 250).take 250 ++
      (L.drop 500).take 250 ++ (L.drop 750).take 250 := by
    have hlen' : (L.drop 750).length ≤ 250 := by simp only [List.length_drop]; omega
    rw [List.take_of_length_le hlen']
    simp only [List.drop_zero, List.append_assoc]
    have h2 := List.take_append_drop 250 (L.drop 500)
    have h1 := List.take_append_drop 250 (L.drop 250)
    simp only [List.drop_drop] at h2 h1
    rw [h2, h1, List.take_append_drop]
  conv_lhs => rw [h]
  simp only [List.map_append, List.sum_append]
  exact add_le_add (add_le_add (add_le_add ha hb) hc) hd

open OAI.OddGoldbach23.Cert in
theorem solution :
    (Qlist.map (fun a => (Qlist.map (fun b => if b < a then WP (a-b) else 0)).sum)).sum ≤ 867860452 := by
  have h := four_parts Qlist (fun a => (Qlist.map (fun b => if b < a then WP (a-b) else 0)).sum)
    (by decide +kernel) _ _ _ _
    OAI.OddGoldbach23.pair_quarter_0 OAI.OddGoldbach23.pair_quarter_1
    OAI.OddGoldbach23.pair_quarter_2 OAI.OddGoldbach23.pair_quarter_3
  exact h.trans_eq (by norm_num)
#print axioms solution
