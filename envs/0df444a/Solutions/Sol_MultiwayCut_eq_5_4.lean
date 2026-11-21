-- Prove2me | solution 1 for MultiwayCut.eq_5_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:20:20.781076+00:00
-- url     : https://prove2.me/submissions/e1c991a9-8d1d-41d4-8934-e19d42f35d66

import Mathlib
import Definitions.Def_MultiwayCut_A53

namespace Aux_MultiwayCut_eq_5_4

open MultiwayCut

noncomputable def a (m n : ℕ) : ℝ :=
  if m = 0 ∧ n = 0 then 1
  else if m = 0 ∨ n = 0 then 5 / 27
  else if m = n ∧ (m = 1 ∨ m = 2) then 1 / 9
  else if m = 3 ∧ n = 3 then -5 / 18
  else if m ≤ 2 ∨ n ≤ 2 then 5 / 108
  else 0

theorem A_eq {k : ℕ} (m n : Fin k) : A53 k m n = a m.val n.val := by
  simp only [A53, a]
  by_cases h1 : m.val = 0 ∧ n.val = 0
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : m.val = 0 ∨ n.val = 0
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : m.val = n.val ∧ (m.val = 1 ∨ m.val = 2)
      · rw [if_pos h3, if_pos (⟨Fin.ext h3.1, h3.2⟩ : m = n ∧ (m.val = 1 ∨ m.val = 2))]
      · rw [if_neg h3, if_neg (fun h : m = n ∧ (m.val = 1 ∨ m.val = 2) =>
          h3 ⟨congrArg Fin.val h.1, h.2⟩)]

theorem a_symm (m n : ℕ) : a n m = a m n := by
  unfold a
  split_ifs <;> first | rfl | (exfalso; omega)

theorem a_big (i m : ℕ) (hi : 3 ≤ i) (hm : 4 ≤ m) : a i m = 0 := by
  unfold a
  rw [if_neg (show ¬(i = 0 ∧ m = 0) by omega), if_neg (show ¬(i = 0 ∨ m = 0) by omega),
    if_neg (show ¬(i = m ∧ (i = 1 ∨ i = 2)) by omega), if_neg (show ¬(i = 3 ∧ m = 3) by omega),
    if_neg (show ¬(i ≤ 2 ∨ m ≤ 2) by omega)]

theorem a0m (m : ℕ) (hm : 4 ≤ m) : a 0 m = 5 / 27 := by
  unfold a
  rw [if_neg (show ¬((0 : ℕ) = 0 ∧ m = 0) by omega), if_pos (show (0 : ℕ) = 0 ∨ m = 0 by omega)]

theorem a1m (m : ℕ) (hm : 4 ≤ m) : a 1 m = 5 / 108 := by
  unfold a
  rw [if_neg (show ¬((1 : ℕ) = 0 ∧ m = 0) by omega), if_neg (show ¬((1 : ℕ) = 0 ∨ m = 0) by omega),
    if_neg (show ¬((1 : ℕ) = m ∧ ((1 : ℕ) = 1 ∨ (1 : ℕ) = 2)) by omega),
    if_neg (show ¬((1 : ℕ) = 3 ∧ m = 3) by omega),
    if_pos (show (1 : ℕ) ≤ 2 ∨ m ≤ 2 by omega)]

theorem a2m (m : ℕ) (hm : 4 ≤ m) : a 2 m = 5 / 108 := by
  unfold a
  rw [if_neg (show ¬((2 : ℕ) = 0 ∧ m = 0) by omega), if_neg (show ¬((2 : ℕ) = 0 ∨ m = 0) by omega),
    if_neg (show ¬((2 : ℕ) = m ∧ ((2 : ℕ) = 1 ∨ (2 : ℕ) = 2)) by omega),
    if_neg (show ¬((2 : ℕ) = 3 ∧ m = 3) by omega),
    if_pos (show (2 : ℕ) ≤ 2 ∨ m ≤ 2 by omega)]

theorem col (m : ℕ) (hm : 4 ≤ m) :
    ∀ L, 2 ≤ L → ∑ i ∈ Finset.range (L + 1), a i m = 5 / 18 := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base =>
    norm_num [Finset.sum_range_succ, a0m m hm, a1m m hm, a2m m hm]
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih, a_big (n + 1) m (by omega) hm]
    norm_num

theorem sum_Iic_eq {k : ℕ} (f : ℕ → ℝ) (ℓ : Fin k) :
    ∑ j ∈ Finset.Iic ℓ, f j.val = ∑ x ∈ Finset.range (ℓ.val + 1), f x := by
  have h := Finset.sum_map (Finset.Iic ℓ) Fin.valEmbedding f
  simp only [Fin.valEmbedding_apply] at h
  rw [← h, Fin.map_valEmbedding_Iic, Nat.range_succ_eq_Iic]

noncomputable def S (L : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (L + 1), ∑ j ∈ Finset.range (L + 1), a i j

theorem dbl {k : ℕ} (ℓ : Fin k) :
    ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic ℓ, A53 k i j = S ℓ.val := by
  have h1 : ∀ i : Fin k, ∑ j ∈ Finset.Iic ℓ, A53 k i j
      = ∑ x ∈ Finset.range (ℓ.val + 1), a i.val x := by
    intro i
    rw [← sum_Iic_eq (a i.val) ℓ]
    exact Finset.sum_congr rfl (fun j _ => A_eq i j)
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  exact sum_Iic_eq (fun y => ∑ x ∈ Finset.range (ℓ.val + 1), a y x) ℓ

theorem S_succ (L : ℕ) :
    S (L + 1) = S L + ∑ i ∈ Finset.range (L + 1), a i (L + 1)
      + (∑ j ∈ Finset.range (L + 1), a (L + 1) j + a (L + 1) (L + 1)) := by
  calc S (L + 1) = ∑ i ∈ Finset.range (L + 1 + 1), ∑ j ∈ Finset.range (L + 1 + 1), a i j := rfl
    _ = ∑ i ∈ Finset.range (L + 1 + 1), (∑ j ∈ Finset.range (L + 1), a i j + a i (L + 1)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_range_succ _ _)
    _ = ∑ i ∈ Finset.range (L + 1 + 1), ∑ j ∈ Finset.range (L + 1), a i j
        + ∑ i ∈ Finset.range (L + 1 + 1), a i (L + 1) := Finset.sum_add_distrib
    _ = (S L + ∑ j ∈ Finset.range (L + 1), a (L + 1) j)
        + (∑ i ∈ Finset.range (L + 1), a i (L + 1) + a (L + 1) (L + 1)) := by
        rw [Finset.sum_range_succ (fun i => ∑ j ∈ Finset.range (L + 1), a i j) (L + 1),
          Finset.sum_range_succ (fun i => a i (L + 1)) (L + 1)]
        rfl
    _ = _ := by ring

theorem S_big (L : ℕ) (hL : 3 ≤ L) : S L = 7 / 3 + 2 * ((L : ℝ) + 1 - 4) * (5 / 18) := by
  induction L, hL using Nat.le_induction with
  | base =>
    norm_num [S, Finset.sum_range_succ, a]
  | succ n hn ih =>
    rw [S_succ, ih, col (n + 1) (by omega) n (by omega)]
    have hrow : ∑ j ∈ Finset.range (n + 1), a (n + 1) j = 5 / 18 := by
      rw [← col (n + 1) (by omega) n (by omega)]
      exact Finset.sum_congr rfl (fun j _ => (a_symm j (n + 1)))
    rw [hrow, a_big (n + 1) (n + 1) (by omega) (by omega)]
    push_cast
    ring

end Aux_MultiwayCut_eq_5_4

open MultiwayCut Aux_MultiwayCut_eq_5_4 in
theorem solution {k : ℕ} :
    (∀ hk : 4 ≤ k,
      ∑ i ∈ Finset.Iic (⟨0, by omega⟩ : Fin k), ∑ j ∈ Finset.Iic (⟨0, by omega⟩ : Fin k),
          A53 k i j = 1 ∧
      ∑ i ∈ Finset.Iic (⟨1, by omega⟩ : Fin k), ∑ j ∈ Finset.Iic (⟨1, by omega⟩ : Fin k),
          A53 k i j = 40 / 27 ∧
      ∑ i ∈ Finset.Iic (⟨2, by omega⟩ : Fin k), ∑ j ∈ Finset.Iic (⟨2, by omega⟩ : Fin k),
          A53 k i j = 37 / 18 ∧
      ∑ i ∈ Finset.Iic (⟨3, by omega⟩ : Fin k), ∑ j ∈ Finset.Iic (⟨3, by omega⟩ : Fin k),
          A53 k i j = 7 / 3) ∧
    (∀ j : Fin k, ∀ hj : 4 ≤ j.val,
      ∑ i ∈ Finset.Iic (⟨2, by have := j.isLt; omega⟩ : Fin k), A53 k i j = 5 / 18) ∧
    (∀ ℓ : Fin k, 3 ≤ ℓ.val →
      ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic ℓ, A53 k i j =
          7 / 3 + 2 * ((ℓ.val : ℝ) + 1 - 4) * (5 / 18) ∧
      1 / ((ℓ.val : ℝ) + 1) * ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic ℓ, A53 k i j =
          1 / ((ℓ.val : ℝ) + 1) * (7 / 3 - 8 * (5 / 18)) + 2 * (5 / 18) ∧
      1 / ((ℓ.val : ℝ) + 1) * (7 / 3 - 8 * (5 / 18)) + 2 * (5 / 18) =
          1 / (9 * ((ℓ.val : ℝ) + 1)) + 5 / 9 ∧
      1 / (9 * ((ℓ.val : ℝ) + 1)) + 5 / 9 ≤ 7 / 12) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hk
    simp only [dbl]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [S, Finset.sum_range_succ, a]
  · intro j hj
    have e : ∑ i ∈ Finset.Iic (⟨2, by have := j.isLt; omega⟩ : Fin k), A53 k i j
        = ∑ i ∈ Finset.Iic (⟨2, by have := j.isLt; omega⟩ : Fin k), a i.val j.val :=
      Finset.sum_congr rfl (fun i _ => A_eq i j)
    rw [e, sum_Iic_eq (fun x => a x j.val)]
    exact col j.val hj 2 le_rfl
  · intro ℓ hℓ
    have hS := S_big ℓ.val hℓ
    rw [dbl, hS]
    have hpos : (0 : ℝ) < (ℓ.val : ℝ) + 1 := by positivity
    have hne : (ℓ.val : ℝ) + 1 ≠ 0 := ne_of_gt hpos
    have h3 : (3 : ℝ) ≤ (ℓ.val : ℝ) := by exact_mod_cast hℓ
    refine ⟨rfl, ?_, ?_, ?_⟩
    · field_simp <;> ring
    · field_simp <;> ring
    · have h36 : (36 : ℝ) ≤ 9 * ((ℓ.val : ℝ) + 1) := by linarith
      have hle : 1 / (9 * ((ℓ.val : ℝ) + 1)) ≤ 1 / 36 :=
        one_div_le_one_div_of_le (by norm_num) h36
      linarith
