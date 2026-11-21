-- Prove2me | solution 1 for MultiwayCut.observation_5_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:15:08.83411+00:00
-- url     : https://prove2.me/submissions/d23e9478-4fed-4806-9751-a09417be6b9e

import Mathlib
import Definitions.Def_MultiwayCut_Transformation
import Definitions.Def_MultiwayCut_A53

namespace Aux_MultiwayCut_observation_5_1

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

theorem a_le_one (m n : ℕ) : a m n ≤ 1 := by
  unfold a
  split_ifs <;> norm_num

theorem a_nonneg (m n : ℕ) (h : ¬ (m = 3 ∧ n = 3)) : 0 ≤ a m n := by
  unfold a
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

theorem a_row_ge4 (m n : ℕ) (hm : 4 ≤ m) : a m n = a 4 n := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m ≠ 1 := by omega
  have hm2 : m ≠ 2 := by omega
  have hm3 : m ≠ 3 := by omega
  have hm2' : ¬ m ≤ 2 := by omega
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | rfl | rfl | hn
  · simp [a, hm0]
  · simp [a, hm0, hm1, hm2, hm3, hm2']
  · simp [a, hm0, hm1, hm2, hm3, hm2']
  · simp [a, hm0, hm1, hm2, hm3, hm2']
  · have hn0 : n ≠ 0 := by omega
    have hn3 : n ≠ 3 := by omega
    have hn2' : ¬ n ≤ 2 := by omega
    simp [a, hm0, hm1, hm2, hm3, hm2', hn0, hn3, hn2']

theorem a01 (j : ℕ) : a 1 j ≤ a 0 j := by
  unfold a
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

theorem a24 (j : ℕ) : a 4 j ≤ a 2 j := by
  unfold a
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

theorem a43 (j : ℕ) : a 3 j ≤ a 4 j := by
  unfold a
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

theorem a12_tail (j : ℕ) (hj : 2 < j) : a 2 j ≤ a 1 j := by
  unfold a
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

theorem a3_tail (j : ℕ) (hj : 3 < j) : (0 : ℝ) ≤ a 3 j := by
  unfold a
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

theorem prefix_ge (f g : ℕ → ℝ) (L0 : ℕ)
    (hbase : ∀ L ≤ L0, ∑ x ∈ Finset.range (L + 1), g x ≤ ∑ x ∈ Finset.range (L + 1), f x)
    (htail : ∀ j, L0 < j → g j ≤ f j) :
    ∀ L, ∑ x ∈ Finset.range (L + 1), g x ≤ ∑ x ∈ Finset.range (L + 1), f x := by
  intro L
  induction L with
  | zero => exact hbase 0 (Nat.zero_le _)
  | succ n ih =>
    by_cases h : n + 1 ≤ L0
    · exact hbase (n + 1) h
    · rw [Finset.sum_range_succ g (n + 1), Finset.sum_range_succ f (n + 1)]
      have := htail (n + 1) (by omega)
      linarith

theorem sum_Iic_eq {k : ℕ} [NeZero k] (f : ℕ → ℝ) (ℓ : Fin k) :
    ∑ j ∈ Finset.Iic ℓ, f j.val = ∑ x ∈ Finset.range (ℓ.val + 1), f x := by
  have h := Finset.sum_map (Finset.Iic ℓ) Fin.valEmbedding f
  simp only [Fin.valEmbedding_apply] at h
  rw [← h, Fin.map_valEmbedding_Iic, Nat.range_succ_eq_Iic]

theorem row3_nonneg (L : ℕ) : (0 : ℝ) ≤ ∑ x ∈ Finset.range (L + 1), a 3 x := by
  have := prefix_ge (a 3) (fun _ => (0 : ℝ)) 3 ?_ ?_ L
  · simpa using this
  · intro L hL
    interval_cases L <;> norm_num [Finset.sum_range_succ, a]
  · intro j hj
    exact a3_tail j hj

theorem row12 (L : ℕ) :
    ∑ x ∈ Finset.range (L + 1), a 2 x ≤ ∑ x ∈ Finset.range (L + 1), a 1 x := by
  refine prefix_ge (a 1) (a 2) 2 ?_ ?_ L
  · intro L hL
    interval_cases L <;> norm_num [Finset.sum_range_succ, a]
  · intro j hj
    exact a12_tail j hj

theorem termwise (f g : ℕ → ℝ) (h : ∀ j, g j ≤ f j) (L : ℕ) :
    ∑ x ∈ Finset.range (L + 1), g x ≤ ∑ x ∈ Finset.range (L + 1), f x :=
  Finset.sum_le_sum (fun j _ => h j)

end Aux_MultiwayCut_observation_5_1

open MultiwayCut Aux_MultiwayCut_observation_5_1 in
theorem solution {k : ℕ} [NeZero k] :
    ((A53 k).IsSymm ∧ Lemma51Conditions (A53 k)) ∧
    ∀ hk : 5 ≤ k,
      (∀ j : Fin k, 4 ≤ j.val → A53 k j = A53 k ⟨4, by omega⟩) ∧
      PrefixGe (A53 k ⟨0, by omega⟩) (A53 k ⟨1, by omega⟩) ∧
      PrefixGe (A53 k ⟨1, by omega⟩) (A53 k ⟨2, by omega⟩) ∧
      PrefixGe (A53 k ⟨2, by omega⟩) (A53 k ⟨4, by omega⟩) ∧
      PrefixGe (A53 k ⟨4, by omega⟩) (A53 k ⟨3, by omega⟩) ∧
      PrefixGe (A53 k ⟨3, by omega⟩) 0 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    rw [A_eq, A_eq, a_symm]
  · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [A_eq]
      simp [a]
    · intro i j
      rw [A_eq]
      exact a_le_one _ _
    · intro ℓ
      refine Finset.sum_nonneg (fun i _ => ?_)
      by_cases hi : i.val = 3
      · have e : ∑ j ∈ Finset.Iic ℓ, A53 k i j = ∑ j ∈ Finset.Iic ℓ, a 3 j.val := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [A_eq, hi]
        rw [e, sum_Iic_eq (a 3) ℓ]
        exact row3_nonneg ℓ.val
      · refine Finset.sum_nonneg (fun j _ => ?_)
        rw [A_eq]
        exact a_nonneg _ _ (fun h => hi h.1)
    · intro ℓ r _
      refine Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => ?_))
      rw [A_eq]
      apply a_nonneg
      intro h
      have hi' : i ≤ ℓ := Finset.mem_Iic.mp hi
      have hj' : ℓ < j := (Finset.mem_Ioc.mp hj).1
      have : i.val < j.val := lt_of_le_of_lt hi' hj'
      omega
  · intro hk
    have hrow : ∀ (r : ℕ) (hr : r < k) (ℓ : Fin k),
        ∑ j ∈ Finset.Iic ℓ, A53 k ⟨r, hr⟩ j = ∑ x ∈ Finset.range (ℓ.val + 1), a r x := by
      intro r hr ℓ
      rw [← sum_Iic_eq (a r) ℓ]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [A_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      funext n
      rw [A_eq, A_eq]
      exact a_row_ge4 _ _ hj
    · unfold PrefixGe
      intro ℓ
      rw [hrow, hrow]
      exact termwise (a 0) (a 1) a01 ℓ.val
    · unfold PrefixGe
      intro ℓ
      rw [hrow, hrow]
      exact row12 ℓ.val
    · unfold PrefixGe
      intro ℓ
      rw [hrow, hrow]
      exact termwise (a 2) (a 4) a24 ℓ.val
    · unfold PrefixGe
      intro ℓ
      rw [hrow, hrow]
      exact termwise (a 4) (a 3) a43 ℓ.val
    · unfold PrefixGe
      intro ℓ
      rw [hrow]
      simp only [Pi.zero_apply, Finset.sum_const_zero]
      exact row3_nonneg ℓ.val
