-- Prove2me | solution 1 for MaxPressure.ReversedLeontief.extremeAllocs_eq_intAllocs
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:20:04.145774+00:00
-- url     : https://prove2.me/submissions/a7520d12-b198-4186-beee-9438edb4eefc

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network



namespace MaxPressure.ReversedLeontief

open Classical

lemma rl_A_nonneg {I J K : ℕ} (N : Network I J K) (hN : N.Standing) (k : Fin K) (j : Fin J) :
    0 ≤ N.A k j := by
  rcases hN.1 k j with h | h <;> rw [h] <;> norm_num

lemma rl_le_one {I J K : ℕ} (N : Network I J K) (hN : N.Standing) {b : Fin J → ℝ}
    (hb : b ∈ allocSet N) (j : Fin J) : b j ≤ 1 := by
  obtain ⟨k, hk⟩ := hN.2.2.2.2.1 j
  have h1 := hb.2.1 k
  have h2 : N.A k j * b j ≤ ∑ j', N.A k j' * b j' :=
    Finset.single_le_sum (f := fun j' => N.A k j' * b j')
      (fun j' _ => mul_nonneg (rl_A_nonneg N hN k j') (hb.1 j')) (Finset.mem_univ j)
  rw [hk, one_mul] at h2
  linarith

lemma rl_int01 {I J K : ℕ} (N : Network I J K) (hN : N.Standing) {a : Fin J → ℝ}
    (ha : a ∈ intAllocs N) (j : Fin J) : a j = 0 ∨ a j = 1 := by
  obtain ⟨n, hn⟩ := ha.2 j
  have h1 := rl_le_one N hN ha.1 j
  rw [hn] at h1 ⊢
  have : n ≤ 1 := by exact_mod_cast h1
  interval_cases n <;> simp

theorem rl_int_sub_ext {I J K : ℕ} (N : Network I J K) (hN : N.Standing) :
    intAllocs N ⊆ extremeAllocs N := by
  intro a ha
  rw [extremeAllocs, mem_extremePoints]
  refine ⟨ha.1, ?_⟩
  intro x1 hx1 x2 hx2 hseg
  obtain ⟨t, s, ht, hs, hts, hx⟩ := hseg
  have key : ∀ j, x1 j = a j ∧ x2 j = a j := by
    intro j
    have hj := congrFun hx j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
    have h1 := rl_le_one N hN hx1 j
    have h2 := rl_le_one N hN hx2 j
    have h3 := hx1.1 j
    have h4 := hx2.1 j
    rcases rl_int01 N hN ha j with h | h <;> rw [h] at hj ⊢
    · constructor
      · apply le_antisymm _ h3
        nlinarith [mul_nonneg hs.le h4]
      · apply le_antisymm _ h4
        nlinarith [mul_nonneg ht.le h3]
    · constructor
      · apply le_antisymm h1
        nlinarith [mul_nonneg hs.le (sub_nonneg.2 h2)]
      · apply le_antisymm h2
        nlinarith [mul_nonneg ht.le (sub_nonneg.2 h1)]
  exact ⟨funext fun j => (key j).1, funext fun j => (key j).2⟩

lemma rl_other_zero {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) {k k' : Fin K} {j : Fin J}
    (h : N.A k j = 1) (hk : k' ≠ k) : N.A k' j = 0 := by
  rcases hN.1 k' j with h' | h'
  · exact h'
  · exact absurd ((hRL j).unique h' h) hk

theorem rl_ext_sub_int {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) : extremeAllocs N ⊆ intAllocs N := by
  intro a ha
  rw [extremeAllocs, mem_extremePoints] at ha
  have haA := ha.1
  refine ⟨haA, ?_⟩
  suffices h01 : ∀ j, a j = 0 ∨ a j = 1 by
    intro j; rcases h01 j with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  intro j
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < a j := lt_of_le_of_ne (haA.1 j) (Ne.symm hcon.1)
  have hlt : a j < 1 := lt_of_le_of_ne (rl_le_one N hN haA j) hcon.2
  obtain ⟨k, hk⟩ := hN.2.2.2.2.1 j
  have pert : ∀ b c : Fin J → ℝ, b ∈ allocSet N → c ∈ allocSet N →
      (∀ j', b j' + c j' = 2 * a j') → b j ≠ a j → False := by
    intro b c hb hc hbc hne
    have h := (ha.2 b hb c hc ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith [hbc i]⟩).1
    exact hne (congrFun h j)
  have hs1 : ∑ j', N.A k j' * a j' ≤ 1 := haA.2.1 k
  rcases lt_or_eq_of_le hs1 with hslt | hseq
  · -- processor k has slack
    have hnin : ¬ N.inputProc k := fun hin => by linarith [haA.2.2 k hin]
    set δ := min (a j) (1 - ∑ j', N.A k j' * a j') with hδ
    have hδpos : 0 < δ := lt_min hpos (by linarith)
    have hδ1 : δ ≤ a j := min_le_left _ _
    have hδ2 : δ ≤ 1 - ∑ j', N.A k j' * a j' := min_le_right _ _
    have mem : ∀ c : ℝ, -δ ≤ c → c ≤ δ →
        (fun j' => a j' + c * (if j' = j then 1 else 0)) ∈ allocSet N := by
      intro c hc1 hc2
      have hsum : ∀ k', ∑ j', N.A k' j' * (a j' + c * (if j' = j then 1 else 0)) =
          ∑ j', N.A k' j' * a j' + c * N.A k' j := by
        intro k'
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
        simp [Finset.sum_ite_eq', mul_comm]
      refine ⟨?_, ?_, ?_⟩
      · intro j'
        by_cases h : j' = j
        · subst h; simp; linarith
        · simp [h]; exact haA.1 j'
      · intro k'
        rw [hsum]
        by_cases hkk : k' = k
        · subst hkk; rw [hk]; linarith
        · rw [rl_other_zero N hN hRL hk hkk]; simpa using haA.2.1 k'
      · intro k' hin
        rw [hsum]
        have hkk : k' ≠ k := fun h => hnin (h ▸ hin)
        rw [rl_other_zero N hN hRL hk hkk]; simpa using haA.2.2 k' hin
    exact pert _ _ (mem δ (by linarith) le_rfl) (mem (-δ) le_rfl (by linarith))
      (fun j' => by ring) (by simp; exact hδpos.ne')
  · -- processor k is saturated: find another active activity
    obtain ⟨j2, hj2ne, hj2k, hj2pos⟩ : ∃ j2, j2 ≠ j ∧ N.A k j2 = 1 ∧ 0 < a j2 := by
      by_contra hno
      push_neg at hno
      have : ∑ j', N.A k j' * a j' = N.A k j * a j := by
        apply Finset.sum_eq_single j
        · intro j' _ hj'
          rcases hN.1 k j' with h | h
          · rw [h, zero_mul]
          · have := hno j' hj' h
            have := haA.1 j'
            rw [h, one_mul]; linarith
        · simp
      rw [this, hk, one_mul] at hseq
      linarith
    set δ := min (a j) (a j2) with hδ
    have hδpos : 0 < δ := lt_min hpos hj2pos
    have hδ1 : δ ≤ a j := min_le_left _ _
    have hδ2 : δ ≤ a j2 := min_le_right _ _
    have mem : ∀ c : ℝ, -δ ≤ c → c ≤ δ →
        (fun j' => a j' + c * ((if j' = j then 1 else 0) - (if j' = j2 then 1 else 0)))
          ∈ allocSet N := by
      intro c hc1 hc2
      have hsum : ∀ k', ∑ j', N.A k' j' *
          (a j' + c * ((if j' = j then 1 else 0) - (if j' = j2 then 1 else 0))) =
          ∑ j', N.A k' j' * a j' := by
        intro k'
        have e : ∑ j', N.A k' j' *
            (a j' + c * ((if j' = j then 1 else 0) - (if j' = j2 then 1 else 0))) =
            ∑ j', N.A k' j' * a j' + c * (N.A k' j - N.A k' j2) := by
          simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite,
            mul_one, mul_zero]
          simp [Finset.sum_ite_eq', mul_comm, mul_sub]
        rw [e]
        by_cases hkk : k' = k
        · subst hkk; rw [hk, hj2k]; ring
        · rw [rl_other_zero N hN hRL hk hkk, rl_other_zero N hN hRL hj2k hkk]; ring
      refine ⟨?_, ?_, ?_⟩
      · intro j'
        by_cases h : j' = j
        · subst h; simp [hj2ne.symm]; linarith
        · by_cases h2 : j' = j2
          · subst h2; simp [h]; linarith
          · simp [h, h2]; exact haA.1 j'
      · intro k'
        rw [hsum]; exact haA.2.1 k'
      · intro k' hin
        rw [hsum]; exact haA.2.2 k' hin
    exact pert _ _ (mem δ (by linarith) le_rfl) (mem (-δ) le_rfl (by linarith))
      (fun j' => by ring) (by simp [hj2ne.symm]; exact hδpos.ne')

theorem extremeAllocs_eq_intAllocs_core {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) :
    extremeAllocs N = intAllocs N :=
  Set.Subset.antisymm (rl_ext_sub_int N hN hRL) (rl_int_sub_ext N hN)

end MaxPressure.ReversedLeontief

open MaxPressure.ReversedLeontief


theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) :
    extremeAllocs N = intAllocs N := by
  exact extremeAllocs_eq_intAllocs_core N hN hRL
