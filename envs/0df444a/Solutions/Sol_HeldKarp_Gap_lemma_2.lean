-- Prove2me | solution 1 for HeldKarp.Gap.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:57:57.642848+00:00
-- url     : https://prove2.me/submissions/3b8a0c80-d66a-4bad-ad7c-9651d64e48f0

import Mathlib
import Definitions.Def_HeldKarp_Gap_SubtourLP

open Classical
open HeldKarp.Gap

theorem g69g_sum_deg {n : ℕ} (x : Edge n → ℝ) : ∑ i, deg x i = 2 * total x := by
  unfold deg total
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have : (Finset.univ.filter (fun i : Fin n => i ∈ e.1)) = e.1.toFinset := by
    ext i; simp [Sym2.mem_toFinset]
  rw [this, Sym2.card_toFinset_of_not_isDiag _ e.2]; norm_num

theorem solution {n : ℕ} [NeZero n] (hn : 3 ≤ n) (x : Edge n → ℝ) :
    (∀ i : Fin n, deg x i = 2) ↔
      ((∀ i : Fin n, i ≠ lastV n → deg x i = 2) ∧ total x = n) := by
  have hs := g69g_sum_deg x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (lastV n))] at hs
  constructor
  · intro h
    refine ⟨fun i _ => h i, ?_⟩
    have : ∑ i, deg x i = ∑ i : Fin n, (2 : ℝ) := Finset.sum_congr rfl (fun i _ => h i)
    have h2 := g69g_sum_deg x
    rw [this] at h2; simp at h2; linarith
  · rintro ⟨h, ht⟩ i
    by_cases hi : i = lastV n
    · have : ∑ j ∈ Finset.univ.erase (lastV n), deg x j =
          ∑ j ∈ Finset.univ.erase (lastV n), (2 : ℝ) :=
        Finset.sum_congr rfl (fun j hj => h j (Finset.ne_of_mem_erase hj))
      rw [this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ht] at hs
      have h1 : (1 : ℕ) ≤ n := by omega
      rw [Nat.cast_sub h1] at hs
      subst hi; push_cast at hs; linarith
    · exact h i hi
