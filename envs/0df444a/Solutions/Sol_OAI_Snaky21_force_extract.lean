-- Prove2me | solution 1 for OAI.Snaky21.force_extract
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-08T07:52:20.900972+00:00
-- url     : https://prove2.me/submissions/c38889e9-c2e9-4617-a93e-23fe807e2491

import Definitions.Def_Snaky21Core
open OAI.Snaky21 OAI.SnakyPrototype OAI.SnakyPrototype.OrdinaryStrategy

namespace OAI.Snaky21
open SnakyPrototype

theorem hasSnaky_mono {M M' : Finset Cell} (h : M ⊆ M') :
    HasSnaky M → HasSnaky M' := by
  rintro ⟨r, t, ht⟩
  exact ⟨r, t, ht.trans h⟩

theorem freshCell_not_mem (M B : Finset Cell) : freshCell M B ∉ M ∪ B := by
  intro hm
  have hh := Finset.le_sup (f := fun x : Cell => x.1.natAbs) hm
  simp only [freshCell, Int.natAbs_natCast] at hh
  omega

theorem fresh_exists (M B : Finset Cell) : ∃ m : Cell, m ∉ M ∧ m ∉ B := by
  exact ⟨freshCell M B, by simpa only [Finset.mem_union, not_or] using freshCell_not_mem M B⟩

theorem won_canForce (n : ℕ) {M B : Finset Cell} (h : HasSnaky M) :
    CanForce n M B := by
  cases n with
  | zero => exact h
  | succ n =>
    obtain ⟨m, hm, hb⟩ := fresh_exists M B
    exact ⟨m, hm, hb, Or.inl (hasSnaky_mono (Finset.subset_insert _ _) h)⟩


end OAI.Snaky21

namespace OAI.Snaky21
open SnakyPrototype SnakyPrototype.OrdinaryStrategy

theorem forcePolicy_legal (r : ℕ) (M B : Finset Cell) :
    forcePolicy r M B ∉ M ∧ forcePolicy r M B ∉ B := by
  classical
  unfold forcePolicy
  split
  · exact ⟨(Classical.choose_spec ‹∃ m, MoveOK r M B m›).1,
      (Classical.choose_spec ‹∃ m, MoveOK r M B m›).2.1⟩
  · simpa only [Finset.mem_union, not_or] using freshCell_not_mem M B

theorem forcePolicy_move {n : ℕ} {M B : Finset Cell} (h : CanForce (n + 1) M B) :
    HasSnaky (insert (forcePolicy (n + 1) M B) M) ∨
      ∀ b, b ∉ insert (forcePolicy (n + 1) M B) M → b ∉ B →
        CanForce n (insert (forcePolicy (n + 1) M B) M) (insert b B) := by
  classical
  have he : ∃ m, MoveOK (n + 1) M B m := by simpa [MoveOK, CanForce] using h
  have heq : forcePolicy (n + 1) M B = Classical.choose he := by
    unfold forcePolicy
    rw [dif_pos he]
  rw [heq]
  simpa only [MoveOK, Nat.add_sub_cancel] using
    (Classical.choose_spec he).2.2

theorem forcePolicy_last {M B : Finset Cell} (h : CanForce 1 M B) :
    HasSnaky (insert (forcePolicy 1 M B) M) := by
  rcases forcePolicy_move h with h | h
  · exact h
  · obtain ⟨b, hbM, hbB⟩ := fresh_exists (insert (forcePolicy 1 M B) M) B
    exact h b hbM hbB

theorem forcePolicy_continues (N : ℕ) (β : ℕ → Cell)
    (hβ : LegalRepliesBeforeFinal forcePolicy N β ∅ ∅)
    (hstart : CanForce N ∅ ∅) :
    ∀ k, k < N → CanForce (N - k)
      (playState forcePolicy N β ∅ ∅ k).1 (playState forcePolicy N β ∅ ∅ k).2 := by
  intro k
  induction k with
  | zero => intro _; simpa [playState] using hstart
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hn : N - k = (N - (k + 1)) + 1 := by omega
    rw [hn] at hprev
    have hmove := forcePolicy_move hprev
    have heq : forcePolicy ((N - (k + 1)) + 1)
        (playState forcePolicy N β ∅ ∅ k).1 (playState forcePolicy N β ∅ ∅ k).2 =
        makerAt forcePolicy N β ∅ ∅ k := by simp only [makerAt, hn]
    rw [heq] at hmove
    change CanForce (N - (k + 1))
      (insert (makerAt forcePolicy N β ∅ ∅ k) (playState forcePolicy N β ∅ ∅ k).1)
      (insert (β k) (playState forcePolicy N β ∅ ∅ k).2)
    rcases hmove with hw | hw
    · exact won_canForce _ hw
    · exact hw (β k) (hβ k hk).1 (hβ k hk).2

theorem legal_play_facts (σ : Policy Cell)
    (hσ : ∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B)
    (N : ℕ) (β : ℕ → Cell) (hβ : LegalRepliesBeforeFinal σ N β ∅ ∅) :
    ∀ k, k < N →
      Disjoint (playState σ N β ∅ ∅ k).1 (playState σ N β ∅ ∅ k).2 ∧
      (playState σ N β ∅ ∅ k).1.card = k ∧
      (playState σ N β ∅ ∅ k).2.card = k := by
  intro k
  induction k with
  | zero => intro _; simp [playState]
  | succ k ih =>
    intro hk
    obtain ⟨hd, hM, hB⟩ := ih (by omega)
    have hm := hσ (N - k) (playState σ N β ∅ ∅ k).1 (playState σ N β ∅ ∅ k).2
    have hb := hβ k hk
    change Disjoint (insert (makerAt σ N β ∅ ∅ k) (playState σ N β ∅ ∅ k).1)
        (insert (β k) (playState σ N β ∅ ∅ k).2) ∧ _
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.disjoint_insert_right, Finset.disjoint_insert_left]
      exact ⟨hb.1, hm.2, hd⟩
    · simpa only [playState, makerAt, Finset.card_insert_of_notMem hm.1] using congrArg (· + 1) hM
    · simpa only [playState, Finset.card_insert_of_notMem hb.2] using congrArg (· + 1) hB

theorem force_extract (N : ℕ) (hN : 0 < N) (hstart : CanForce N ∅ ∅) :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ N β ∅ ∅ →
        HasSnaky (playState σ N β ∅ ∅ N).1 ∧
        (playState σ N β ∅ ∅ N).1.card = N ∧
        Disjoint (playState σ N β ∅ ∅ N).1 (playState σ N β ∅ ∅ (N - 1)).2 ∧
        ∀ k, k < N →
          Disjoint (playState σ N β ∅ ∅ k).1 (playState σ N β ∅ ∅ k).2 ∧
          (playState σ N β ∅ ∅ k).2.card = k := by
  refine ⟨forcePolicy, forcePolicy_legal, ?_⟩
  intro β hβ
  let k := N - 1
  have hk : k < N := by dsimp [k]; omega
  have hNk : N = k + 1 := by dsimp [k]; omega
  have hremain : N - k = 1 := by omega
  have hforce := forcePolicy_continues N β hβ hstart k hk
  rw [hremain] at hforce
  have hw := forcePolicy_last hforce
  obtain ⟨hd, hM, _⟩ := legal_play_facts forcePolicy forcePolicy_legal N β hβ k hk
  have hfresh := forcePolicy_legal 1 (playState forcePolicy N β ∅ ∅ k).1
    (playState forcePolicy N β ∅ ∅ k).2
  have hstate : (playState forcePolicy N β ∅ ∅ N).1 =
      insert (forcePolicy 1 (playState forcePolicy N β ∅ ∅ k).1
        (playState forcePolicy N β ∅ ∅ k).2) (playState forcePolicy N β ∅ ∅ k).1 := by
    conv_lhs => rw [hNk]
    simp only [playState, ← hNk, hremain]
  refine ⟨by simpa only [hstate] using hw, ?_, ?_, ?_⟩
  · rw [hstate, Finset.card_insert_of_notMem hfresh.1, hM]
    omega
  · rw [hstate, Finset.disjoint_insert_left]
    exact ⟨hfresh.2, hd⟩
  · intro j hj
    obtain ⟨hd, _, hB⟩ := legal_play_facts forcePolicy forcePolicy_legal N β hβ j hj
    exact ⟨hd, hB⟩

end OAI.Snaky21

theorem solution (N : ℕ) (hN : 0 < N) (hstart : CanForce N ∅ ∅) :
    ∃ σ : Policy Cell,
      (∀ r M B, σ r M B ∉ M ∧ σ r M B ∉ B) ∧
      ∀ β : ℕ → Cell, LegalRepliesBeforeFinal σ N β ∅ ∅ →
        HasSnaky (playState σ N β ∅ ∅ N).1 ∧
        (playState σ N β ∅ ∅ N).1.card = N ∧
        Disjoint (playState σ N β ∅ ∅ N).1 (playState σ N β ∅ ∅ (N - 1)).2 ∧
        ∀ k, k < N →
          Disjoint (playState σ N β ∅ ∅ k).1 (playState σ N β ∅ ∅ k).2 ∧
          (playState σ N β ∅ ∅ k).2.card = k :=
  force_extract N hN hstart

#print axioms solution
