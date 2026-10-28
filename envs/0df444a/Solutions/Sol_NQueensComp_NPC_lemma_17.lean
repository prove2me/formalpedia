-- Prove2me | solution 1 for NQueensComp.NPC.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:45:28.640435+00:00
-- url     : https://prove2.me/submissions/1d94e5ba-0f2e-4667-bff8-6785c735fc97

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions

open NQueensComp.NPC

/-- Attacks, in integer form. -/
theorem attacks_int (q₁ q₂ : Queen) (h : Attacks q₁ q₂) :
    ¬ ((q₁.1 : ℤ) = q₂.1 ∧ (q₁.2 : ℤ) = q₂.2) ∧
    ((q₁.1 : ℤ) = q₂.1 ∨ (q₁.2 : ℤ) = q₂.2 ∨ (q₁.1 : ℤ) + q₁.2 = q₂.1 + q₂.2 ∨
      (q₁.1 : ℤ) - q₁.2 = q₂.1 - q₂.2) := by
  obtain ⟨hne, hl⟩ := h
  simp only [col, row, sumDiag, diffDiag] at hl
  refine ⟨fun h => hne (Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2)), ?_⟩
  rcases hl with h | h | h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (Or.inl (by exact_mod_cast h))
  · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h)))
  · exact Or.inr (Or.inr (Or.inr h))

/-- Attacks from integer data. -/
theorem attacks_of_int (q₁ q₂ : Queen)
    (hne : ¬ ((q₁.1 : ℤ) = q₂.1 ∧ (q₁.2 : ℤ) = q₂.2))
    (hl : (q₁.1 : ℤ) = q₂.1 ∨ (q₁.2 : ℤ) = q₂.2 ∨ (q₁.1 : ℤ) + q₁.2 = q₂.1 + q₂.2 ∨
      (q₁.1 : ℤ) - q₁.2 = q₂.1 - q₂.2) : Attacks q₁ q₂ := by
  refine ⟨fun h => hne ⟨by rw [h], by rw [h]⟩, ?_⟩
  simp only [col, row, sumDiag, diffDiag]
  rcases hl with h | h | h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (Or.inl (by exact_mod_cast h))
  · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h)))
  · exact Or.inr (Or.inr (Or.inr h))

theorem mem_QDm (M : Inst4) (hM : M.Valid) (q : Queen) (hq : q ∈ def16_QDm M) :
    ∃ d ∈ M.Dm, (q.1 : ℤ) = 6 * M.n - 3 - d ∧ (q.2 : ℤ) = 3 * M.n - 1 - 2 * d ∧
      -((M.n : ℤ) - 1) ≤ d ∧ d ≤ (M.n : ℤ) - 1 := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hd1, hd2⟩ := hM.2.1 d hd
  refine ⟨d, hd, ?_, ?_, hd1, hd2⟩
  · simp only; rw [Int.toNat_of_nonneg (by omega)]
  · simp only; rw [Int.toNat_of_nonneg (by omega)]

theorem mem_QDp (M : Inst4) (hM : M.Valid) (q : Queen) (hq : q ∈ def16_QDp M) :
    ∃ d ∈ M.Dp, (q.1 : ℤ) = 2 * M.n - 2 - d ∧ (q.2 : ℤ) = M.n + 2 * d ∧
      (d : ℤ) ≤ 2 * (M.n : ℤ) - 2 := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hq
  have hd2 := hM.2.2 d hd
  refine ⟨d, hd, ?_, ?_, hd2⟩
  · simp only; rw [Int.toNat_of_nonneg (by omega)]
  · simp only; push_cast; ring

theorem QDm_queen_mem (M : Inst4) (d : ℤ) (hd : d ∈ M.Dm) :
    ((6 * (M.n : ℤ) - 3 - d).toNat, (3 * (M.n : ℤ) - 1 - 2 * d).toNat) ∈ def16_QDm M :=
  Finset.mem_image_of_mem _ hd

theorem QDp_queen_mem (M : Inst4) (d : ℕ) (hd : d ∈ M.Dp) :
    ((2 * (M.n : ℤ) - 2 - (d : ℤ)).toNat, M.n + 2 * d) ∈ def16_QDp M :=
  Finset.mem_image_of_mem _ hd

/-- Validity unpacked. -/
theorem valid_facts (M : Inst4) (hM : M.Valid) :
    1 ≤ M.n ∧ M.C.card = M.R.card ∧ (∀ c ∈ M.C, c < M.n) ∧ (∀ r ∈ M.R, r < M.n) := by
  obtain ⟨⟨⟨h1, _, _⟩, h2, _, h3, h4⟩, _, _⟩ := hM
  exact ⟨h1, h2, h3, h4⟩

/-- Solution facts unpacked. -/
theorem sol_facts (M : Inst4) (S : Finset Queen) (hS : M.IsSol S) :
    S.card = M.C.card ∧ NonAttacking S ∧ (∀ q ∈ S, col q ∈ M.C ∧ row q ∈ M.R) ∧
      ∀ q ∈ S, diffDiag q ∉ M.Dm ∧ sumDiag q ∉ M.Dp := by
  obtain ⟨⟨h1, _, h3, h4⟩, h5⟩ := hS
  simp only [Inst4.toInst3, Finset.card_empty, add_zero, Finset.sdiff_empty] at h1 h4
  exact ⟨h1, h3, h4, h5⟩

theorem mem_shift17 (M : Inst4) (S₄ : Finset Queen) (q : Queen)
    (hq : q ∈ shiftSet S₄ (3 * M.n - 2, 0)) :
    ∃ p ∈ S₄, q.1 = p.1 + (3 * M.n - 2) ∧ q.2 = p.2 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨p, hp, rfl, by simp⟩

theorem solution (M : Inst4) (hM : M.Valid) (S₄ : Finset Queen) (hS : M.IsSol S₄) :
    (def16 M).IsSol (lemma17_map M S₄) := by
  obtain ⟨hn, hCR, hC, hR⟩ := valid_facts M hM
  obtain ⟨hcard, hNA, hcolrow, hexcl⟩ := sol_facts M S₄ hS
  -- integer facts about the three kinds of queens
  have hshift : ∀ q ∈ shiftSet S₄ (3 * M.n - 2, 0), ∃ p ∈ S₄,
      (q.1 : ℤ) = p.1 + 3 * M.n - 2 ∧ (q.2 : ℤ) = p.2 ∧ (p.1 : ℤ) < M.n ∧ (p.2 : ℤ) < M.n := by
    intro q hq
    obtain ⟨p, hp, h1, h2⟩ := mem_shift17 M S₄ q hq
    obtain ⟨hc, hr⟩ := hcolrow p hp
    have := hC _ hc
    have := hR _ hr
    refine ⟨p, hp, ?_, by rw [h2], by simp [col] at *; omega, by simp [row] at *; omega⟩
    rw [h1]; push_cast [Nat.cast_sub (by omega : 2 ≤ 3 * M.n)]; ring
  have hinj : Function.Injective (fun q : Queen => q + (3 * M.n - 2, 0)) := by
    intro a b h; simpa using h
  -- rows of P are ≥ n, so P is disjoint from the shifted part
  have hrowP : ∀ q ∈ def16_QDm M ∪ def16_QDp M, (M.n : ℤ) ≤ q.2 := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨d, _, _, h2, h3, h4⟩ := mem_QDm M hM q hq; omega
    · obtain ⟨d, _, _, h2, _⟩ := mem_QDp M hM q hq; omega
  have hdisj : Disjoint (shiftSet S₄ (3 * M.n - 2, 0)) (def16_QDm M ∪ def16_QDp M) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨p, _, _, h2, _, h4⟩ := hshift q hq
    have := hrowP q hq'
    omega
  have hunion : lemma17_map M S₄ =
      shiftSet S₄ (3 * M.n - 2, 0) ∪ (def16_QDm M ∪ def16_QDp M) := by
    unfold lemma17_map; rw [Finset.union_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- cardinality
    rw [hunion, Finset.card_union_of_disjoint hdisj]
    simp only [def16]
    rw [Finset.card_image_of_injective _ (add_left_injective _), shiftSet,
      Finset.card_image_of_injective _ hinj, hcard]
  · rw [hunion]; exact Finset.subset_union_right
  · -- non-attacking
    intro q₁ h₁ q₂ h₂ hatt
    obtain ⟨hne, hl⟩ := attacks_int q₁ q₂ hatt
    rw [hunion, Finset.mem_union, Finset.mem_union] at h₁ h₂
    rcases h₁ with h₁ | h₁ | h₁ <;> rcases h₂ with h₂ | h₂ | h₂
    · -- shift / shift
      obtain ⟨p₁, hp₁, e₁, f₁, _, _⟩ := hshift q₁ h₁
      obtain ⟨p₂, hp₂, e₂, f₂, _, _⟩ := hshift q₂ h₂
      apply hNA p₁ hp₁ p₂ hp₂
      apply attacks_of_int
      · intro h; apply hne; omega
      · omega
    · -- shift / QDm
      obtain ⟨p₁, hp₁, e₁, f₁, g₁, g₁'⟩ := hshift q₁ h₁
      obtain ⟨d, hd, e₂, f₂, g₂, g₂'⟩ := mem_QDm M hM q₂ h₂
      have hp : (p₁.1 : ℤ) - p₁.2 ≠ d := by
        intro h; apply (hexcl p₁ hp₁).1; rw [diffDiag, h]; exact hd
      have : (0 : ℤ) ≤ p₁.1 := by positivity
      have : (0 : ℤ) ≤ p₁.2 := by positivity
      omega
    · -- shift / QDp
      obtain ⟨p₁, hp₁, e₁, f₁, g₁, g₁'⟩ := hshift q₁ h₁
      obtain ⟨d, hd, e₂, f₂, g₂⟩ := mem_QDp M hM q₂ h₂
      have hp : (p₁.1 : ℤ) + p₁.2 ≠ d := by
        intro h; apply (hexcl p₁ hp₁).2
        have : p₁.1 + p₁.2 = d := by exact_mod_cast h
        rw [sumDiag, this]; exact hd
      have : (0 : ℤ) ≤ p₁.1 := by positivity
      have : (0 : ℤ) ≤ p₁.2 := by positivity
      omega
    · -- QDm / shift
      obtain ⟨d, hd, e₁, f₁, g₁, g₁'⟩ := mem_QDm M hM q₁ h₁
      obtain ⟨p₂, hp₂, e₂, f₂, g₂, g₂'⟩ := hshift q₂ h₂
      have hp : (p₂.1 : ℤ) - p₂.2 ≠ d := by
        intro h; apply (hexcl p₂ hp₂).1; rw [diffDiag, h]; exact hd
      have : (0 : ℤ) ≤ p₂.1 := by positivity
      have : (0 : ℤ) ≤ p₂.2 := by positivity
      omega
    · -- QDm / QDm
      obtain ⟨d, hd, e₁, f₁, g₁, g₁'⟩ := mem_QDm M hM q₁ h₁
      obtain ⟨d', hd', e₂, f₂, g₂, g₂'⟩ := mem_QDm M hM q₂ h₂
      apply hne; omega
    · -- QDm / QDp
      obtain ⟨d, hd, e₁, f₁, g₁, g₁'⟩ := mem_QDm M hM q₁ h₁
      obtain ⟨d', hd', e₂, f₂, g₂⟩ := mem_QDp M hM q₂ h₂
      omega
    · -- QDp / shift
      obtain ⟨d, hd, e₁, f₁, g₁⟩ := mem_QDp M hM q₁ h₁
      obtain ⟨p₂, hp₂, e₂, f₂, g₂, g₂'⟩ := hshift q₂ h₂
      have hp : (p₂.1 : ℤ) + p₂.2 ≠ d := by
        intro h; apply (hexcl p₂ hp₂).2
        have : p₂.1 + p₂.2 = d := by exact_mod_cast h
        rw [sumDiag, this]; exact hd
      have : (0 : ℤ) ≤ p₂.1 := by positivity
      have : (0 : ℤ) ≤ p₂.2 := by positivity
      omega
    · -- QDp / QDm
      obtain ⟨d, hd, e₁, f₁, g₁⟩ := mem_QDp M hM q₁ h₁
      obtain ⟨d', hd', e₂, f₂, g₂, g₂'⟩ := mem_QDm M hM q₂ h₂
      omega
    · -- QDp / QDp
      obtain ⟨d, hd, e₁, f₁, g₁⟩ := mem_QDp M hM q₁ h₁
      obtain ⟨d', hd', e₂, f₂, g₂⟩ := mem_QDp M hM q₂ h₂
      apply hne; omega
  · -- columns and rows of the non-prescribed queens
    intro q hq
    rw [Finset.mem_sdiff, hunion, Finset.mem_union] at hq
    obtain ⟨hq, hqP⟩ := hq
    have hq' : q ∈ shiftSet S₄ (3 * M.n - 2, 0) := by
      rcases hq with h | h
      · exact h
      · exact absurd h hqP
    obtain ⟨p, hp, h1, h2⟩ := mem_shift17 M S₄ q hq'
    obtain ⟨hc, hr⟩ := hcolrow p hp
    simp only [def16, col, row] at *
    refine ⟨?_, h2 ▸ hr⟩
    rw [Finset.mem_image]
    exact ⟨p.1, hc, h1.symm⟩
