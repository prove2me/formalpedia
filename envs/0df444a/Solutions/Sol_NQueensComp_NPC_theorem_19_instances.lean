-- Prove2me | solution 1 for NQueensComp.NPC.theorem_19_instances
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-11-03T02:53:41.836412+00:00
-- url     : https://prove2.me/submissions/bc0b8884-5745-46ca-b1f1-9568e368cf27

import Mathlib
import Definitions.Def_NQueensComp_NPC_Reductions
import Theorems.Thm_NQueensComp_NPC_lemma_17
import Theorems.Thm_NQueensComp_NPC_lemma_18

open NQueensComp.NPC

namespace NQueensComp.NPC.T19Proof

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

theorem valid_facts (M : Inst4) (hM : M.Valid) :
    1 ≤ M.n ∧ M.C.card = M.R.card ∧ (∀ c ∈ M.C, c < M.n) ∧ (∀ r ∈ M.R, r < M.n) := by
  obtain ⟨⟨⟨h1, _, _⟩, h2, _, h3, h4⟩, _, _⟩ := hM
  exact ⟨h1, h2, h3, h4⟩

/-- Every queen of `Q_{D⁻} ∪ Q_{D⁺}` lies in a row `≥ n`. -/
theorem row_P (M : Inst4) (hM : M.Valid) (q : Queen) (hq : q ∈ def16_QDm M ∪ def16_QDp M) :
    M.n ≤ q.2 := by
  rcases Finset.mem_union.mp hq with hq | hq
  · obtain ⟨d, _, _, h2, h3, h4⟩ := mem_QDm M hM q hq; omega
  · obtain ⟨d, _, _, h2, _⟩ := mem_QDp M hM q hq; omega

/-- Definition 16 sends instances of Problem 4 to instances of Problem 3. -/
theorem valid_def16 (M : Inst4) (hM : M.Valid) : (def16 M).Valid := by
  obtain ⟨hn, hCR, hC, hR⟩ := valid_facts M hM
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ 7 * M.n - 3
    omega
  · intro q hq
    show max q.1 q.2 < 7 * M.n - 3
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨d, _, h1, h2, h3, h4⟩ := mem_QDm M hM q hq
      rw [max_lt_iff]; constructor <;> omega
    · obtain ⟨d, _, h1, h2, h3⟩ := mem_QDp M hM q hq
      rw [max_lt_iff]; constructor <;> omega
  · intro q₁ h₁ q₂ h₂ hne
    simp only [col, row]
    rcases Finset.mem_union.mp h₁ with h₁ | h₁ <;> rcases Finset.mem_union.mp h₂ with h₂ | h₂
    · obtain ⟨d₁, _, a₁, b₁, -, -⟩ := mem_QDm M hM q₁ h₁
      obtain ⟨d₂, _, a₂, b₂, -, -⟩ := mem_QDm M hM q₂ h₂
      refine ⟨fun h => hne (Prod.ext h ?_), fun h => hne (Prod.ext ?_ h)⟩ <;> omega
    · obtain ⟨d₁, _, a₁, b₁, c₁, -⟩ := mem_QDm M hM q₁ h₁
      obtain ⟨d₂, _, a₂, b₂, c₂⟩ := mem_QDp M hM q₂ h₂
      constructor <;> intro h <;> omega
    · obtain ⟨d₁, _, a₁, b₁, c₁⟩ := mem_QDp M hM q₁ h₁
      obtain ⟨d₂, _, a₂, b₂, c₂, -⟩ := mem_QDm M hM q₂ h₂
      constructor <;> intro h <;> omega
    · obtain ⟨d₁, _, a₁, b₁, -⟩ := mem_QDp M hM q₁ h₁
      obtain ⟨d₂, _, a₂, b₂, -⟩ := mem_QDp M hM q₂ h₂
      refine ⟨fun h => hne (Prod.ext h ?_), fun h => hne (Prod.ext ?_ h)⟩ <;> omega
  · show (M.C.image fun c => c + (3 * M.n - 2)).card = M.R.card
    rw [Finset.card_image_of_injective _ (add_left_injective _), hCR]
  · intro q hq
    have hrow := row_P M hM q hq
    refine ⟨fun hc => ?_, fun hr => ?_⟩
    · obtain ⟨c, hcC, hcq⟩ := Finset.mem_image.mp hc
      have := hC c hcC
      simp only [col] at hcq
      rcases Finset.mem_union.mp hq with hq | hq
      · obtain ⟨d, _, h1, h2, h3, h4⟩ := mem_QDm M hM q hq; omega
      · obtain ⟨d, _, h1, h2, h3⟩ := mem_QDp M hM q hq; omega
    · have := hR _ hr
      simp only [row] at this
      omega
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    have := hC c' hc'
    show c' + (3 * M.n - 2) < 7 * M.n - 3
    omega
  · intro r hr
    have := hR r hr
    show r < 7 * M.n - 3
    omega

/-- Lemma 18's map undoes Lemma 17's map. -/
theorem left_inv (M : Inst4) (hM : M.Valid) (S₄ : Finset Queen) (hS : M.IsSol S₄) :
    lemma18_map M (lemma17_map M S₄) = S₄ := by
  have hrow : ∀ q ∈ S₄, q.2 < M.n := fun q hq =>
    (valid_facts M hM).2.2.2 _ (hS.1.2.2.2 q (by simpa [Inst4.toInst3] using hq)).2
  ext q
  simp only [lemma18_map, lemma17_map, shiftSet, Finset.mem_image, Finset.mem_filter,
    Finset.mem_union]
  constructor
  · rintro ⟨p, ⟨(⟨s, hs, rfl⟩ | hp) | hp, h1, h2⟩, rfl⟩
    · simpa using hs
    · have := row_P M hM p (Finset.mem_union_left _ hp); omega
    · have := row_P M hM p (Finset.mem_union_right _ hp); omega
  · intro hq
    refine ⟨q + (3 * M.n - 2, 0), ⟨Or.inl (Or.inl ⟨q, hq, rfl⟩), ?_, ?_⟩, ?_⟩
    · simp
    · simpa using hrow q hq
    · simp

/-- Lemma 17's map undoes Lemma 18's map on solutions of `def16 M`. -/
theorem right_inv (M : Inst4) (hM : M.Valid) (S₃ : Finset Queen) (hS : (def16 M).IsSol S₃) :
    lemma17_map M (lemma18_map M S₃) = S₃ := by
  obtain ⟨hn, hCR, hC, hR⟩ := valid_facts M hM
  obtain ⟨-, hPS, -, hcolrow⟩ := hS
  simp only [def16] at hPS hcolrow
  have hfilt : ∀ q ∈ S₃, q ∉ def16_QDm M ∪ def16_QDp M → 3 * M.n - 2 ≤ q.1 ∧ q.2 < M.n := by
    intro q hq hqP
    obtain ⟨hc, hr⟩ := hcolrow q (Finset.mem_sdiff.mpr ⟨hq, hqP⟩)
    obtain ⟨c, _, hcq⟩ := Finset.mem_image.mp hc
    simp only [col] at hcq
    exact ⟨by omega, hR _ hr⟩
  ext q
  simp only [lemma18_map, lemma17_map, shiftSet, Finset.mem_image, Finset.mem_filter,
    Finset.mem_union]
  constructor
  · rintro ((⟨s, ⟨p, ⟨hp, h1, -⟩, rfl⟩, rfl⟩ | hq) | hq)
    · have : (p.1 - (3 * M.n - 2), p.2) + ((3 * M.n - 2 : ℕ), (0 : ℕ)) = p :=
        Prod.ext (by simp; omega) (by simp)
      rw [this]; exact hp
    · exact hPS (Finset.mem_union_left _ hq)
    · exact hPS (Finset.mem_union_right _ hq)
  · intro hq
    by_cases hqP : q ∈ def16_QDm M ∪ def16_QDp M
    · rcases Finset.mem_union.mp hqP with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · obtain ⟨h1, h2⟩ := hfilt q hq hqP
      refine Or.inl (Or.inl ⟨(q.1 - (3 * M.n - 2), q.2), ⟨q, ⟨hq, h1, h2⟩, rfl⟩, ?_⟩)
      exact Prod.ext (by simp; omega) (by simp)

end NQueensComp.NPC.T19Proof

open NQueensComp.NPC.T19Proof in
theorem solution :
    ∀ M : Inst4, M.Valid →
      (def16 M).Valid ∧
        _root_.Set.ncard {S : Finset Queen | (def16 M).IsSol S} =
          _root_.Set.ncard {S : Finset Queen | M.IsSol S} := by
  intro M hM
  refine ⟨valid_def16 M hM, ?_⟩
  refine Set.ncard_congr (fun S _ => lemma18_map M S) ?_ ?_ ?_
  · intro S hS
    exact lemma_18 M hM S hS
  · intro S S' hS hS' h
    rw [← right_inv M hM S hS, ← right_inv M hM S' hS']
    exact congrArg (lemma17_map M) h
  · intro S₄ hS₄
    exact ⟨lemma17_map M S₄, lemma_17 M hM S₄ hS₄, left_inv M hM S₄ hS₄⟩
