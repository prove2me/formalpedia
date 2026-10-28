-- Prove2me | solution 1 for NQueensComp.NPC.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:37:01.536224+00:00
-- url     : https://prove2.me/submissions/1d5b5fe4-e34c-412a-afea-6b8def570543

import Mathlib
import Definitions.Def_NQueensComp_NPC_Queens

open NQueensComp.NPC

/-- From equality of images: every element of `P₁` shares its `f`-value with some element of
`P`. -/
theorem exists_of_image_eq {α : Type*} [DecidableEq α] (f : Queen → α) (P P₁ : Finset Queen)
    (h : P₁.image f = P.image f) (p₁ : Queen) (hp₁ : p₁ ∈ P₁) : ∃ p ∈ P, f p = f p₁ := by
  have : f p₁ ∈ P.image f := h ▸ Finset.mem_image_of_mem f hp₁
  obtain ⟨p, hp, hfp⟩ := Finset.mem_image.mp this
  exact ⟨p, hp, hfp⟩

/-- A non-attacking set has injective column/row/diagonal maps. -/
theorem injOn_of_nonAttacking {α : Type*} (f : Queen → α) (Q : Finset Queen)
    (hQ : NonAttacking Q)
    (hf : ∀ q q' : Queen, f q = f q' →
      col q = col q' ∨ row q = row q' ∨ sumDiag q = sumDiag q' ∨ diffDiag q = diffDiag q') :
    Set.InjOn f Q := by
  intro q hq q' hq' heq
  by_contra hne
  exact hQ q hq q' hq' ⟨hne, hf q q' heq⟩

theorem solution (n : ℕ) (Q P P₁ : Finset Queen) (hQ : IsNQueensSol n Q) (hPQ : P ⊆ Q)
    (hcard : P₁.card = P.card)
    (hrow : P₁.image row = P.image row) (hcol : P₁.image col = P.image col)
    (hsum : P₁.image sumDiag = P.image sumDiag) (hdiff : P₁.image diffDiag = P.image diffDiag) :
    IsNQueensSol n ((Q \ P) ∪ P₁) := by
  obtain ⟨hn, hfit, hQcard, hNA⟩ := hQ
  have hNAP : NonAttacking P := fun q₁ h₁ q₂ h₂ => hNA q₁ (hPQ h₁) q₂ (hPQ h₂)
  -- injectivity on P₁ of the four maps
  have inj₁ : ∀ {α : Type} [DecidableEq α] (f : Queen → α), P₁.image f = P.image f →
      (∀ q q' : Queen, f q = f q' →
        col q = col q' ∨ row q = row q' ∨ sumDiag q = sumDiag q' ∨ diffDiag q = diffDiag q') →
      Set.InjOn f P₁ := by
    intro α _ f himg hf
    have h1 : Set.InjOn f P := injOn_of_nonAttacking f P hNAP hf
    have h2 : (P₁.image f).card = P₁.card := by
      rw [himg, Finset.card_image_of_injOn h1, hcard]
    exact Finset.card_image_iff.mp h2
  have injcol : Set.InjOn col P₁ := inj₁ col hcol (fun q q' h => Or.inl h)
  have injrow : Set.InjOn row P₁ := inj₁ row hrow (fun q q' h => Or.inr (Or.inl h))
  have injsum : Set.InjOn sumDiag P₁ := inj₁ sumDiag hsum (fun q q' h => Or.inr (Or.inr (Or.inl h)))
  have injdiff : Set.InjOn diffDiag P₁ :=
    inj₁ diffDiag hdiff (fun q q' h => Or.inr (Or.inr (Or.inr h)))
  -- a queen of Q \ P never shares a line with a queen of P₁
  have noShare : ∀ q ∈ Q \ P, ∀ p₁ ∈ P₁,
      ¬ (col q = col p₁ ∨ row q = row p₁ ∨ sumDiag q = sumDiag p₁ ∨ diffDiag q = diffDiag p₁) := by
    intro q hq p₁ hp₁ h
    rw [Finset.mem_sdiff] at hq
    have key : ∀ {α : Type} [DecidableEq α] (f : Queen → α), P₁.image f = P.image f →
        (∀ q q' : Queen, f q = f q' →
          col q = col q' ∨ row q = row q' ∨ sumDiag q = sumDiag q' ∨ diffDiag q = diffDiag q') →
        f q = f p₁ → False := by
      intro α _ f himg hf hfq
      obtain ⟨p, hp, hfp⟩ := exists_of_image_eq f P P₁ himg p₁ hp₁
      have hne : q ≠ p := fun h => hq.2 (h ▸ hp)
      exact hNA q hq.1 p (hPQ hp) ⟨hne, hf q p (hfq.trans hfp.symm)⟩
    rcases h with h | h | h | h
    · exact key col hcol (fun q q' h => Or.inl h) h
    · exact key row hrow (fun q q' h => Or.inr (Or.inl h)) h
    · exact key sumDiag hsum (fun q q' h => Or.inr (Or.inr (Or.inl h))) h
    · exact key diffDiag hdiff (fun q q' h => Or.inr (Or.inr (Or.inr h))) h
  have hdisj : Disjoint (Q \ P) P₁ := by
    rw [Finset.disjoint_left]
    intro q hq hq₁
    exact noShare q hq q hq₁ (Or.inl rfl)
  refine ⟨hn, ?_, ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · exact hfit q (Finset.mem_sdiff.mp hq).1
    · obtain ⟨p, hp, hcp⟩ := exists_of_image_eq col P P₁ hcol q hq
      obtain ⟨p', hp', hrp⟩ := exists_of_image_eq row P P₁ hrow q hq
      have h1 := hfit p (hPQ hp)
      have h2 := hfit p' (hPQ hp')
      simp only [FitsOn, size, max_lt_iff, col, row] at h1 h2 hcp hrp ⊢
      omega
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hPQ, hcard, hQcard]
    have := Finset.card_le_card hPQ
    omega
  · intro q₁ h₁ q₂ h₂ hatt
    obtain ⟨hne, hline⟩ := hatt
    rw [Finset.mem_union] at h₁ h₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact hNA q₁ (Finset.mem_sdiff.mp h₁).1 q₂ (Finset.mem_sdiff.mp h₂).1 ⟨hne, hline⟩
    · exact noShare q₁ h₁ q₂ h₂ hline
    · apply noShare q₂ h₂ q₁ h₁
      rcases hline with h | h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · exact Or.inr (Or.inr (Or.inr h.symm))
    · apply hne
      rcases hline with h | h | h | h
      · exact injcol h₁ h₂ h
      · exact injrow h₁ h₂ h
      · exact injsum h₁ h₂ h
      · exact injdiff h₁ h₂ h
