-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_genF_locals_of_W_rec
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:02:23.567201+00:00
-- url     : https://prove2.me/submissions/e7f36bac-4716-4a64-a782-6e815aa57724

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRec
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open IntMul.Kappa.R8.Bit.Oppbank.NB

/-- Moves from `foldl (mvF c)` started at empty move list come from `ws`. -/
private theorem foldl_mvF_from_empty (c : ℕ) (ws : List ℕ) (st : ℕ → ℕ) :
    ∀ p ∈ (ws.foldl (mvF c) (st, [])).2, p.1 ∈ ws := by
  have gen : ∀ (ws : List ℕ) (acc : (ℕ → ℕ) × List (ℕ × ℕ)),
      ∀ p ∈ (ws.foldl (mvF c) acc).2, p.1 ∈ ws ∨ p ∈ acc.2 := by
    intro ws
    induction ws with
    | nil =>
      intro acc p hp; exact Or.inr hp
    | cons w ws ih =>
      intro acc p hp
      have hp' : p ∈ (ws.foldl (mvF c) (mvF c acc w)).2 := by
        simpa [List.foldl_cons] using hp
      rcases ih (mvF c acc w) p hp' with hws | hmv
      · exact Or.inl (List.mem_cons_of_mem _ hws)
      · dsimp [mvF] at hmv
        split_ifs at hmv with _
        · exact Or.inr hmv
        · simp only [List.mem_cons] at hmv
          rcases hmv with hEq | hmv
          · left
            have : p.1 = w := congrArg Prod.fst hEq
            simpa [this] using (List.mem_cons_self (a := w) (l := ws))
          · exact Or.inr hmv
  intro p hp
  exact (gen ws (st, []) p hp).resolve_right (fun h => by cases h)

private theorem locals_of_fresh (acc : (ℕ → ℕ) × List LChunk) (i : LInstr) (ℓ : ℕ)
    (hℓ : (∃ mv ∈ (i.2.1.foldl (mvF i.1) (acc.1, [])).2.reverse, mv.1 = ℓ) ∨
          (∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ)) :
    ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ := by
  rcases hℓ with ⟨mv, hmv, rfl⟩ | hxor
  · have : mv ∈ (i.2.1.foldl (mvF i.1) (acc.1, [])).2 := by
      simpa [List.mem_reverse] using hmv
    exact Or.inl (foldl_mvF_from_empty i.1 i.2.1 acc.1 mv this)
  · exact Or.inr hxor

/-- Chunk locals in the foldl accumulator come from instructions in `done ++ ws`. -/
private theorem foldl_genStepF_locals (ℓ : ℕ) :
    ∀ (done ws : List LInstr) (acc : (ℕ → ℕ) × List LChunk),
      (∀ ch ∈ acc.2,
        ((∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)) →
          ∃ i ∈ done, ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ) →
      ∀ ch ∈ (ws.foldl genStepF acc).2,
        ((∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)) →
          ∃ i ∈ done ++ ws, ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ := by
  intro done ws
  induction ws generalizing done with
  | nil =>
    intro acc hacc ch hch hℓch
    obtain ⟨i, hi, h⟩ := hacc ch hch hℓch
    exact ⟨i, List.mem_append_left _ hi, h⟩
  | cons i ws ih =>
    intro acc hacc ch hch hℓch
    have hshape :
        (genStepF acc i).2 =
          (i.1, (i.2.1.foldl (mvF i.1) (acc.1, [])).2.reverse, i.2.2) :: acc.2 := by
      simp only [genStepF]
    have hacc' : ∀ ch ∈ (genStepF acc i).2,
        ((∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)) →
          ∃ j ∈ done ++ [i], ℓ ∈ j.2.1 ∨ ∃ p ∈ j.2.2, p.1 = ℓ ∨ p.2 = ℓ := by
      intro ch hch' hℓch'
      rw [hshape] at hch'
      rcases List.mem_cons.1 hch' with heq | hold
      · subst heq
        refine ⟨i, ?_, locals_of_fresh acc i ℓ ?_⟩
        · simp
        · -- hℓch' after subst
          simpa using hℓch'
      · obtain ⟨j, hj, h⟩ := hacc ch hold hℓch'
        exact ⟨j, List.mem_append_left _ hj, h⟩
    have hch' : ch ∈ (ws.foldl genStepF (genStepF acc i)).2 := by
      simpa [List.foldl_cons] using hch
    obtain ⟨j, hj, h⟩ := ih (done ++ [i]) (genStepF acc i) hacc' ch hch' hℓch
    refine ⟨j, ?_, h⟩
    simpa [List.append_assoc, List.singleton_append] using hj

theorem solution (f : ℕ → ℕ) (W : List LInstr) (ℓ : ℕ)
    (hℓ : ∃ ch ∈ (genF f W).2,
      (∃ mv ∈ ch.2.1, mv.1 = ℓ) ∨ (∃ p ∈ ch.2.2, p.1 = ℓ ∨ p.2 = ℓ)) :
    ∃ i ∈ W, ℓ ∈ i.2.1 ∨ ∃ p ∈ i.2.2, p.1 = ℓ ∨ p.2 = ℓ := by
  simp only [genF] at hℓ
  obtain ⟨ch, hch, hℓch⟩ := hℓ
  have hch' : ch ∈ (W.foldl genStepF (f, [])).2 := by
    simpa [List.mem_reverse] using hch
  obtain ⟨i, hi, h⟩ :=
    foldl_genStepF_locals ℓ [] W (f, []) (by intro ch hch; cases hch) ch hch' hℓch
  exact ⟨i, by simpa using hi, h⟩
