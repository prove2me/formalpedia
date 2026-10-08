-- Prove2me | solution 1 for HallReps.CDR.cdr_of_not_subset_cdrMeet
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T14:24:56.458111+00:00
-- url     : https://prove2.me/submissions/2c455b60-13c7-4a97-8b5f-469f33425744

import Mathlib
import Definitions.Def_HallReps_CDR_System

set_option autoImplicit false

open HallReps.CDR

theorem solution {α : Type*} {m : ℕ} (T : Fin (m + 1) → Set α)
    (hT : ¬ T (Fin.last m) ⊆ cdrMeet (fun i : Fin m => T i.castSucc)) :
    ∃ a : Fin (m + 1) → α, IsCDR T a := by
  -- an element of `T m` that is missed by some C.D.R. of the shorter system
  obtain ⟨x, hxT, hxR⟩ := Set.not_subset.mp hT
  have hex : ∃ b : Fin m → α, IsCDR (fun i : Fin m => T i.castSucc) b ∧ x ∉ Set.range b := by
    by_contra hcon
    apply hxR
    intro b hb
    by_contra hxb
    exact hcon ⟨b, hb, hxb⟩
  obtain ⟨b, ⟨hbinj, hbmem⟩, hxb⟩ := hex
  refine ⟨Fin.snoc (α := fun _ => α) b x, ?_, ?_⟩
  · -- injectivity
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd ⟨j, hij.symm⟩ hxb
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd ⟨i, hij⟩ hxb
      | cast j =>
        simp only [Fin.snoc_castSucc] at hij
        exact congrArg Fin.castSucc (hbinj hij)
  · intro i
    induction i using Fin.lastCases with
    | last => simpa using hxT
    | cast i => simpa using hbmem i

#print axioms solution
