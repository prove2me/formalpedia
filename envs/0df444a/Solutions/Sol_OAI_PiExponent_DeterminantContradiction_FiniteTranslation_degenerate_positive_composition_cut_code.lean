-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.degenerate_positive_composition_cut_code
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T22:09:10.373186+00:00
-- url     : https://prove2.me/submissions/086a515d-26f0-42dd-bf40-8c12b36ae8e8

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Definitions.Def_OAI_PiExponent_logMajorantCompositions

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution (q k : ℕ) (h : q = 0 ∨ k = 0 ∨ q = 1) :
    ∃ f : {a // a ∈ logMajorantCompositions q k} → Finset (Fin k),
      Function.Injective f := by
  classical
  letI : Subsingleton {a // a ∈ logMajorantCompositions q k} := by
    constructor
    intro a b
    rcases h with hq | hk | hq
    · subst q
      apply Subtype.ext
      funext i
      exact Fin.elim0 i
    · subst k
      cases q with
      | zero =>
          apply Subtype.ext
          funext i
          exact Fin.elim0 i
      | succ q' =>
          have parts (x : {a // a ∈ logMajorantCompositions (q' + 1) 0}) :
              (∀ i, 0 < x.val i) ∧ (∑ i : Fin (q' + 1), x.val i = 0) := by
            have hx := x.property
            simp only [logMajorantCompositions, Finset.mem_filter] at hx
            exact hx.2
          have hpos : 0 < ∑ i : Fin (q' + 1), a.val i :=
            Finset.sum_pos (fun i _ => (parts a).1 i) ⟨0, Finset.mem_univ _⟩
          exact False.elim ((Nat.ne_of_gt hpos) (parts a).2)
    · subst q
      have parts (x : {a // a ∈ logMajorantCompositions 1 k}) :
          (∀ i, 0 < x.val i) ∧ (∑ i : Fin 1, x.val i = k) := by
        have hx := x.property
        simp only [logMajorantCompositions, Finset.mem_filter] at hx
        exact hx.2
      have ha : a.val 0 = k := by simpa using (parts a).2
      have hb : b.val 0 = k := by simpa using (parts b).2
      apply Subtype.ext
      funext i
      have hi : i = 0 := Fin.eq_zero i
      rw [hi, ha, hb]
  refine ⟨fun _ => ∅, ?_⟩
  intro a b _
  exact Subsingleton.elim a b