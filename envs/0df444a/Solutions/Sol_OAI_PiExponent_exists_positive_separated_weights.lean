-- Prove2me | solution 1 for OAI.PiExponent.exists_positive_separated_weights
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:24:41.113828+00:00
-- url     : https://prove2.me/submissions/31390a3e-470a-404b-b657-1bfd8d71e65a

import Definitions.Def_PiExponent_DeterminantSetup
import Theorems.Thm_OAI_PiExponent_extend_positive_separated_weights

theorem solution
    (S : List ℕ → ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ w : Fin m → ℕ,
      (∀ i, 0 < w i) ∧ OAI.PiExponent.separatedWeights S w := by
  have hAll : ∀ n : ℕ, ∃ w : Fin n → ℕ,
      (∀ i, 0 < w i) ∧ OAI.PiExponent.separatedWeights S w := by
    intro n
    induction n with
    | zero =>
        exact ⟨fun i => Fin.elim0 i,
          ⟨by intro i; exact Fin.elim0 i,
           by intro i; exact Fin.elim0 i⟩⟩
    | succ n ih =>
        obtain ⟨w, hw, hsep⟩ := ih
        exact OAI.PiExponent.extend_positive_separated_weights S n w hw hsep
  obtain ⟨w, hw, hsep⟩ := hAll m
  exact ⟨w, hw, hsep⟩
