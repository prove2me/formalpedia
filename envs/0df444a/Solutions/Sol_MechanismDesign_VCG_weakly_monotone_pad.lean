-- Prove2me | solution 1 for MechanismDesign.VCG.weakly_monotone_pad
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:05:16.725291+00:00
-- url     : https://prove2.me/submissions/9bb3b3db-e30c-4944-a4c4-21ed1dcf74f3

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model



namespace MechanismDesign.VCG

theorem weakly_monotone_pad_core {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) (hq : WeaklyMonotoneInEvery u q) :
    PAD u q := by
  intro θ θ' a hqa hdiff
  let P : Finset ι → (∀ j, Θ j) := fun s j => if j ∈ s then θ' j else θ j
  have key : ∀ s : Finset ι, q (P s) = a := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa [P] using hqa
    | @insert i s hi ih =>
      have hP : P (insert i s) = Function.update (P s) i (θ' i) := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [P]
        · simp [P, hj, Function.update_of_ne hj]
      have hPi : Function.update (P s) i (θ i) = P s := by
        funext j
        by_cases hj : j = i
        · subst hj; simp [P, hi]
        · simp [Function.update_of_ne hj]
      rw [hP]
      by_contra hne
      have hw := hq i (P s) (θ' i) (θ i)
      simp only [hPi, ih] at hw
      have := hdiff i _ hne
      linarith
  have : P Finset.univ = θ' := by funext j; simp [P]
  rw [← this]; exact key _

end MechanismDesign.VCG

open MechanismDesign.VCG


theorem solution {ι A : Type*} {Θ : ι → Type*} [Fintype ι] [DecidableEq ι]
    (u : ∀ i, A → Θ i → ℝ) (q : (∀ i, Θ i) → A) (hq : WeaklyMonotoneInEvery u q) :
    PAD u q := by
  exact weakly_monotone_pad_core u q hq
