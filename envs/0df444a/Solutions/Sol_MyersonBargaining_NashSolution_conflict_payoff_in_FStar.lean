-- Prove2me | solution 1 for MyersonBargaining.NashSolution.conflict_payoff_in_FStar
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:23:47.074579+00:00
-- url     : https://prove2.me/submissions/ba940ee1-2cb8-4496-aa8b-734f4dff6fb4

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining
set_option autoImplicit false
open MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

theorem solution (G : Problem ι A C) (cstar : C) :
    IsChoiceMechanism (constMech (A := A) cstar) ∧
    IsBIC G (constMech (A := A) cstar) ∧
    V G (constMech (A := A) cstar) = conflictPayoff G cstar ∧
    conflictPayoff G cstar ∈ FStar G := by
  have hZ : ∀ (i : ι) (b a : A i),
      Z G i (constMech (A := A) cstar) b a = conflictPayoff G cstar ⟨i, a⟩ := by
    intro i b a
    unfold Z conflictPayoff constMech
    apply Finset.sum_congr rfl
    intro α _
    simp [mul_ite, ite_mul]
  have hmech : IsChoiceMechanism (constMech (A := A) cstar) := by
    refine ⟨fun c s => ?_, fun s => ?_⟩
    · unfold constMech; split_ifs <;> norm_num
    · unfold constMech; simp
  have hbic : IsBIC G (constMech (A := A) cstar) := by
    intro i a b
    rw [hZ, hZ]
  have hV : V G (constMech (A := A) cstar) = conflictPayoff G cstar := by
    funext x
    exact hZ x.1 x.2 x.2
  exact ⟨hmech, hbic, hV, ⟨_, hmech, hbic, hV⟩⟩
