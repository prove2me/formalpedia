-- Prove2me | solution 1 for MyersonBargaining.NashSolution.uniform_mechanism_bic
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:25:36.241661+00:00
-- url     : https://prove2.me/submissions/727ce621-802b-4007-a23e-658caaa1e825

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining
set_option autoImplicit false
open MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

theorem solution (G : Problem ι A C) :
    let π : C → (∀ i, A i) → ℝ := fun _ _ => 1 / (Fintype.card C : ℝ)
    IsChoiceMechanism π ∧ IsBIC G π := by
  intro π
  have hcard : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  refine ⟨⟨fun c s => ?_, fun s => ?_⟩, ?_⟩
  · simp only [π]; positivity
  · simp only [π, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · intro i a b
    apply le_of_eq
    simp [Z, π]
