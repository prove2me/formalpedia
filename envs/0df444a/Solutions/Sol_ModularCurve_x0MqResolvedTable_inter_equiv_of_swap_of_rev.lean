-- Prove2me | solution 1 for ModularCurve.x0MqResolvedTable_inter_equiv_of_swap_of_rev
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/107ef1a7-5c90-5afc-a3f3-567b65edf2cb

import Mathlib
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_x0MqResolvedTable_inter_equiv_of_swap_of_rev

set_option autoImplicit false

open ModularCurve MazurRapoportAppendix
open scoped BigOperators

theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → ℕ)
    (Φ : X0MqComponents e ≃ X0MqComponents e)
    (hΦ0 : Φ (Sum.inl 0) = Sum.inl 1) (hΦ1 : Φ (Sum.inl 1) = Sum.inl 0)
    (hΦr : ∀ (x : ι) (k k' : Fin (e x - 1)), k.val + k'.val + 2 = e x → Φ (Sum.inr ⟨x, k⟩) = Sum.inr ⟨x, k'⟩)
    (a b : X0MqComponents e) :
    (x0MqResolvedTable e).inter (Φ a) (Φ b) = (x0MqResolvedTable e).inter a b := by

  have hr : ∀ (x : ι) (k : Fin (e x - 1)),
      Φ (Sum.inr ⟨x, k⟩) = Sum.inr ⟨x, ⟨e x - 2 - k.val, by have := k.isLt; omega⟩⟩ :=
    fun x k => hΦr x k _ (by have := k.isLt; simp only; omega)

  have hl : ∀ i : Fin 2, Φ (Sum.inl i) = Sum.inl (Fin.rev i) := by
    intro i
    fin_cases i
    · simpa using hΦ0
    · simpa using hΦ1

  have hadj : ∀ a b : X0MqComponents e, x0MqAdj e (Φ a) (Φ b) = x0MqAdj e a b := by
    intro a b
    rcases a with i | ⟨x, k⟩ <;> rcases b with j | ⟨y, l⟩
    · simp only [hl, x0MqAdj, ne_eq, Fin.rev_inj]
    · rw [hl, hr]
      have hl' := l.isLt
      simp only [x0MqAdj]
      congr 1
      apply propext
      fin_cases i <;> simp [Fin.ext_iff] <;> omega
    · rw [hl, hr]
      have hk := k.isLt
      simp only [x0MqAdj]
      congr 1
      apply propext
      fin_cases j <;> simp [Fin.ext_iff] <;> omega
    · rw [hr, hr]
      have hk := k.isLt
      have hl' := l.isLt
      simp only [x0MqAdj]
      congr 1
      apply propext
      constructor
      · rintro ⟨rfl, h⟩
        exact ⟨rfl, by omega⟩
      · rintro ⟨rfl, h⟩
        exact ⟨rfl, by omega⟩
  have hdiag : (∑ j', (x0MqAdj e (Φ a) j' : ℤ)) = ∑ j, (x0MqAdj e a j : ℤ) := by
    rw [← Φ.sum_comp]
    exact Finset.sum_congr rfl fun j _ => by rw [hadj]
  simp only [x0MqResolvedTable, hadj, Φ.injective.eq_iff, hdiag]

end S_ModularCurve_x0MqResolvedTable_inter_equiv_of_swap_of_rev
end P2MW
export P2MW.S_ModularCurve_x0MqResolvedTable_inter_equiv_of_swap_of_rev (solution)
