-- Prove2me | solution 1 for ModularCurve.x0MqResolvedTable_inter_equiv_of_width_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6c1596c2-fa44-5199-9451-2831c1538c53

import Mathlib
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_x0MqResolvedTable_inter_equiv_of_width_eq

set_option autoImplicit false

open ModularCurve MazurRapoportAppendix
open scoped BigOperators

theorem solution
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (e : ι → ℕ) (e' : ι' → ℕ) (φ : ι ≃ ι') (hφ : ∀ x, e' (φ x) = e x)
    (Φ : X0MqComponents e ≃ X0MqComponents e')
    (hΦl : ∀ i : Fin 2, Φ (Sum.inl i) = Sum.inl i)
    (hΦr : ∀ (x : ι) (k : Fin (e x - 1)) (k' : Fin (e' (φ x) - 1)), k.val = k'.val →
      Φ (Sum.inr ⟨x, k⟩) = Sum.inr ⟨φ x, k'⟩)
    (a b : X0MqComponents e) :
    (x0MqResolvedTable e').inter (Φ a) (Φ b) = (x0MqResolvedTable e).inter a b := by

  have hr : ∀ (x : ι) (k : Fin (e x - 1)),
      Φ (Sum.inr ⟨x, k⟩) = Sum.inr ⟨φ x, ⟨k.val, by rw [hφ]; exact k.isLt⟩⟩ :=
    fun x k => hΦr x k _ rfl

  have hcard : (Finset.univ.filter fun x' : ι' => e' x' = 1).card = (Finset.univ.filter fun x : ι => e x = 1).card := by
    symm
    apply Finset.card_equiv φ
    intro x
    simp [hφ]

  have hadj : ∀ a b : X0MqComponents e, x0MqAdj e' (Φ a) (Φ b) = x0MqAdj e a b := by
    intro a b
    rcases a with i | ⟨x, k⟩ <;> rcases b with j | ⟨y, l⟩
    · simp only [hΦl, x0MqAdj, hcard]
    · rw [hΦl, hr]; simp only [x0MqAdj, hφ]
    · rw [hΦl, hr]; simp only [x0MqAdj, hφ]
    · rw [hr, hr]; simp only [x0MqAdj, φ.injective.eq_iff]

  have hdiag : (∑ j', (x0MqAdj e' (Φ a) j' : ℤ)) = ∑ j, (x0MqAdj e a j : ℤ) := by
    rw [← Φ.sum_comp]
    exact Finset.sum_congr rfl fun j _ => by rw [hadj]
  simp only [x0MqResolvedTable, hadj, Φ.injective.eq_iff, hdiag]

end S_ModularCurve_x0MqResolvedTable_inter_equiv_of_width_eq
end P2MW
export P2MW.S_ModularCurve_x0MqResolvedTable_inter_equiv_of_width_eq (solution)
