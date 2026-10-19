-- Prove2me | solution 1 for OAI.Kervaire.coefficient_injective_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:00:16.356764+00:00
-- url     : https://prove2.me/submissions/f704c2e4-f6b5-4cad-9565-fc03c2aa2927

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions

open OAI OAI.Kervaire
universe u
theorem solution {A : Type u} [Group A] (w : WordGroup A) :
    Function.Injective (coefficientMap w) ↔
      ∀ a : A, Monoid.Coprod.inl a ∈ relatorClosure w → a = 1 := by
  rw [injective_iff_map_eq_one]
  have h : ∀ a : A, coefficientMap w a = 1 ↔ Monoid.Coprod.inl a ∈ relatorClosure w := by
    intro a
    simp only [coefficientMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff _
  simp only [h]

