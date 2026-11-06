-- Prove2me | solution 1 for OAI.SevenEighths.HeckeCharacterAnalytic.sum_residue_pullback_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:46:14.847319+00:00
-- url     : https://prove2.me/submissions/f51bf492-0ecf-411e-b7c4-421706f1e9d1

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
import Theorems.Thm_OAI_SevenEighths_HeckeCharacterAnalytic_sum_comp_additiveHom

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeCharacterAnalytic
namespace OAI.SevenEighths.HeckeCharacterAnalytic
theorem _root_.solution {A R : Type*} [AddCommGroup A] [Fintype A]
    [CommRing R] [Fintype R] (π : A →+ R) (hπ : Function.Surjective π)
    (χ : MulChar R ℂ) (hχ : χ ≠ 1) : (∑ a, χ (π a)) = 0 := by
  rw [sum_comp_additiveHom π hπ, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]
end OAI.SevenEighths.HeckeCharacterAnalytic
