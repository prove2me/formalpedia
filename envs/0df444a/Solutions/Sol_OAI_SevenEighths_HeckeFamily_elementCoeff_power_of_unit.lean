-- Prove2me | solution 1 for OAI.SevenEighths.HeckeFamily.elementCoeff_power_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:50.586122+00:00
-- url     : https://prove2.me/submissions/aed0d437-e1b2-46e7-9413-9c026479fd13

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Operations

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace OAI.SevenEighths.HeckeFamily
theorem _root_.solution (χ : Character) (n : ℕ) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk χ.modulus z)) :
    elementCoeff (χ.power n) z = elementCoeff χ z ^ n := by
  change (χ.residue ^ n) (Ideal.Quotient.mk χ.modulus z) = _
  obtain ⟨u, hu⟩ := hz
  rw [← hu, MulChar.pow_apply_coe, hu]
  rfl
end OAI.SevenEighths.HeckeFamily
