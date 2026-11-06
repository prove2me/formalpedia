-- Prove2me | solution 1 for OAI.SevenEighths.HeckeFamily.elementCoeff_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:48.519607+00:00
-- url     : https://prove2.me/submissions/8bb8b239-148a-4fae-8cbb-01b4cdd2ad42

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Operations

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace OAI.SevenEighths.HeckeFamily
theorem _root_.solution (χ : Character) (z : O) :
    elementCoeff χ.inverse z = (elementCoeff χ z)⁻¹ := by
  exact MulChar.inv_apply_eq_inv' _ _
end OAI.SevenEighths.HeckeFamily
