-- Prove2me | solution 1 for OAI.SevenEighths.HeckeFamily.elementCoeff_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:47.71717+00:00
-- url     : https://prove2.me/submissions/226edc43-1a37-4e9a-82b1-5dd327a40471

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Definitions.Def_OAI_NumberTheory_DirichletL_ResidueCharacter
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Operations
import Theorems.Thm_OAI_SevenEighths_ResidueCharacter_product_mk


set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace OAI.SevenEighths.HeckeFamily
theorem _root_.solution (χ ψ : Character) (z : O) :
    elementCoeff (χ.product ψ) z = elementCoeff χ z * elementCoeff ψ z :=
  ResidueCharacter.product_mk _ _ _ _ z
end OAI.SevenEighths.HeckeFamily
