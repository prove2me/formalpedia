-- Prove2me | solution 1 for OAI.SevenEighths.HeckeCharacterAnalytic.residue_zero_of_nonprincipal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:45:05.318409+00:00
-- url     : https://prove2.me/submissions/bb646dde-fe89-4d13-9c81-6910c6f5fb50

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeCoordinates_coordinateQuotientHom_intCast
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_one
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeCoordinates.coordinateQuotientHom_intCast
attribute [local simp] OAI.SevenEighths.HeckeFamily.elementCoeff_one
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeCharacterAnalytic
namespace OAI.SevenEighths.HeckeCharacterAnalytic
theorem _root_.solution (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    χ.residue 0 = 0 := by
  rcases subsingleton_or_nontrivial (HeckeFamily.O ⧸ χ.modulus) with h | h
  · let := h
    exfalso
    apply hχ
    apply MulChar.ext'
    intro a
    have ha : a = 1 := Subsingleton.elim _ _
    simp [ha]
  · let := h
    exact χ.residue.map_zero
end OAI.SevenEighths.HeckeCharacterAnalytic
