-- Prove2me | solution 1 for OAI.SevenEighths.HeckeCoordinates.coefficients_eq_quotient_character
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:45:00.917596+00:00
-- url     : https://prove2.me/submissions/b53451c9-a58c-46da-8258-de4bff25bbfa

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Mathlib.Data.ZMod.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Theorems.Thm_OAI_SevenEighths_HeckeCoordinates_coordinateQuotientHom_intCast
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_one
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeFamily.elementCoeff_one
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k


attribute [local simp] OAI.SevenEighths.HeckeCoordinates.coordinateQuotientHom_intCast

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeCoordinates
open HeckeFamily
namespace OAI.SevenEighths.HeckeCoordinates
theorem _root_.solution (χ : Character)
    (a : Fin χ.period × Fin χ.period) :
    coefficients χ a = χ.residue (coordinateQuotientHom χ (a.1, a.2)) := by
  simp [HeckeFamily.coefficients, HeckeFamily.elementCoeff, coordinateQuotientHom,
    coordinateElement]
end OAI.SevenEighths.HeckeCoordinates
