-- Prove2me | solution 1 for OAI.SevenEighths.HeckeCharacterAnalytic.coefficients_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:47:17.010482+00:00
-- url     : https://prove2.me/submissions/ffe37b7e-68d2-419e-9ad9-473bb3e5771e

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
import Theorems.Thm_OAI_SevenEighths_HeckeCharacterAnalytic_sum_residue_pullback_eq_zero
import Theorems.Thm_OAI_SevenEighths_HeckeCoordinates_coefficients_eq_quotient_character
import Theorems.Thm_OAI_SevenEighths_HeckeCoordinates_coordinateQuotientHom_surjective


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeCharacterAnalytic
namespace OAI.SevenEighths.HeckeCharacterAnalytic
theorem _root_.solution (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    (∑ a, HeckeFamily.coefficients χ a) = 0 := by
  classical
  let : Finite (HeckeFamily.O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  calc
    (∑ a, HeckeFamily.coefficients χ a) =
        ∑ a, χ.residue (HeckeCoordinates.coordinateQuotientHom χ (e a)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact HeckeCoordinates.coefficients_eq_quotient_character χ a
    _ = ∑ a : ZMod χ.period × ZMod χ.period,
        χ.residue (HeckeCoordinates.coordinateQuotientHom χ a) :=
      e.bijective.sum_comp (fun a => χ.residue (HeckeCoordinates.coordinateQuotientHom χ a))
    _ = 0 := sum_residue_pullback_eq_zero
      (HeckeCoordinates.coordinateQuotientHom χ)
      (HeckeCoordinates.coordinateQuotientHom_surjective χ) χ.residue hχ
end OAI.SevenEighths.HeckeCharacterAnalytic
