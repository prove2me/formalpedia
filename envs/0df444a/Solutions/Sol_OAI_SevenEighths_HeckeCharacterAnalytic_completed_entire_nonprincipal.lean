-- Prove2me | solution 1 for OAI.SevenEighths.HeckeCharacterAnalytic.completed_entire_nonprincipal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:48:43.876199+00:00
-- url     : https://prove2.me/submissions/ddf7e630-005a-4f0b-ba80-9b473852fe0e

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
import Theorems.Thm_OAI_SevenEighths_HeckeCharacterAnalytic_coefficients_sum_eq_zero
import Theorems.Thm_OAI_SevenEighths_HeckeCharacterAnalytic_coefficients_zero_of_nonprincipal
import Theorems.Thm_P2M_OAI_SevenEighths_HeckeTheta_pair_f__4d2050f76d8c
import Theorems.Thm_P2M_OAI_SevenEighths_HeckeTheta_pair_g__eq_zero_5068f1b5229c


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeCharacterAnalytic
namespace OAI.SevenEighths.HeckeCharacterAnalytic
theorem _root_.solution (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    Differentiable ℂ (HeckeTheta.completed (HeckeFamily.coefficients χ)) := by
  intro s
  exact (HeckeTheta.pair (HeckeFamily.coefficients χ)).differentiableAt_Λ
    (Or.inr (by rw [HeckeTheta.pair_f₀, coefficients_zero_of_nonprincipal χ hχ]))
    (Or.inr (HeckeTheta.pair_g₀_eq_zero _ (coefficients_sum_eq_zero χ hχ)))
end OAI.SevenEighths.HeckeCharacterAnalytic
