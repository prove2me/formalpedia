-- Prove2me | solution 1 for OAI.SevenEighths.HeckeCharacterAnalytic.continuedLattice_differentiableAt_nonprincipal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:42.365204+00:00
-- url     : https://prove2.me/submissions/26dcaf86-727e-401f-8893-07e5ba90d41f

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
import Theorems.Thm_OAI_SevenEighths_HeckeCharacterAnalytic_coefficients_sum_eq_zero
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_continuedLattice_differentiableAt


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeCharacterAnalytic
namespace OAI.SevenEighths.HeckeCharacterAnalytic
theorem _root_.solution (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (HeckeFamily.continuedLattice χ) s :=
  HeckeFamily.continuedLattice_differentiableAt χ hs₀
    (Or.inr (coefficients_sum_eq_zero χ hχ))
end OAI.SevenEighths.HeckeCharacterAnalytic
