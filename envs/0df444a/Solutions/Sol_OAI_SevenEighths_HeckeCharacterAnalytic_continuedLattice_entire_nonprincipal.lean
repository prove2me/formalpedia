-- Prove2me | solution 1 for OAI.SevenEighths.HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:43.01419+00:00
-- url     : https://prove2.me/submissions/8f389254-2249-43f1-a0c3-4f9fdfb203df

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
import Theorems.Thm_OAI_SevenEighths_HeckeCharacterAnalytic_completed_entire_nonprincipal

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeCharacterAnalytic
namespace OAI.SevenEighths.HeckeCharacterAnalytic
theorem _root_.solution (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) : Differentiable ℂ (HeckeFamily.continuedLattice χ) := by
  exact ((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
      Complex.differentiable_one_div_Gamma).mul (completed_entire_nonprincipal χ hχ)
end OAI.SevenEighths.HeckeCharacterAnalytic
