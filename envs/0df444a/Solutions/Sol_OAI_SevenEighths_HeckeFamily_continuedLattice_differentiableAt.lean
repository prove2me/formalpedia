-- Prove2me | solution 1 for OAI.SevenEighths.HeckeFamily.continuedLattice_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:55.554389+00:00
-- url     : https://prove2.me/submissions/a0f018fc-5845-46a6-a514-e45692680442

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_latticeL_differentiableAt


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace OAI.SevenEighths.HeckeFamily
theorem _root_.solution (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, (coefficients χ) a = 0) :
    DifferentiableAt ℂ (continuedLattice χ) s :=
  HeckeTheta.latticeL_differentiableAt (coefficients χ) hs₀ hs₁
end OAI.SevenEighths.HeckeFamily
