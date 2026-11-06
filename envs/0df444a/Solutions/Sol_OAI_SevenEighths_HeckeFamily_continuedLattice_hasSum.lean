-- Prove2me | solution 1 for OAI.SevenEighths.HeckeFamily.continuedLattice_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:12:38.445424+00:00
-- url     : https://prove2.me/submissions/a5fabc03-3483-4cf8-82a6-15da0750718e

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FamilySeries
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_one
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_periodicCoeff_eq_elementCoeff
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_latticeL_hasSum
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_pair_k
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_periodicCoeff_zero
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.HeckeFamily.elementCoeff_one
attribute [local simp] OAI.SevenEighths.HeckeTheta.pair_k
attribute [local simp] OAI.SevenEighths.HeckeTheta.periodicCoeff_zero
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k



set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open EisensteinTheta
namespace OAI.SevenEighths.HeckeFamily
theorem _root_.solution (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => elementCoeff χ (coordinateElement n.1 n.2) /
      (normForm n.1 n.2 : ℂ) ^ s) (continuedLattice χ s) := by
  simpa only [periodicCoeff_eq_elementCoeff, continuedLattice] using HeckeTheta.latticeL_hasSum (coefficients χ) hs
end OAI.SevenEighths.HeckeFamily
