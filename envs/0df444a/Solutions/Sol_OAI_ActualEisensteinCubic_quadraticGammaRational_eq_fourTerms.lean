-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quadraticGammaRational_eq_fourTerms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:18.760109+00:00
-- url     : https://prove2.me/submissions/45d6eedf-1e7b-4f18-b5d5-1df3f8e44328

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_quadraticGammaRational_eq_one
import Theorems.Thm_OAI_ActualEisensteinCubic_breveGaussianFourTerms_rational_odd

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (m : ℕ) (hm : m ≠ 0)
    (hodd : Odd m) :
    quadraticGammaRational m hm = breveGaussianFourTerms (m : ℤ) 0 := by
  rw [quadraticGammaRational_eq_one m hm hodd,
    breveGaussianFourTerms_rational_odd m hodd]
end OAI.ActualEisensteinCubic
