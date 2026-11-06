-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quadraticGammaO_rational_odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:34.698859+00:00
-- url     : https://prove2.me/submissions/32189144-2dfb-4f4d-9477-ef9cb22ab8af

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_ActualEisensteinCubic_quadraticGammaO_rational
import Theorems.Thm_OAI_ActualEisensteinCubic_quadraticGammaRational_eq_fourTerms


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
    (hodd : Odd m) (hc : (m : O) ≠ 0) :
    quadraticGammaO (m : O) hc = breveGaussianFourTerms (m : ℤ) 0 := by
  rw [quadraticGammaO_rational m hm hc,
    quadraticGammaRational_eq_fourTerms m hm hodd]
end OAI.ActualEisensteinCubic
