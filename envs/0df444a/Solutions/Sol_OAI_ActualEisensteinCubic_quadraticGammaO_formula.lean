-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quadraticGammaO_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:54:07.535204+00:00
-- url     : https://prove2.me/submissions/d5537d2d-8caf-4137-95f6-a19ea9b237f8

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ThetaLocalRows
import Theorems.Thm_OAI_ActualEisensteinCubic_quadraticGammaO_eq_fourTerms
import Theorems.Thm_OAI_ActualEisensteinCubic_breveGaussianFourTerms_formula


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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    quadraticGammaO (ActualEisensteinCoordinates.eval a b) hc =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  rw [quadraticGammaO_eq_fourTerms a b hc, breveGaussianFourTerms_formula]
end OAI.ActualEisensteinCubic
