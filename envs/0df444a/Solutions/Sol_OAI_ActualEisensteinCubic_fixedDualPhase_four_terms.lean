-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.fixedDualPhase_four_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:32:33.959812+00:00
-- url     : https://prove2.me/submissions/af51da2b-51ce-4e8e-a49b-41663c5e6db3

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_ActualEisensteinCubic_fixedDualPhase_quotient_two_four_residues
import Theorems.Thm_OAI_ActualEisensteinCubic_fixedDualPhase_coordinates
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span


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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b : ℤ) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑ r : O ⧸ Ideal.span {(2 : O)},
      fixedDualPhase (ActualEisensteinCoordinates.eval a b)
        (GaussianShiftedPartition.representative 2 r)) / 2 =
      breveGaussianFourTerms a b := by
  let : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    finite_quotient_span (by norm_num : (2 : O) ≠ 0)
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  rw [fixedDualPhase_quotient_two_four_residues]
  rw [fixedDualPhase_coordinates a b 0 0,
    fixedDualPhase_coordinates a b 0 1,
    fixedDualPhase_coordinates a b 1 0,
    fixedDualPhase_coordinates a b 1 1]
  unfold breveGaussianFourTerms
  norm_num
  ring_nf
end OAI.ActualEisensteinCubic
