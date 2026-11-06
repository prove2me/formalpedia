-- Prove2me | solution 1 for OAI.GaussianShiftedPartition.representative_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:45:00.141698+00:00
-- url     : https://prove2.me/submissions/693426ee-0f2f-4ca3-930d-892934824749

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian

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
open OAI.GaussianShiftedPartition
open ActualEisensteinCubic ConcreteTraceCRT ConcreteBreveE
namespace OAI.GaussianShiftedPartition
theorem _root_.solution (c : O) (r : O ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (representative c r) = r :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective r)
end OAI.GaussianShiftedPartition
