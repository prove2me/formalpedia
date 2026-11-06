-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rationalCoordEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:39.316211+00:00
-- url     : https://prove2.me/submissions/37d28822-c047-40d0-9578-5fdd75517850

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace

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
    (a b : ZMod m) :
    rationalCoordEquiv m hm (a,b) =
      Ideal.Quotient.mk (Ideal.span {(m : O)})
        (ActualEisensteinCoordinates.eval (ZMod.cast a) (ZMod.cast b)) := rfl
end OAI.ActualEisensteinCubic
