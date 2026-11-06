-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.fiber_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:45:01.436621+00:00
-- url     : https://prove2.me/submissions/77fa34b6-5a45-4cf1-8012-5e10228c32e5

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_mul
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b x y m n : ℤ) :
    ActualEisensteinCoordinates.eval x y +
      ActualEisensteinCoordinates.eval a b *
        ActualEisensteinCoordinates.eval m n =
    ActualEisensteinCoordinates.eval (x + a*m-b*n)
      (y+b*m+(a-b)*n) := by
  rw [ActualEisensteinCoordinates.eval_mul]
  simp only [ActualEisensteinCoordinates.eval]
  push_cast
  ring
end OAI.ActualEisensteinCubic
