-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.fiber_quadratic_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:45:40.262763+00:00
-- url     : https://prove2.me/submissions/f44fadca-5976-48cd-8ddb-63debd3374fd

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
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
    let q := a*a-a*b+b*b
    let X := x+a*m-b*n
    let Y := y+b*m+(a-b)*n
    X*X-X*Y+Y*Y =
      q*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) := by
  dsimp
  ring
end OAI.ActualEisensteinCubic
