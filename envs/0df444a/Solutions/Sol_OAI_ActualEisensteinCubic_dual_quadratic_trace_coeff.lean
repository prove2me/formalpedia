-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.dual_quadratic_trace_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:25:22.984201+00:00
-- url     : https://prove2.me/submissions/e19c2763-7074-4f4b-9002-bab038b6ada9

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_mul
import Theorems.Thm_OAI_ShortDraftLatticeCount_coords_eval


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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b k l : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)).2 =
      (a-b)*k^2+2*a*k*l+b*l^2 := by
  rw [pow_two, ActualEisensteinCoordinates.eval_mul (k+l) k (k+l) k]
  rw [ActualEisensteinCoordinates.eval_mul]
  rw [ShortDraftLatticeCount.coords_eval]
  ring
end OAI.ActualEisensteinCubic
