-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.eisEmbedding_fiber_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:50.669205+00:00
-- url     : https://prove2.me/submissions/8f7131bf-5e74-4ad0-baab-b3d8e8c796b1

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval_norm_sq
import Theorems.Thm_OAI_ActualEisensteinCubic_fiber_coordinates
import Theorems.Thm_OAI_ActualEisensteinCubic_fiber_quadratic_expansion

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
    ‖eisEmbedding
      (ActualEisensteinCoordinates.eval x y +
        ActualEisensteinCoordinates.eval a b *
          ActualEisensteinCoordinates.eval m n)‖ ^ 2 =
      ((a*a-a*b+b*b)*(m*m-m*n+n*n) +
      ((2*a-b)*x+(2*b-a)*y)*m +
      (-(a+b)*x+(2*a-b)*y)*n +
      (x*x-x*y+y*y) : ℤ) := by
  rw [fiber_coordinates, eisEmbedding_eval_norm_sq]
  exact_mod_cast fiber_quadratic_expansion a b x y m n
end OAI.ActualEisensteinCubic
