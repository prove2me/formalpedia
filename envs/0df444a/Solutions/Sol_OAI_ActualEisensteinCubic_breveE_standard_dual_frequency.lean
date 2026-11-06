-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveE_standard_dual_frequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:49:33.758066+00:00
-- url     : https://prove2.me/submissions/e8f896db-af26-4291-8b3e-27b06726c2e7

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_bilinear_coordinates

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
theorem _root_.solution (k l m n : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (ActualEisensteinCoordinates.eval (k+l) k) *
        eisEmbedding (ActualEisensteinCoordinates.eval m n) / eisLam) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((k*m+l*n : ℤ) : ℂ)) := by
  rw [breveE_bilinear_coordinates]
  congr 1
  push_cast
  ring
end OAI.ActualEisensteinCubic
