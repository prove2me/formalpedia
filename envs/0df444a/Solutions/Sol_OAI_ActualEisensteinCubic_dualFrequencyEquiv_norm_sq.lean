-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.dualFrequencyEquiv_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:25:35.850286+00:00
-- url     : https://prove2.me/submissions/c33ab9a6-a69c-44ff-87f5-c4e0a954b7e0

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval_norm_sq


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
theorem _root_.solution (k l : ℤ) :
    ‖eisEmbedding (dualFrequencyEquiv (k,l))‖ ^ 2 =
      (((k^2+k*l+l^2 : ℤ) : ℝ)) := by
  change ‖eisEmbedding (ActualEisensteinCoordinates.eval (k+l) k)‖ ^ 2 = _
  rw [eisEmbedding_eval_norm_sq]
  ring_nf
end OAI.ActualEisensteinCubic
