-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.coordinate_norm_pos_of_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:45:52.327197+00:00
-- url     : https://prove2.me/submissions/726a3654-a423-4d92-8ba0-676f1801f4d2

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    0 < a*a-a*b+b*b := by
  have he : eisEmbedding (ActualEisensteinCoordinates.eval a b) ≠ 0 :=
    ConcreteTraceCRT.eisEmbedding_ne_zero hc
  have hn : 0 < ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ :=
    norm_pos_iff.mpr he
  have heq := eisEmbedding_eval_norm_sq a b
  exact_mod_cast (show (0:ℝ) < (a*a-a*b+b*b : ℤ) by
    rw [← heq]
    positivity)
end OAI.ActualEisensteinCubic
